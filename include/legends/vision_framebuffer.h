/**
 * @file vision_framebuffer.h
 * @brief VGA framebuffer access for vision model integration.
 *
 * Provides low-level access to the VGA framebuffer, palette, and video mode
 * information for screenshot capture and computer vision applications.
 */

#pragma once

#include <array>
#include <cstdint>
#include <span>
#include <vector>

namespace legends::vision {

// Type alias for span (C++23 std::span)
// Kept as alias for potential future customization (e.g., bounds checking)
template<typename T>
using Span = std::span<T>;

// ─────────────────────────────────────────────────────────────────────────────
// Video Mode Information
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief VGA video mode information.
 */
struct VgaModeInfo {
    uint16_t width{0};            ///< Horizontal resolution in pixels
    uint16_t height{0};           ///< Vertical resolution in pixels
    uint8_t bits_per_pixel{8};    ///< Bits per pixel (1, 2, 4, 8, 15, 16, 24, or 32)
    bool is_text_mode{false};     ///< True for text modes (03h, 07h)
    bool is_planar{false};        ///< True for EGA/VGA planar modes
    uint8_t text_columns{80};     ///< Columns if text mode
    uint8_t text_rows{25};        ///< Rows if text mode
    uint8_t char_width{8};        ///< Character cell width in pixels
    uint8_t char_height{16};      ///< Character cell height in pixels
    uint8_t mode_number{0x03};    ///< VGA mode number

    /**
     * @brief Get total pixel count.
     */
    [[nodiscard]] size_t pixel_count() const noexcept {
        return static_cast<size_t>(width) * height;
    }

    /**
     * @brief Get bytes per scanline.
     */
    [[nodiscard]] size_t stride() const noexcept {
        return (static_cast<size_t>(width) * bits_per_pixel + 7) / 8;
    }

    /**
     * @brief Check if mode is a graphics mode.
     */
    [[nodiscard]] bool is_graphics() const noexcept {
        return !is_text_mode;
    }

    /**
     * @brief Equality comparison.
     */
    [[nodiscard]] bool operator==(const VgaModeInfo& other) const noexcept {
        return width == other.width &&
               height == other.height &&
               bits_per_pixel == other.bits_per_pixel &&
               is_text_mode == other.is_text_mode &&
               is_planar == other.is_planar &&
               text_columns == other.text_columns &&
               text_rows == other.text_rows &&
               mode_number == other.mode_number;
    }

    [[nodiscard]] bool operator!=(const VgaModeInfo& other) const noexcept {
        return !(*this == other);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Color Types
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief RGB color triplet (8-bit per channel).
 */
struct RgbColor {
    uint8_t r{0};
    uint8_t g{0};
    uint8_t b{0};

    /**
     * @brief Convert from VGA DAC 6-bit values.
     *
     * VGA DAC uses 6-bit values (0-63), this scales to 8-bit (0-255).
     */
    [[nodiscard]] static RgbColor from_vga_dac(uint8_t r6, uint8_t g6, uint8_t b6) noexcept {
        // Scale 6-bit to 8-bit: val * 255 / 63 ≈ (val << 2) | (val >> 4)
        return {
            static_cast<uint8_t>((r6 << 2) | (r6 >> 4)),
            static_cast<uint8_t>((g6 << 2) | (g6 >> 4)),
            static_cast<uint8_t>((b6 << 2) | (b6 >> 4))
        };
    }

    /**
     * @brief Convert to 32-bit packed RGB (0x00RRGGBB).
     */
    [[nodiscard]] uint32_t to_packed() const noexcept {
        return (static_cast<uint32_t>(r) << 16) |
               (static_cast<uint32_t>(g) << 8) |
               static_cast<uint32_t>(b);
    }

    /**
     * @brief Create from 32-bit packed RGB.
     */
    [[nodiscard]] static RgbColor from_packed(uint32_t packed) noexcept {
        return {
            static_cast<uint8_t>((packed >> 16) & 0xFF),
            static_cast<uint8_t>((packed >> 8) & 0xFF),
            static_cast<uint8_t>(packed & 0xFF)
        };
    }

    [[nodiscard]] bool operator==(const RgbColor& other) const noexcept {
        return r == other.r && g == other.g && b == other.b;
    }

    [[nodiscard]] bool operator!=(const RgbColor& other) const noexcept {
        return !(*this == other);
    }
};

/**
 * @brief RGBA color with alpha channel.
 */
struct RgbaColor {
    uint8_t r{0};
    uint8_t g{0};
    uint8_t b{0};
    uint8_t a{255};

    /**
     * @brief Create from RGB with optional alpha.
     */
    [[nodiscard]] static RgbaColor from_rgb(RgbColor rgb, uint8_t alpha = 255) noexcept {
        return {rgb.r, rgb.g, rgb.b, alpha};
    }

    /**
     * @brief Convert to RGB (discarding alpha).
     */
    [[nodiscard]] RgbColor to_rgb() const noexcept {
        return {r, g, b};
    }

    /**
     * @brief Convert to 32-bit packed RGBA (0xAARRGGBB).
     */
    [[nodiscard]] uint32_t to_packed() const noexcept {
        return (static_cast<uint32_t>(a) << 24) |
               (static_cast<uint32_t>(r) << 16) |
               (static_cast<uint32_t>(g) << 8) |
               static_cast<uint32_t>(b);
    }

    /**
     * @brief Create from 32-bit packed RGBA.
     */
    [[nodiscard]] static RgbaColor from_packed(uint32_t packed) noexcept {
        return {
            static_cast<uint8_t>((packed >> 16) & 0xFF),
            static_cast<uint8_t>((packed >> 8) & 0xFF),
            static_cast<uint8_t>(packed & 0xFF),
            static_cast<uint8_t>((packed >> 24) & 0xFF)
        };
    }

    /**
     * @brief Blend this color over another using alpha.
     */
    [[nodiscard]] RgbaColor blend_over(RgbaColor background) const noexcept {
        if (a == 255) return *this;
        if (a == 0) return background;

        float alpha = a / 255.0f;
        float inv_alpha = 1.0f - alpha;

        return {
            static_cast<uint8_t>(r * alpha + background.r * inv_alpha),
            static_cast<uint8_t>(g * alpha + background.g * inv_alpha),
            static_cast<uint8_t>(b * alpha + background.b * inv_alpha),
            static_cast<uint8_t>(255)
        };
    }

    /**
     * @brief Create a copy with different alpha value.
     */
    [[nodiscard]] RgbaColor with_alpha(uint8_t new_alpha) const noexcept {
        return {r, g, b, new_alpha};
    }

    /**
     * @brief Check if fully opaque.
     */
    [[nodiscard]] bool is_opaque() const noexcept {
        return a == 255;
    }

    /**
     * @brief Check if fully transparent.
     */
    [[nodiscard]] bool is_transparent() const noexcept {
        return a == 0;
    }

    [[nodiscard]] bool operator==(const RgbaColor& other) const noexcept {
        return r == other.r && g == other.g && b == other.b && a == other.a;
    }

    [[nodiscard]] bool operator!=(const RgbaColor& other) const noexcept {
        return !(*this == other);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// VGA Palette
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief VGA palette (256 colors).
 *
 * Provides palette storage and lookup for indexed color modes.
 */
class VgaPalette {
public:
    static constexpr size_t SIZE = 256;

    /**
     * @brief Default constructor (initializes to default VGA palette).
     */
    VgaPalette() {
        // Initialize to standard VGA palette (simplified)
        // First 16 colors are the basic CGA colors
        set_default_palette();
    }

    /**
     * @brief Get color at index.
     */
    [[nodiscard]] RgbColor operator[](size_t index) const noexcept {
        return colors_[index % SIZE];
    }

    /**
     * @brief Set color at index.
     */
    void set(size_t index, RgbColor color) noexcept {
        colors_[index % SIZE] = color;
        dirty_ = true;
    }

    /**
     * @brief Load from VGA DAC registers (6-bit per channel).
     *
     * @param dac_data Raw DAC data (256 * 3 bytes, 6-bit values)
     */
    void load_from_dac(const uint8_t* dac_data) noexcept {
        if (dac_data == nullptr) return;

        for (size_t i = 0; i < SIZE; ++i) {
            colors_[i] = RgbColor::from_vga_dac(
                dac_data[i * 3 + 0],
                dac_data[i * 3 + 1],
                dac_data[i * 3 + 2]
            );
        }
        dirty_ = true;
    }

    /**
     * @brief Load from 8-bit RGB values.
     *
     * @param rgb_data RGB data (256 * 3 bytes, 8-bit values)
     */
    void load_from_rgb(const uint8_t* rgb_data) noexcept {
        if (rgb_data == nullptr) return;

        for (size_t i = 0; i < SIZE; ++i) {
            colors_[i] = {
                rgb_data[i * 3 + 0],
                rgb_data[i * 3 + 1],
                rgb_data[i * 3 + 2]
            };
        }
        dirty_ = true;
    }

    /**
     * @brief Get raw data pointer (for FFI).
     */
    [[nodiscard]] const RgbColor* data() const noexcept {
        return colors_.data();
    }

    /**
     * @brief Get raw data as byte array (R,G,B,R,G,B,...).
     */
    void export_rgb(uint8_t* out) const noexcept {
        if (out == nullptr) return;
        for (size_t i = 0; i < SIZE; ++i) {
            out[i * 3 + 0] = colors_[i].r;
            out[i * 3 + 1] = colors_[i].g;
            out[i * 3 + 2] = colors_[i].b;
        }
    }

    /**
     * @brief Check if palette has changed since last check.
     */
    [[nodiscard]] bool is_dirty() const noexcept {
        return dirty_;
    }

    /**
     * @brief Check dirty and clear flag.
     */
    [[nodiscard]] bool check_dirty_and_clear() noexcept {
        bool was_dirty = dirty_;
        dirty_ = false;
        return was_dirty;
    }

    /**
     * @brief Clear dirty flag.
     */
    void clear_dirty() noexcept {
        dirty_ = false;
    }

private:
    void set_default_palette() noexcept {
        // Standard VGA 16-color palette (CGA compatible)
        static constexpr RgbColor default_16[16] = {
            {0, 0, 0},       // 0: Black
            {0, 0, 170},     // 1: Blue
            {0, 170, 0},     // 2: Green
            {0, 170, 170},   // 3: Cyan
            {170, 0, 0},     // 4: Red
            {170, 0, 170},   // 5: Magenta
            {170, 85, 0},    // 6: Brown
            {170, 170, 170}, // 7: Light Gray
            {85, 85, 85},    // 8: Dark Gray
            {85, 85, 255},   // 9: Light Blue
            {85, 255, 85},   // 10: Light Green
            {85, 255, 255},  // 11: Light Cyan
            {255, 85, 85},   // 12: Light Red
            {255, 85, 255},  // 13: Light Magenta
            {255, 255, 85},  // 14: Yellow
            {255, 255, 255}  // 15: White
        };

        for (size_t i = 0; i < 16; ++i) {
            colors_[i] = default_16[i];
        }

        // Fill rest with grayscale gradient
        for (size_t i = 16; i < SIZE; ++i) {
            uint8_t gray = static_cast<uint8_t>((i - 16) * 255 / (SIZE - 17));
            colors_[i] = {gray, gray, gray};
        }
    }

    std::array<RgbColor, SIZE> colors_{};
    bool dirty_{true};
};

// ─────────────────────────────────────────────────────────────────────────────
// Predefined Video Modes
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Common VGA mode presets.
 */
namespace modes {

/// Mode 03h: 80x25 text mode
/// Order: width, height, bits_per_pixel, is_text_mode, is_planar,
///        text_columns, text_rows, char_width, char_height, mode_number
inline VgaModeInfo make_text_80x25() noexcept {
    VgaModeInfo m;
    m.width = 720;           // 80 * 9 pixels
    m.height = 400;          // 25 * 16 pixels
    m.bits_per_pixel = 4;
    m.is_text_mode = true;
    m.is_planar = false;
    m.text_columns = 80;
    m.text_rows = 25;
    m.char_width = 9;
    m.char_height = 16;
    m.mode_number = 0x03;
    return m;
}
inline const VgaModeInfo TEXT_80x25 = make_text_80x25();

/// Mode 13h: 320x200 256-color
inline VgaModeInfo make_mode_13h() noexcept {
    VgaModeInfo m;
    m.width = 320;
    m.height = 200;
    m.bits_per_pixel = 8;
    m.is_text_mode = false;
    m.is_planar = false;
    m.text_columns = 40;
    m.text_rows = 25;
    m.char_width = 8;
    m.char_height = 8;
    m.mode_number = 0x13;
    return m;
}
inline const VgaModeInfo MODE_13H = make_mode_13h();

/// Mode 12h: 640x480 16-color
inline VgaModeInfo make_mode_12h() noexcept {
    VgaModeInfo m;
    m.width = 640;
    m.height = 480;
    m.bits_per_pixel = 4;
    m.is_text_mode = false;
    m.is_planar = true;
    m.text_columns = 80;
    m.text_rows = 30;
    m.char_width = 8;
    m.char_height = 16;
    m.mode_number = 0x12;
    return m;
}
inline const VgaModeInfo MODE_12H = make_mode_12h();

/// Mode X: 320x240 256-color (planar)
inline VgaModeInfo make_mode_x() noexcept {
    VgaModeInfo m;
    m.width = 320;
    m.height = 240;
    m.bits_per_pixel = 8;
    m.is_text_mode = false;
    m.is_planar = true;
    m.text_columns = 40;
    m.text_rows = 30;
    m.char_width = 8;
    m.char_height = 8;
    m.mode_number = 0x13;  // Technically modified 13h
    return m;
}
inline const VgaModeInfo MODE_X = make_mode_x();

} // namespace modes

// ─────────────────────────────────────────────────────────────────────────────
// Framebuffer Access
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Low-level framebuffer access interface.
 *
 * Provides read-only access to the VGA framebuffer and related state.
 * This is an abstract interface that must be implemented by the emulator.
 */
class IFramebufferAccess {
public:
    virtual ~IFramebufferAccess() = default;

    /**
     * @brief Get current video mode information.
     */
    [[nodiscard]] virtual VgaModeInfo get_mode_info() const = 0;

    /**
     * @brief Get raw indexed pixel buffer (for indexed color modes).
     *
     * For Mode 13h: Linear array of palette indices.
     * For text modes: Returns empty span (use get_text_buffer instead).
     */
    [[nodiscard]] virtual Span<const uint8_t> get_indexed_pixels() const = 0;

    /**
     * @brief Get current palette.
     */
    [[nodiscard]] virtual const VgaPalette& get_palette() const = 0;

    /**
     * @brief Check if framebuffer has changed since last capture.
     */
    [[nodiscard]] virtual bool is_dirty() const = 0;

    /**
     * @brief Mark framebuffer as clean (call after capture).
     */
    virtual void clear_dirty_flag() = 0;

    /**
     * @brief Get text mode character/attribute buffer.
     *
     * Each entry is: low byte = character, high byte = attribute.
     * Attribute format: BLINK(1) | BG(3) | FG(4)
     */
    [[nodiscard]] virtual Span<const uint16_t> get_text_buffer() const = 0;

    /**
     * @brief Get VGA font data for text rendering.
     *
     * Returns the current VGA font (256 characters * char_height bytes).
     */
    [[nodiscard]] virtual Span<const uint8_t> get_font_data() const = 0;
};

/**
 * @brief Mock framebuffer for testing.
 */
class MockFramebuffer : public IFramebufferAccess {
public:
    MockFramebuffer() = default;

    explicit MockFramebuffer(VgaModeInfo mode) : mode_(mode) {
        resize_buffers();
    }

    void set_mode(VgaModeInfo mode) {
        mode_ = mode;
        resize_buffers();
        dirty_ = true;
    }

    void set_pixel(size_t x, size_t y, uint8_t index) {
        if (x < mode_.width && y < mode_.height) {
            pixels_[y * mode_.width + x] = index;
            dirty_ = true;
        }
    }

    void fill(uint8_t index) {
        std::fill(pixels_.begin(), pixels_.end(), index);
        dirty_ = true;
    }

    VgaPalette& palette() { return palette_; }

    [[nodiscard]] VgaModeInfo get_mode_info() const override { return mode_; }
    [[nodiscard]] Span<const uint8_t> get_indexed_pixels() const override {
        return Span<const uint8_t>(pixels_.data(), pixels_.size());
    }
    [[nodiscard]] const VgaPalette& get_palette() const override { return palette_; }
    [[nodiscard]] bool is_dirty() const override { return dirty_; }
    void clear_dirty_flag() override { dirty_ = false; }
    [[nodiscard]] Span<const uint16_t> get_text_buffer() const override {
        return Span<const uint16_t>(text_buffer_.data(), text_buffer_.size());
    }
    [[nodiscard]] Span<const uint8_t> get_font_data() const override {
        return Span<const uint8_t>(font_data_.data(), font_data_.size());
    }

private:
    void resize_buffers() {
        if (mode_.is_text_mode) {
            text_buffer_.resize(mode_.text_columns * mode_.text_rows);
            pixels_.clear();
        } else {
            pixels_.resize(mode_.pixel_count());
            text_buffer_.clear();
        }
    }

    VgaModeInfo mode_ = modes::MODE_13H;
    VgaPalette palette_;
    std::vector<uint8_t> pixels_;
    std::vector<uint16_t> text_buffer_;
    std::vector<uint8_t> font_data_;
    bool dirty_{true};
};

} // namespace legends::vision
