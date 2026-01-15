/**
 * @file display.h
 * @brief Platform-agnostic display interface for DOSBox library mode.
 *
 * This interface abstracts display/rendering operations, allowing DOSBox
 * to run headless or with different rendering backends (SDL2, SDL3, custom).
 *
 * ## Design Principles
 * 1. **Determinism**: Core produces pixels, backend presents
 * 2. **Two Modes**: Software blit (headless) and hardware present (GPU)
 * 3. **No SDL Dependencies**: Pure C++ interface
 *
 * ## Usage
 * ```cpp
 * // Headless mode (testing, AI agents)
 * auto display = std::make_unique<HeadlessDisplay>();
 * display->set_mode(640, 480, PixelFormat::Indexed8, false);
 * // ... emulation produces frames via upload_frame()
 * auto frame = display->capture_frame();  // Get last frame for analysis
 *
 * // SDL mode (normal GUI)
 * auto display = std::make_unique<SDLDisplay>(window);
 * display->set_mode(640, 480, PixelFormat::BGRA8888, false);
 * // ... emulation produces frames
 * display->present();  // Show on screen
 * ```
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_PLATFORM_DISPLAY_H
#define DOSBOX_PLATFORM_DISPLAY_H

#include <cstdint>
#include <cstddef>
#include <memory>
#include <span>
#include <vector>

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// Pixel Format
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Pixel format enumeration.
 *
 * Covers common formats used by VGA/SVGA modes and modern backends.
 */
enum class PixelFormat : uint8_t {
    Indexed8 = 0,    ///< 8-bit indexed color (256 colors, requires palette)
    RGB565 = 1,      ///< 16-bit RGB (5-6-5 bits)
    RGB888 = 2,      ///< 24-bit RGB (8-8-8 bits, packed)
    BGRA8888 = 3,    ///< 32-bit BGRA (8-8-8-8 bits, common for SDL)
    RGBA8888 = 4,    ///< 32-bit RGBA (8-8-8-8 bits)
};

/**
 * @brief Get bytes per pixel for a format.
 */
inline constexpr size_t bytes_per_pixel(PixelFormat format) {
    switch (format) {
        case PixelFormat::Indexed8: return 1;
        case PixelFormat::RGB565:   return 2;
        case PixelFormat::RGB888:   return 3;
        case PixelFormat::BGRA8888: return 4;
        case PixelFormat::RGBA8888: return 4;
        default: return 0;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Frame Information
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Information about a display frame.
 *
 * Describes the dimensions, format, and layout of pixel data.
 */
struct FrameInfo {
    uint16_t width = 0;          ///< Frame width in pixels
    uint16_t height = 0;         ///< Frame height in pixels
    PixelFormat format = PixelFormat::Indexed8;  ///< Pixel format
    uint16_t pitch = 0;          ///< Bytes per row (may include padding)
    bool is_text_mode = true;    ///< True if text mode, false if graphics

    /**
     * @brief Calculate minimum pitch for the given width and format.
     */
    uint16_t min_pitch() const {
        return static_cast<uint16_t>(width * bytes_per_pixel(format));
    }

    /**
     * @brief Calculate total frame size in bytes.
     */
    size_t frame_size() const {
        return static_cast<size_t>(pitch) * height;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Display Interface
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Abstract display interface for DOSBox rendering.
 *
 * Implementations:
 * - HeadlessDisplay: Stores frames in memory (testing, AI)
 * - SDL2Display: Uses SDL2 for window/rendering
 * - SDL3Display: Uses SDL3 GPU API
 *
 * ## Thread Safety
 * All methods must be called from the main/render thread.
 *
 * ## Determinism
 * The core emulation calls upload_frame() with produced pixels.
 * The backend decides when/how to present (decoupled from emulation timing).
 */
class IDisplay {
public:
    virtual ~IDisplay() = default;

    // ─────────────────────────────────────────────────────────────────────────
    // Mode Configuration
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set the display mode.
     *
     * Called when VGA mode changes. Backend should resize/reconfigure.
     *
     * @param width Frame width in pixels
     * @param height Frame height in pixels
     * @param format Pixel format
     * @param fullscreen Request fullscreen mode
     */
    virtual void set_mode(uint16_t width, uint16_t height,
                          PixelFormat format, bool fullscreen) = 0;

    /**
     * @brief Set the display aspect ratio.
     *
     * Used for proper scaling (e.g., 4:3 for classic DOS games).
     *
     * @param ratio Aspect ratio (width/height), e.g., 4.0/3.0
     */
    virtual void set_aspect_ratio(float ratio) = 0;

    /**
     * @brief Get current frame info.
     */
    virtual FrameInfo get_frame_info() const = 0;

    // ─────────────────────────────────────────────────────────────────────────
    // Software Rendering Mode
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Upload a frame from the emulator.
     *
     * Called by the emulation core when a frame is ready.
     * The backend may copy or process the data as needed.
     *
     * @param pixels Raw pixel data
     * @param info Frame information (dimensions, format, pitch)
     */
    virtual void upload_frame(std::span<const uint8_t> pixels,
                              const FrameInfo& info) = 0;

    /**
     * @brief Present the current frame to the display.
     *
     * For headless mode, this may be a no-op.
     * For windowed mode, this swaps buffers / presents to screen.
     */
    virtual void present() = 0;

    // ─────────────────────────────────────────────────────────────────────────
    // Hardware Rendering Mode (Optional)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Check if hardware rendering is available.
     *
     * If true, the core can use lock_texture/unlock_texture for
     * direct texture upload (more efficient for GPU rendering).
     */
    virtual bool supports_hardware_present() const { return false; }

    /**
     * @brief Lock the texture for direct pixel upload.
     *
     * Returns a pointer to the texture memory for direct writing.
     * Must call unlock_texture() when done.
     *
     * @param info_out Receives frame info (pitch may differ from expected)
     * @return Pointer to texture memory, or nullptr if not supported
     */
    virtual void* lock_texture(FrameInfo* info_out) {
        (void)info_out;
        return nullptr;
    }

    /**
     * @brief Unlock the texture after direct upload.
     */
    virtual void unlock_texture() {}

    // ─────────────────────────────────────────────────────────────────────────
    // Palette (for Indexed8 mode)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set the color palette for indexed modes.
     *
     * @param palette 256 RGBA colors (1024 bytes)
     */
    virtual void set_palette(std::span<const uint8_t> palette) {
        (void)palette;
        // Default: no-op (not all backends need palette)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Frame Capture (for headless/testing)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Capture the current frame.
     *
     * Returns the last uploaded frame data. Useful for headless mode
     * where frames need to be analyzed programmatically.
     *
     * @return Frame data, or empty vector if not available
     */
    virtual std::vector<uint8_t> capture_frame() const {
        return {};
    }

    /**
     * @brief Check if a frame is available for capture.
     */
    virtual bool has_frame() const { return false; }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Null Display (No-op implementation)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Null display that discards all frames.
 *
 * Useful for benchmarking or when display output is not needed.
 */
class NullDisplay : public IDisplay {
public:
    void set_mode(uint16_t width, uint16_t height,
                  PixelFormat format, bool /*fullscreen*/) override {
        info_.width = width;
        info_.height = height;
        info_.format = format;
        info_.pitch = info_.min_pitch();
    }

    void set_aspect_ratio(float ratio) override {
        aspect_ratio_ = ratio;
    }

    FrameInfo get_frame_info() const override {
        return info_;
    }

    void upload_frame(std::span<const uint8_t> /*pixels*/,
                      const FrameInfo& info) override {
        info_ = info;
        frame_count_++;
    }

    void present() override {
        // No-op
    }

    uint64_t frame_count() const { return frame_count_; }

private:
    FrameInfo info_;
    float aspect_ratio_ = 4.0f / 3.0f;
    uint64_t frame_count_ = 0;
};

} // namespace platform
} // namespace dosbox

#endif // DOSBOX_PLATFORM_DISPLAY_H
