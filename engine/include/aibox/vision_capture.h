/**
 * @file vision_capture.h
 * @brief Screenshot capture engine for vision model integration.
 *
 * Provides configurable screenshot capture with palette application,
 * scaling, and format conversion for computer vision applications.
 */

#pragma once

#include "vision_framebuffer.h"

#include <chrono>
#include <cstdint>
#include <functional>
#include <optional>
#include <vector>

namespace aibox::vision {

// ─────────────────────────────────────────────────────────────────────────────
// Pixel Format
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Output pixel format.
 */
enum class PixelFormat : uint8_t {
    Indexed8 = 0,   ///< Raw indexed (no palette applied) - 1 byte/pixel
    RGB24 = 1,      ///< 24-bit RGB (R, G, B bytes) - 3 bytes/pixel
    RGBA32 = 2,     ///< 32-bit RGBA (R, G, B, A bytes) - 4 bytes/pixel
    BGR24 = 3,      ///< 24-bit BGR (Windows BMP order) - 3 bytes/pixel
    BGRA32 = 4,     ///< 32-bit BGRA - 4 bytes/pixel
    Grayscale8 = 5  ///< 8-bit grayscale (luminance) - 1 byte/pixel
};

/**
 * @brief Convert PixelFormat to string.
 */
[[nodiscard]] constexpr const char* to_string(PixelFormat format) noexcept {
    switch (format) {
        case PixelFormat::Indexed8:   return "Indexed8";
        case PixelFormat::RGB24:      return "RGB24";
        case PixelFormat::RGBA32:     return "RGBA32";
        case PixelFormat::BGR24:      return "BGR24";
        case PixelFormat::BGRA32:     return "BGRA32";
        case PixelFormat::Grayscale8: return "Grayscale8";
        default:                      return "Unknown";
    }
}

/**
 * @brief Get bytes per pixel for a format.
 */
[[nodiscard]] constexpr size_t bytes_per_pixel(PixelFormat format) noexcept {
    switch (format) {
        case PixelFormat::Indexed8:
        case PixelFormat::Grayscale8:
            return 1;
        case PixelFormat::RGB24:
        case PixelFormat::BGR24:
            return 3;
        case PixelFormat::RGBA32:
        case PixelFormat::BGRA32:
            return 4;
        default:
            return 0;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Scaling Mode
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Scaling mode for capture output.
 */
enum class ScaleMode : uint8_t {
    Native = 0,           ///< No scaling (1:1)
    NearestNeighbor = 1,  ///< Fast integer scaling (pixelated)
    Bilinear = 2,         ///< Smooth scaling (interpolated)
    AspectCorrect = 3     ///< Correct DOS aspect ratio (320x200 -> 320x240)
};

/**
 * @brief Convert ScaleMode to string.
 */
[[nodiscard]] constexpr const char* to_string(ScaleMode mode) noexcept {
    switch (mode) {
        case ScaleMode::Native:          return "Native";
        case ScaleMode::NearestNeighbor: return "NearestNeighbor";
        case ScaleMode::Bilinear:        return "Bilinear";
        case ScaleMode::AspectCorrect:   return "AspectCorrect";
        default:                         return "Unknown";
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Capture Configuration
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Screenshot capture configuration.
 */
struct CaptureConfig {
    PixelFormat format{PixelFormat::RGB24};   ///< Output pixel format
    ScaleMode scale_mode{ScaleMode::Native};  ///< Scaling mode
    uint8_t scale_factor{1};      ///< Integer scale factor (1, 2, 4)
    uint16_t target_width{0};     ///< Target width (0 = auto from scale_factor)
    uint16_t target_height{0};    ///< Target height (0 = auto from scale_factor)
    bool include_overlay{true};   ///< Composite overlay onto output
    bool flip_vertical{false};    ///< Flip for OpenGL texture upload

    /**
     * @brief Calculate output dimensions for given input.
     */
    [[nodiscard]] std::pair<uint16_t, uint16_t> calculate_output_size(
        uint16_t input_width,
        uint16_t input_height
    ) const noexcept {
        uint16_t out_w = input_width;
        uint16_t out_h = input_height;

        if (target_width > 0 && target_height > 0) {
            out_w = target_width;
            out_h = target_height;
        } else if (scale_factor > 1) {
            out_w = input_width * scale_factor;
            out_h = input_height * scale_factor;
        }

        // Apply aspect correction for Mode 13h (320x200 -> 320x240)
        if (scale_mode == ScaleMode::AspectCorrect &&
            input_width == 320 && input_height == 200) {
            out_h = out_h * 6 / 5;  // 200 -> 240
        }

        return {out_w, out_h};
    }

    /**
     * @brief Calculate required buffer size.
     */
    [[nodiscard]] size_t calculate_buffer_size(
        uint16_t input_width,
        uint16_t input_height
    ) const noexcept {
        auto [w, h] = calculate_output_size(input_width, input_height);
        return static_cast<size_t>(w) * h * bytes_per_pixel(format);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Screenshot Result
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Screenshot capture result.
 */
struct Screenshot {
    std::vector<uint8_t> pixels;   ///< Pixel data
    uint16_t width{0};             ///< Output width
    uint16_t height{0};            ///< Output height
    PixelFormat format{PixelFormat::RGB24};  ///< Pixel format
    uint64_t capture_time_us{0};   ///< Capture timestamp (microseconds)
    uint64_t frame_number{0};      ///< DOSBox frame counter

    /**
     * @brief Get pixel data size.
     */
    [[nodiscard]] size_t size() const noexcept {
        return pixels.size();
    }

    /**
     * @brief Check if screenshot is valid.
     */
    [[nodiscard]] bool is_valid() const noexcept {
        return !pixels.empty() && width > 0 && height > 0;
    }

    /**
     * @brief Get expected size based on dimensions and format.
     */
    [[nodiscard]] size_t expected_size() const noexcept {
        return static_cast<size_t>(width) * height * bytes_per_pixel(format);
    }

    /**
     * @brief Get stride (bytes per row).
     */
    [[nodiscard]] size_t stride() const noexcept {
        return static_cast<size_t>(width) * bytes_per_pixel(format);
    }

    /**
     * @brief Get pixel at position (for RGB24/RGBA32 formats).
     */
    [[nodiscard]] RgbaColor get_pixel(uint16_t x, uint16_t y) const noexcept {
        if (x >= width || y >= height) return {};

        size_t offset = (y * width + x) * bytes_per_pixel(format);
        const uint8_t* p = pixels.data() + offset;

        switch (format) {
            case PixelFormat::RGB24:
                return {p[0], p[1], p[2], 255};
            case PixelFormat::RGBA32:
                return {p[0], p[1], p[2], p[3]};
            case PixelFormat::BGR24:
                return {p[2], p[1], p[0], 255};
            case PixelFormat::BGRA32:
                return {p[2], p[1], p[0], p[3]};
            case PixelFormat::Grayscale8:
                return {p[0], p[0], p[0], 255};
            case PixelFormat::Indexed8:
                return {p[0], p[0], p[0], 255};  // Index as grayscale
            default:
                return {};
        }
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Capture Engine
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Screenshot capture engine.
 *
 * Captures screenshots from the VGA framebuffer with palette application,
 * scaling, and format conversion.
 *
 * Example:
 * @code
 *   MockFramebuffer fb(modes::MODE_13H);
 *   CaptureEngine engine(fb);
 *
 *   CaptureConfig config;
 *   config.format = PixelFormat::RGB24;
 *   config.scale_factor = 2;
 *   engine.configure(config);
 *
 *   Screenshot shot = engine.capture();
 *   // shot.pixels contains 640x400 RGB24 data
 * @endcode
 */
class CaptureEngine {
public:
    /**
     * @brief Construct a capture engine.
     *
     * @param fb Framebuffer access interface
     */
    explicit CaptureEngine(IFramebufferAccess& fb) : fb_(fb) {}

    /**
     * @brief Configure capture settings.
     */
    void configure(const CaptureConfig& config) noexcept {
        config_ = config;
    }

    /**
     * @brief Get current configuration.
     */
    [[nodiscard]] const CaptureConfig& config() const noexcept {
        return config_;
    }

    /**
     * @brief Capture current frame.
     */
    [[nodiscard]] Screenshot capture();

    /**
     * @brief Capture only if framebuffer changed.
     *
     * @return Screenshot if dirty, nullopt if unchanged
     */
    [[nodiscard]] std::optional<Screenshot> capture_if_dirty();

    /**
     * @brief Calculate output buffer size for current configuration.
     */
    [[nodiscard]] size_t calculate_buffer_size() const noexcept {
        auto mode = fb_.get_mode_info();
        return config_.calculate_buffer_size(mode.width, mode.height);
    }

    /**
     * @brief Get current frame number.
     */
    [[nodiscard]] uint64_t frame_number() const noexcept {
        return frame_number_;
    }

private:
    /**
     * @brief Apply palette lookup to indexed pixels.
     */
    void apply_palette(
        Span<const uint8_t> indexed,
        Span<uint8_t> output
    );

    /**
     * @brief Scale image using configured mode.
     */
    void scale_image(
        Span<const uint8_t> input,
        uint16_t in_w, uint16_t in_h,
        Span<uint8_t> output,
        uint16_t out_w, uint16_t out_h
    );

    /**
     * @brief Render text mode to pixel buffer.
     */
    void render_text_mode(Span<uint8_t> output, uint16_t width, uint16_t height);

    /**
     * @brief Flip buffer vertically.
     */
    void flip_vertical(Span<uint8_t> buffer, uint16_t width, uint16_t height);

    IFramebufferAccess& fb_;
    CaptureConfig config_;
    uint64_t frame_number_{0};
    std::vector<uint8_t> intermediate_buffer_;
};

// ─────────────────────────────────────────────────────────────────────────────
// Streaming Capture
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Streaming capture statistics.
 */
struct StreamingStats {
    uint64_t frames_captured{0};      ///< Total frames captured
    uint64_t frames_dropped{0};       ///< Frames skipped due to timing
    double average_fps{0.0};          ///< Average frames per second
    double average_latency_us{0.0};   ///< Average capture latency
    uint64_t total_bytes{0};          ///< Total bytes captured
};

/**
 * @brief Streaming capture for continuous frame export.
 *
 * Provides rate-limited continuous capture with statistics tracking.
 */
class StreamingCapture {
public:
    using FrameCallback = std::function<void(const Screenshot&)>;

    /**
     * @brief Construct streaming capture.
     *
     * @param engine Capture engine to use
     */
    explicit StreamingCapture(CaptureEngine& engine) : engine_(engine) {}

    /**
     * @brief Start streaming with callback.
     *
     * @param callback Function to call for each captured frame
     * @param target_fps Target frames per second (default: 30)
     */
    void start(FrameCallback callback, uint32_t target_fps = 30);

    /**
     * @brief Stop streaming.
     */
    void stop() noexcept;

    /**
     * @brief Check if streaming is active.
     */
    [[nodiscard]] bool is_running() const noexcept {
        return running_;
    }

    /**
     * @brief Process one frame (call from main loop).
     *
     * Captures a frame if enough time has passed since the last capture
     * and invokes the callback.
     */
    void tick();

    /**
     * @brief Get streaming statistics.
     */
    [[nodiscard]] const StreamingStats& stats() const noexcept {
        return stats_;
    }

    /**
     * @brief Reset statistics.
     */
    void reset_stats() noexcept {
        stats_ = StreamingStats{};
    }

    /**
     * @brief Get target FPS.
     */
    [[nodiscard]] uint32_t target_fps() const noexcept {
        return target_fps_;
    }

    /**
     * @brief Set target FPS.
     */
    void set_target_fps(uint32_t fps) noexcept {
        target_fps_ = fps > 0 ? fps : 1;
    }

private:
    CaptureEngine& engine_;
    FrameCallback callback_;
    bool running_{false};
    uint32_t target_fps_{30};
    uint64_t last_capture_us_{0};
    StreamingStats stats_{};
};

// ─────────────────────────────────────────────────────────────────────────────
// Utility Functions
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Convert RGB to grayscale using ITU-R BT.601.
 *
 * Y = 0.299*R + 0.587*G + 0.114*B
 */
[[nodiscard]] inline uint8_t rgb_to_grayscale(uint8_t r, uint8_t g, uint8_t b) noexcept {
    // Using integer approximation: (77*R + 150*G + 29*B) / 256
    return static_cast<uint8_t>((77 * r + 150 * g + 29 * b) >> 8);
}

/**
 * @brief Convert RGB color to grayscale.
 */
[[nodiscard]] inline uint8_t rgb_to_grayscale(RgbColor color) noexcept {
    return rgb_to_grayscale(color.r, color.g, color.b);
}

/**
 * @brief Get current timestamp in microseconds.
 */
[[nodiscard]] inline uint64_t get_timestamp_us() noexcept {
    auto now = std::chrono::high_resolution_clock::now();
    auto duration = now.time_since_epoch();
    return static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::microseconds>(duration).count()
    );
}

} // namespace aibox::vision
