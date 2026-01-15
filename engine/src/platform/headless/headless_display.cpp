/**
 * @file headless_display.cpp
 * @brief HeadlessDisplay implementation for frame capture.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/platform/headless.h"
#include <algorithm>
#include <cstring>
#include <cmath>

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// HeadlessDisplay Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void HeadlessDisplay::set_mode(uint16_t width, uint16_t height,
                                PixelFormat format, bool /*fullscreen*/) {
    std::lock_guard<std::mutex> lock(mutex_);

    info_.width = width;
    info_.height = height;
    info_.format = format;
    info_.pitch = static_cast<uint16_t>(width * bytes_per_pixel(format));
    info_.is_text_mode = (width <= 80);  // Heuristic for text mode

    // Pre-allocate frame buffer
    if (capture_enabled_) {
        frame_buffer_.resize(info_.frame_size());
    }

    // Initialize palette to grayscale for indexed mode
    if (format == PixelFormat::Indexed8 && palette_.empty()) {
        palette_.resize(256 * 4);
        for (int i = 0; i < 256; ++i) {
            palette_[i * 4 + 0] = static_cast<uint8_t>(i);  // R
            palette_[i * 4 + 1] = static_cast<uint8_t>(i);  // G
            palette_[i * 4 + 2] = static_cast<uint8_t>(i);  // B
            palette_[i * 4 + 3] = 255;                       // A
        }
    }
}

void HeadlessDisplay::set_aspect_ratio(float ratio) {
    aspect_ratio_ = ratio;
}

FrameInfo HeadlessDisplay::get_frame_info() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return info_;
}

void HeadlessDisplay::upload_frame(std::span<const uint8_t> pixels,
                                    const FrameInfo& info) {
    frame_count_.fetch_add(1, std::memory_order_relaxed);

    if (!capture_enabled_) {
        return;
    }

    std::lock_guard<std::mutex> lock(mutex_);

    info_ = info;

    // Resize buffer if needed
    size_t required_size = info.frame_size();
    if (frame_buffer_.size() < required_size) {
        frame_buffer_.resize(required_size);
    }

    // Copy frame data
    size_t copy_size = std::min(pixels.size(), required_size);
    std::memcpy(frame_buffer_.data(), pixels.data(), copy_size);

    has_frame_.store(true, std::memory_order_release);
}

void HeadlessDisplay::present() {
    present_count_.fetch_add(1, std::memory_order_relaxed);
    // No-op for headless - frame is already captured
}

void HeadlessDisplay::set_palette(std::span<const uint8_t> palette) {
    std::lock_guard<std::mutex> lock(mutex_);

    // Palette should be 256 RGBA entries = 1024 bytes
    size_t copy_size = std::min(palette.size(), size_t(1024));
    palette_.resize(1024);
    std::memcpy(palette_.data(), palette.data(), copy_size);
}

std::vector<uint8_t> HeadlessDisplay::capture_frame() const {
    std::lock_guard<std::mutex> lock(mutex_);

    if (!has_frame_.load(std::memory_order_acquire)) {
        return {};
    }

    return frame_buffer_;
}

bool HeadlessDisplay::has_frame() const {
    return has_frame_.load(std::memory_order_acquire);
}

std::vector<uint8_t> HeadlessDisplay::get_palette() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return palette_;
}

std::vector<uint8_t> HeadlessDisplay::capture_frame_rgba() const {
    std::lock_guard<std::mutex> lock(mutex_);

    if (!has_frame_.load(std::memory_order_acquire)) {
        return {};
    }

    size_t pixel_count = static_cast<size_t>(info_.width) * info_.height;
    std::vector<uint8_t> rgba(pixel_count * 4);

    switch (info_.format) {
        case PixelFormat::Indexed8: {
            // Expand indexed to RGBA using palette
            const uint8_t* src = frame_buffer_.data();
            uint8_t* dst = rgba.data();

            for (uint16_t y = 0; y < info_.height; ++y) {
                const uint8_t* row = src + y * info_.pitch;
                for (uint16_t x = 0; x < info_.width; ++x) {
                    uint8_t index = row[x];
                    size_t pal_offset = index * 4;

                    if (pal_offset + 3 < palette_.size()) {
                        *dst++ = palette_[pal_offset + 0];  // R
                        *dst++ = palette_[pal_offset + 1];  // G
                        *dst++ = palette_[pal_offset + 2];  // B
                        *dst++ = palette_[pal_offset + 3];  // A
                    } else {
                        // Fallback to grayscale
                        *dst++ = index;
                        *dst++ = index;
                        *dst++ = index;
                        *dst++ = 255;
                    }
                }
            }
            break;
        }

        case PixelFormat::RGB565: {
            const uint8_t* src = frame_buffer_.data();
            uint8_t* dst = rgba.data();

            for (uint16_t y = 0; y < info_.height; ++y) {
                const uint8_t* row = src + y * info_.pitch;
                for (uint16_t x = 0; x < info_.width; ++x) {
                    uint16_t pixel = static_cast<uint16_t>(row[x * 2]) |
                                     (static_cast<uint16_t>(row[x * 2 + 1]) << 8);

                    uint8_t r = static_cast<uint8_t>((pixel >> 11) << 3);
                    uint8_t g = static_cast<uint8_t>(((pixel >> 5) & 0x3F) << 2);
                    uint8_t b = static_cast<uint8_t>((pixel & 0x1F) << 3);

                    *dst++ = r;
                    *dst++ = g;
                    *dst++ = b;
                    *dst++ = 255;
                }
            }
            break;
        }

        case PixelFormat::RGB888: {
            const uint8_t* src = frame_buffer_.data();
            uint8_t* dst = rgba.data();

            for (uint16_t y = 0; y < info_.height; ++y) {
                const uint8_t* row = src + y * info_.pitch;
                for (uint16_t x = 0; x < info_.width; ++x) {
                    *dst++ = row[x * 3 + 0];  // R
                    *dst++ = row[x * 3 + 1];  // G
                    *dst++ = row[x * 3 + 2];  // B
                    *dst++ = 255;             // A
                }
            }
            break;
        }

        case PixelFormat::BGRA8888: {
            const uint8_t* src = frame_buffer_.data();
            uint8_t* dst = rgba.data();

            for (uint16_t y = 0; y < info_.height; ++y) {
                const uint8_t* row = src + y * info_.pitch;
                for (uint16_t x = 0; x < info_.width; ++x) {
                    *dst++ = row[x * 4 + 2];  // R (from B)
                    *dst++ = row[x * 4 + 1];  // G
                    *dst++ = row[x * 4 + 0];  // B (from R)
                    *dst++ = row[x * 4 + 3];  // A
                }
            }
            break;
        }

        case PixelFormat::RGBA8888: {
            // Already RGBA, just copy accounting for pitch
            const uint8_t* src = frame_buffer_.data();
            uint8_t* dst = rgba.data();

            for (uint16_t y = 0; y < info_.height; ++y) {
                const uint8_t* row = src + y * info_.pitch;
                std::memcpy(dst, row, info_.width * 4);
                dst += info_.width * 4;
            }
            break;
        }
    }

    return rgba;
}

void HeadlessDisplay::clear_frame() {
    std::lock_guard<std::mutex> lock(mutex_);
    frame_buffer_.clear();
    has_frame_.store(false, std::memory_order_release);
}

} // namespace platform
} // namespace dosbox
