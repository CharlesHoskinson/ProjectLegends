/**
 * @file vision_capture.cpp
 * @brief Implementation of screenshot capture engine for vision model integration.
 */

#include "legends/vision_capture.h"
#include <algorithm>
#include <cstring>

namespace legends::vision {

// ─────────────────────────────────────────────────────────────────────────────
// CaptureEngine Implementation
// ─────────────────────────────────────────────────────────────────────────────

Screenshot CaptureEngine::capture() {
    Screenshot shot;

    // Get framebuffer info
    auto mode = fb_.get_mode_info();
    auto indexed_pixels = fb_.get_indexed_pixels();

    // Calculate output dimensions
    auto [out_w, out_h] = config_.calculate_output_size(mode.width, mode.height);
    shot.width = out_w;
    shot.height = out_h;
    shot.format = config_.format;
    shot.capture_time_us = get_timestamp_us();
    shot.frame_number = frame_number_++;

    // Handle indexed format (no palette application)
    if (config_.format == PixelFormat::Indexed8) {
        shot.pixels.resize(indexed_pixels.size());
        std::copy(indexed_pixels.begin(), indexed_pixels.end(), shot.pixels.begin());

        if (config_.flip_vertical) {
            flip_vertical(Span<uint8_t>(shot.pixels.data(), shot.pixels.size()), shot.width, shot.height);
        }
        return shot;
    }

    // Apply palette to get RGB pixels
    intermediate_buffer_.resize(mode.width * mode.height * 3);
    apply_palette(indexed_pixels, Span<uint8_t>(intermediate_buffer_.data(), intermediate_buffer_.size()));

    // Scale if needed
    if (out_w != mode.width || out_h != mode.height) {
        std::vector<uint8_t> scaled_buffer(out_w * out_h * 3);
        scale_image(
            Span<const uint8_t>(intermediate_buffer_.data(), intermediate_buffer_.size()),
            mode.width, mode.height,
            Span<uint8_t>(scaled_buffer.data(), scaled_buffer.size()),
            out_w, out_h
        );
        intermediate_buffer_ = std::move(scaled_buffer);
    }

    // Convert to final format
    size_t out_bpp = bytes_per_pixel(config_.format);
    shot.pixels.resize(out_w * out_h * out_bpp);

    const uint8_t* src = intermediate_buffer_.data();
    uint8_t* dst = shot.pixels.data();

    for (size_t i = 0; i < static_cast<size_t>(out_w) * out_h; ++i) {
        uint8_t r = src[i * 3 + 0];
        uint8_t g = src[i * 3 + 1];
        uint8_t b = src[i * 3 + 2];

        switch (config_.format) {
            case PixelFormat::RGB24:
                dst[i * 3 + 0] = r;
                dst[i * 3 + 1] = g;
                dst[i * 3 + 2] = b;
                break;
            case PixelFormat::RGBA32:
                dst[i * 4 + 0] = r;
                dst[i * 4 + 1] = g;
                dst[i * 4 + 2] = b;
                dst[i * 4 + 3] = 255;
                break;
            case PixelFormat::BGR24:
                dst[i * 3 + 0] = b;
                dst[i * 3 + 1] = g;
                dst[i * 3 + 2] = r;
                break;
            case PixelFormat::BGRA32:
                dst[i * 4 + 0] = b;
                dst[i * 4 + 1] = g;
                dst[i * 4 + 2] = r;
                dst[i * 4 + 3] = 255;
                break;
            case PixelFormat::Grayscale8:
                dst[i] = rgb_to_grayscale(r, g, b);
                break;
            default:
                break;
        }
    }

    if (config_.flip_vertical) {
        flip_vertical(Span<uint8_t>(shot.pixels.data(), shot.pixels.size()), out_w, out_h);
    }

    return shot;
}

std::optional<Screenshot> CaptureEngine::capture_if_dirty() {
    if (!fb_.is_dirty()) {
        return std::nullopt;
    }

    fb_.clear_dirty_flag();
    return capture();
}

void CaptureEngine::apply_palette(
    Span<const uint8_t> indexed,
    Span<uint8_t> output
) {
    const VgaPalette& palette = fb_.get_palette();

    for (size_t i = 0; i < indexed.size(); ++i) {
        RgbColor color = palette[indexed[i]];
        output[i * 3 + 0] = color.r;
        output[i * 3 + 1] = color.g;
        output[i * 3 + 2] = color.b;
    }
}

void CaptureEngine::scale_image(
    Span<const uint8_t> input,
    uint16_t in_w, uint16_t in_h,
    Span<uint8_t> output,
    uint16_t out_w, uint16_t out_h
) {
    // Use scaling mode to determine algorithm
    switch (config_.scale_mode) {
        case ScaleMode::NearestNeighbor:
        case ScaleMode::Native:
        case ScaleMode::AspectCorrect:
        default:
            // Nearest neighbor scaling
            for (uint16_t y = 0; y < out_h; ++y) {
                for (uint16_t x = 0; x < out_w; ++x) {
                    // Map output coordinates to input
                    uint16_t src_x = x * in_w / out_w;
                    uint16_t src_y = y * in_h / out_h;

                    size_t src_offset = (src_y * in_w + src_x) * 3;
                    size_t dst_offset = (y * out_w + x) * 3;

                    output[dst_offset + 0] = input[src_offset + 0];
                    output[dst_offset + 1] = input[src_offset + 1];
                    output[dst_offset + 2] = input[src_offset + 2];
                }
            }
            break;

        case ScaleMode::Bilinear:
            // Bilinear interpolation
            for (uint16_t y = 0; y < out_h; ++y) {
                for (uint16_t x = 0; x < out_w; ++x) {
                    // Map to source coordinates
                    float src_xf = static_cast<float>(x) * (in_w - 1) / (out_w - 1);
                    float src_yf = static_cast<float>(y) * (in_h - 1) / (out_h - 1);

                    uint16_t x0 = static_cast<uint16_t>(src_xf);
                    uint16_t y0 = static_cast<uint16_t>(src_yf);
                    uint16_t x1 = std::min<uint16_t>(x0 + 1, in_w - 1);
                    uint16_t y1 = std::min<uint16_t>(y0 + 1, in_h - 1);

                    float fx = src_xf - x0;
                    float fy = src_yf - y0;

                    size_t dst_offset = (y * out_w + x) * 3;

                    for (int c = 0; c < 3; ++c) {
                        float v00 = input[(y0 * in_w + x0) * 3 + c];
                        float v10 = input[(y0 * in_w + x1) * 3 + c];
                        float v01 = input[(y1 * in_w + x0) * 3 + c];
                        float v11 = input[(y1 * in_w + x1) * 3 + c];

                        float v = v00 * (1 - fx) * (1 - fy) +
                                  v10 * fx * (1 - fy) +
                                  v01 * (1 - fx) * fy +
                                  v11 * fx * fy;

                        output[dst_offset + c] = static_cast<uint8_t>(v);
                    }
                }
            }
            break;
    }
}

void CaptureEngine::flip_vertical(Span<uint8_t> buffer, uint16_t width, uint16_t height) {
    size_t bpp = bytes_per_pixel(config_.format);
    size_t stride = width * bpp;
    std::vector<uint8_t> temp_row(stride);

    for (uint16_t y = 0; y < height / 2; ++y) {
        uint8_t* row1 = buffer.data() + y * stride;
        uint8_t* row2 = buffer.data() + (height - 1 - y) * stride;

        std::memcpy(temp_row.data(), row1, stride);
        std::memcpy(row1, row2, stride);
        std::memcpy(row2, temp_row.data(), stride);
    }
}

void CaptureEngine::render_text_mode(Span<uint8_t> output, uint16_t width, uint16_t height) {
    (void)width;   // Reserved for future font rendering
    (void)height;  // Reserved for future font rendering
    // Text mode rendering is complex - for now, fill with a pattern
    // Full implementation would need font data
    std::fill(output.begin(), output.end(), 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// StreamingCapture Implementation
// ─────────────────────────────────────────────────────────────────────────────

void StreamingCapture::start(FrameCallback callback, uint32_t target_fps) {
    callback_ = std::move(callback);
    target_fps_ = target_fps > 0 ? target_fps : 1;
    running_ = true;
    last_capture_us_ = get_timestamp_us();
}

void StreamingCapture::stop() noexcept {
    running_ = false;
    callback_ = nullptr;
}

void StreamingCapture::tick() {
    if (!running_ || !callback_) {
        return;
    }

    uint64_t now_us = get_timestamp_us();
    uint64_t interval_us = 1000000 / target_fps_;

    if (now_us - last_capture_us_ >= interval_us) {
        auto start_time = get_timestamp_us();

        Screenshot shot = engine_.capture();

        auto end_time = get_timestamp_us();
        uint64_t latency = end_time - start_time;

        // Update statistics
        ++stats_.frames_captured;
        stats_.total_bytes += shot.size();

        // Update rolling average latency
        double alpha = 0.1;  // Smoothing factor
        stats_.average_latency_us = stats_.average_latency_us * (1 - alpha) + latency * alpha;

        // Update FPS calculation
        if (stats_.frames_captured > 1) {
            double elapsed_s = (now_us - last_capture_us_) / 1000000.0;
            if (elapsed_s > 0) {
                double instant_fps = 1.0 / elapsed_s;
                stats_.average_fps = stats_.average_fps * (1 - alpha) + instant_fps * alpha;
            }
        }

        callback_(shot);
        last_capture_us_ = now_us;
    }
}

}  // namespace legends::vision
