// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// REQ-UX-005: Performance overlay — FPS, CPU cycles/sec, audio buffer fill.

#pragma once

#include <cstdint>
#include <cstdio>
#include <cstring>

#include "legends/internal/cp437_font_8x16.h"

namespace legends {

class PerfOverlay {
public:
    void setEnabled(bool enabled) { enabled_ = enabled; }
    [[nodiscard]] bool isEnabled() const { return enabled_; }
    void toggle() { enabled_ = !enabled_; }

    /// Call once per frame with the frame delta in microseconds.
    void recordFrame(uint64_t delta_us) {
        if (frame_idx_ < kHistorySize) {
            frame_deltas_[frame_idx_] = delta_us;
        } else {
            frame_deltas_[frame_idx_ % kHistorySize] = delta_us;
        }
        ++frame_idx_;
    }

    void setCyclesPerSec(uint64_t cps) { cycles_per_sec_ = cps; }
    void setAudioQueuedMs(uint32_t ms) { audio_queued_ms_ = ms; }

    /// Render the overlay text into an RGB24 framebuffer.
    /// Draws white text on a translucent dark background at top-left.
    void render(uint8_t* pixels, uint16_t width, uint16_t height, uint32_t pitch) const {
        if (!enabled_ || !pixels || width < 160 || height < 20) return;

        // Compute average FPS from recent frames
        double avg_us = 0;
        uint32_t n = frame_idx_ < kHistorySize ? frame_idx_ : kHistorySize;
        if (n == 0) return;
        for (uint32_t i = 0; i < n; ++i) {
            avg_us += frame_deltas_[i % kHistorySize];
        }
        avg_us /= n;
        double fps = (avg_us > 0) ? 1000000.0 / avg_us : 0;

        // Format the overlay string
        char buf[128];
        std::snprintf(buf, sizeof(buf), "FPS: %.1f  Cycles: %llu/s  Audio: %ums",
                       fps,
                       static_cast<unsigned long long>(cycles_per_sec_),
                       audio_queued_ms_);

        // Draw dark background strip (one row of 16px characters + padding)
        uint32_t bar_h = 20;
        uint32_t bar_w = static_cast<uint32_t>(std::strlen(buf)) * 8 + 8;
        if (bar_w > width) bar_w = width;
        for (uint32_t y = 0; y < bar_h && y < height; ++y) {
            uint8_t* row = pixels + y * pitch;
            for (uint32_t x = 0; x < bar_w; ++x) {
                // Darken: multiply existing pixel by 0.3
                uint8_t* p = row + x * 3;
                p[0] = static_cast<uint8_t>(p[0] * 3 / 10);
                p[1] = static_cast<uint8_t>(p[1] * 3 / 10);
                p[2] = static_cast<uint8_t>(p[2] * 3 / 10);
            }
        }

        // Draw text using CP437 8x16 bitmap font
        drawString(pixels, width, height, pitch, 4, 2, buf);
    }

private:
    bool enabled_ = false;
    static constexpr uint32_t kHistorySize = 60;
    uint64_t frame_deltas_[kHistorySize] = {};
    uint32_t frame_idx_ = 0;
    uint64_t cycles_per_sec_ = 0;
    uint32_t audio_queued_ms_ = 0;

    // Draw a single character using the CP437 8x16 bitmap font.
    static void drawChar(uint8_t* pixels, uint16_t width, uint16_t height,
                          uint32_t pitch, int x0, int y0, char ch) {
        auto idx = static_cast<uint8_t>(ch);
        const auto& font = internal::CP437_FONT_8x16;
        int glyph_offset = static_cast<int>(idx) * 16;

        for (int row = 0; row < 16; ++row) {
            int py = y0 + row;
            if (py < 0 || py >= height) continue;

            uint8_t bits = font[static_cast<size_t>(glyph_offset + row)];
            for (int col = 0; col < 8; ++col) {
                int px = x0 + col;
                if (px < 0 || px >= width) continue;

                if ((bits & (0x80 >> col)) != 0) {
                    uint8_t* p = pixels + py * pitch + px * 3;
                    p[0] = 255; p[1] = 255; p[2] = 255;
                }
            }
        }
    }

    static void drawString(uint8_t* pixels, uint16_t width, uint16_t height,
                             uint32_t pitch, int x, int y, const char* str) {
        for (int i = 0; str[i]; ++i) {
            drawChar(pixels, width, height, pitch, x + i * 8, y, str[i]);
            // Each char is 8 wide with no gap (standard VGA text mode spacing)
        }
    }
};

} // namespace legends
