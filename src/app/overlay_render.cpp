// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Shared overlay rendering primitives — canonical implementations.

#include "app/overlay_render.h"
#include "legends/internal/cp437_font_8x16.h"

namespace legends::overlay {

void darkenRect(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
                uint32_t pitch,
                int x, int y, int w, int h, int divisor) {
    for (int py = y; py < y + h && py < buf_h; ++py) {
        if (py < 0) continue;
        for (int px = x; px < x + w && px < buf_w; ++px) {
            if (px < 0) continue;
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb[idx]     = static_cast<uint8_t>(rgb[idx] / divisor);
            rgb[idx + 1] = static_cast<uint8_t>(rgb[idx + 1] / divisor);
            rgb[idx + 2] = static_cast<uint8_t>(rgb[idx + 2] / divisor);
        }
    }
}

void fillRect(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
              uint32_t pitch,
              int x, int y, int w, int h,
              uint8_t r, uint8_t g, uint8_t b) {
    for (int py = y; py < y + h && py < buf_h; ++py) {
        if (py < 0) continue;
        for (int px = x; px < x + w && px < buf_w; ++px) {
            if (px < 0) continue;
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb[idx]     = r;
            rgb[idx + 1] = g;
            rgb[idx + 2] = b;
        }
    }
}

void drawChar(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
              uint32_t pitch,
              int x, int y, uint8_t ch,
              uint8_t fr, uint8_t fg, uint8_t fb,
              uint8_t br, uint8_t bg, uint8_t bb) {
    const auto& font = internal::CP437_FONT_8x16;
    int glyph_offset = static_cast<int>(ch) * 16;

    for (int row = 0; row < 16; ++row) {
        int py = y + row;
        if (py < 0 || py >= buf_h) continue;

        uint8_t bits = font[static_cast<size_t>(glyph_offset + row)];
        for (int col = 0; col < 8; ++col) {
            int px = x + col;
            if (px < 0 || px >= buf_w) continue;

            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            bool set = (bits & (0x80 >> col)) != 0;
            rgb[idx]     = set ? fr : br;
            rgb[idx + 1] = set ? fg : bg;
            rgb[idx + 2] = set ? fb : bb;
        }
    }
}

void drawString(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
                uint32_t pitch,
                int x, int y, const std::string& text,
                uint8_t fr, uint8_t fg, uint8_t fb,
                uint8_t br, uint8_t bg, uint8_t bb) {
    for (size_t i = 0; i < text.size(); ++i) {
        drawChar(rgb, buf_w, buf_h, pitch,
                 x + static_cast<int>(i) * kCharW, y,
                 static_cast<uint8_t>(text[i]),
                 fr, fg, fb, br, bg, bb);
    }
}

} // namespace legends::overlay
