// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Shared overlay rendering primitives — CP437 bitmap font text, rects, darken.
// Used by MenuSystem, AIPanel, MapperUI, and SaveBrowser overlays.

#pragma once

#include <cstdint>
#include <span>
#include <string>

namespace legends::overlay {

/// Character dimensions for the CP437 8x16 bitmap font.
inline constexpr int kCharW = 8;
inline constexpr int kCharH = 16;

/// @brief Darken a rectangular region by dividing each channel by a divisor.
/// @param rgb    RGB24 pixel buffer
/// @param buf_w  Buffer width in pixels
/// @param buf_h  Buffer height in pixels
/// @param pitch  Row stride in bytes
/// @param x, y   Top-left corner of the rectangle
/// @param w, h   Width and height of the rectangle
/// @param divisor Darken factor (default 3 = divide by 3)
void darkenRect(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
                uint32_t pitch,
                int x, int y, int w, int h, int divisor = 3);

/// @brief Fill a rectangle with a solid RGB color.
/// @param rgb    RGB24 pixel buffer
/// @param buf_w  Buffer width in pixels
/// @param buf_h  Buffer height in pixels
/// @param pitch  Row stride in bytes
/// @param x, y   Top-left corner
/// @param w, h   Width and height
/// @param r, g, b Fill color
void fillRect(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
              uint32_t pitch,
              int x, int y, int w, int h,
              uint8_t r, uint8_t g, uint8_t b);

/// @brief Draw a single CP437 glyph with foreground and background colors.
/// @param rgb    RGB24 pixel buffer
/// @param buf_w  Buffer width in pixels
/// @param buf_h  Buffer height in pixels
/// @param pitch  Row stride in bytes
/// @param x, y   Top-left corner of the glyph
/// @param ch     CP437 character code
/// @param fr, fg, fb  Foreground color
/// @param br, bg, bb  Background color
void drawChar(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
              uint32_t pitch,
              int x, int y, uint8_t ch,
              uint8_t fr, uint8_t fg, uint8_t fb,
              uint8_t br, uint8_t bg, uint8_t bb);

/// @brief Draw a string of CP437 glyphs with foreground and background colors.
/// @param rgb    RGB24 pixel buffer
/// @param buf_w  Buffer width in pixels
/// @param buf_h  Buffer height in pixels
/// @param pitch  Row stride in bytes
/// @param x, y   Top-left corner of the first character
/// @param text   String to render
/// @param fr, fg, fb  Foreground color
/// @param br, bg, bb  Background color
void drawString(std::span<uint8_t> rgb, uint16_t buf_w, uint16_t buf_h,
                uint32_t pitch,
                int x, int y, const std::string& text,
                uint8_t fr, uint8_t fg, uint8_t fb,
                uint8_t br, uint8_t bg, uint8_t bb);

} // namespace legends::overlay
