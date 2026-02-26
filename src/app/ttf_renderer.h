// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// TTF text mode renderer using stb_truetype.

#pragma once

#include <cstdint>
#include <string>
#include <vector>
#include <array>

namespace legends {

struct GlyphInfo {
    int width = 0;
    int height = 0;
    int x_offset = 0;
    int y_offset = 0;
    std::vector<uint8_t> bitmap;    // alpha values
    bool valid = false;
};

class TTFRenderer {
public:
    TTFRenderer();
    ~TTFRenderer();

    TTFRenderer(const TTFRenderer&) = delete;
    TTFRenderer& operator=(const TTFRenderer&) = delete;

    /// Load a TTF font from file.
    bool loadFont(const std::string& path, uint32_t point_size);

    /// Check if font is loaded.
    bool isLoaded() const { return loaded_; }

    /// Get current point size.
    uint32_t pointSize() const { return point_size_; }

    /// Get cell dimensions (for text mode grid).
    int cellWidth() const { return cell_width_; }
    int cellHeight() const { return cell_height_; }

    /// Get glyph info for a CP437 character.
    const GlyphInfo& getGlyph(uint8_t cp437_char) const;

    /// Render a text cell (single character) into an RGB buffer.
    /// @param rgb     Target buffer
    /// @param pitch   Row stride in bytes
    /// @param buf_w   Buffer width in pixels
    /// @param buf_h   Buffer height in pixels
    /// @param x, y    Pixel position
    /// @param cp437   CP437 character code
    /// @param fg_r/g/b Foreground color
    /// @param bg_r/g/b Background color
    void renderCell(uint8_t* rgb, uint32_t pitch, uint16_t buf_w, uint16_t buf_h,
                    int x, int y, uint8_t cp437,
                    uint8_t fg_r, uint8_t fg_g, uint8_t fg_b,
                    uint8_t bg_r, uint8_t bg_g, uint8_t bg_b) const;

    /// Enable/disable TTF rendering.
    void setEnabled(bool enabled) { enabled_ = enabled; }
    bool isEnabled() const { return enabled_; }

private:
    void buildGlyphCache();

    bool loaded_ = false;
    bool enabled_ = false;
    uint32_t point_size_ = 16;
    int cell_width_ = 8;
    int cell_height_ = 16;
    std::vector<uint8_t> font_data_;
    std::array<GlyphInfo, 256> glyph_cache_;
    GlyphInfo empty_glyph_;
};

} // namespace legends
