// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for TTFRenderer.

#include <gtest/gtest.h>
#include "app/ttf_renderer.h"

#include <cstdint>
#include <vector>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Default state
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, DefaultNotLoaded) {
    TTFRenderer renderer;
    EXPECT_FALSE(renderer.isLoaded());
}

TEST(TTFRendererTest, DefaultNotEnabled) {
    TTFRenderer renderer;
    EXPECT_FALSE(renderer.isEnabled());
}

TEST(TTFRendererTest, DefaultPointSize) {
    TTFRenderer renderer;
    EXPECT_EQ(renderer.pointSize(), 16u);
}

TEST(TTFRendererTest, DefaultCellWidth) {
    TTFRenderer renderer;
    EXPECT_EQ(renderer.cellWidth(), 8);
}

TEST(TTFRendererTest, DefaultCellHeight) {
    TTFRenderer renderer;
    EXPECT_EQ(renderer.cellHeight(), 16);
}

// ═══════════════════════════════════════════════════════════════════════════
// setEnabled / isEnabled
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, SetEnabled_True) {
    TTFRenderer renderer;
    renderer.setEnabled(true);
    EXPECT_TRUE(renderer.isEnabled());
}

TEST(TTFRendererTest, SetEnabled_False) {
    TTFRenderer renderer;
    renderer.setEnabled(true);
    renderer.setEnabled(false);
    EXPECT_FALSE(renderer.isEnabled());
}

// ═══════════════════════════════════════════════════════════════════════════
// loadFont
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, LoadFont_EmptyPath_ReturnsFalse) {
    TTFRenderer renderer;
    EXPECT_FALSE(renderer.loadFont("", 16));
    EXPECT_FALSE(renderer.isLoaded());
}

TEST(TTFRendererTest, LoadFont_NonexistentFile_ReturnsFalse) {
    TTFRenderer renderer;
    EXPECT_FALSE(renderer.loadFont("/nonexistent/font.ttf", 16));
    EXPECT_FALSE(renderer.isLoaded());
}

TEST(TTFRendererTest, IsLoaded_InitiallyFalse) {
    TTFRenderer renderer;
    EXPECT_FALSE(renderer.isLoaded());
}

// ═══════════════════════════════════════════════════════════════════════════
// getGlyph
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, GetGlyph_UnloadedFont_ReturnsEmptyGlyph) {
    TTFRenderer renderer;
    const GlyphInfo& gi = renderer.getGlyph(65);  // 'A'
    EXPECT_FALSE(gi.valid);
}

TEST(TTFRendererTest, EmptyGlyph_ValidIsFalse) {
    TTFRenderer renderer;
    const GlyphInfo& gi = renderer.getGlyph(0);
    EXPECT_FALSE(gi.valid);
}

TEST(TTFRendererTest, GetGlyph_Index0) {
    TTFRenderer renderer;
    // Should not crash; returns empty glyph when not loaded.
    const GlyphInfo& gi = renderer.getGlyph(0);
    EXPECT_FALSE(gi.valid);
}

TEST(TTFRendererTest, GetGlyph_Index255) {
    TTFRenderer renderer;
    // Should not crash; returns empty glyph when not loaded.
    const GlyphInfo& gi = renderer.getGlyph(255);
    EXPECT_FALSE(gi.valid);
}

TEST(TTFRendererTest, GetGlyph_MultipleCallsConsistent) {
    TTFRenderer renderer;
    const GlyphInfo& a = renderer.getGlyph(65);
    const GlyphInfo& b = renderer.getGlyph(65);
    EXPECT_EQ(a.valid, b.valid);
    EXPECT_EQ(a.width, b.width);
    EXPECT_EQ(a.height, b.height);
}

TEST(TTFRendererTest, AllGlyphsAccessible) {
    TTFRenderer renderer;
    for (int i = 0; i < 256; ++i) {
        const GlyphInfo& gi = renderer.getGlyph(static_cast<uint8_t>(i));
        // All should return without crashing. When not loaded, all are invalid.
        EXPECT_FALSE(gi.valid) << "Glyph " << i << " should be invalid when font not loaded";
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// GlyphInfo defaults
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, GlyphInfoDefaultValues) {
    GlyphInfo gi;
    EXPECT_EQ(gi.width, 0);
    EXPECT_EQ(gi.height, 0);
    EXPECT_EQ(gi.x_offset, 0);
    EXPECT_EQ(gi.y_offset, 0);
    EXPECT_FALSE(gi.valid);
}

TEST(TTFRendererTest, GlyphInfoBitmapEmptyByDefault) {
    GlyphInfo gi;
    EXPECT_TRUE(gi.bitmap.empty());
}

TEST(TTFRendererTest, GlyphInfoDimensionsNonNegative) {
    GlyphInfo gi;
    EXPECT_GE(gi.width, 0);
    EXPECT_GE(gi.height, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Cell dimensions
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, CellDimensionsPositive) {
    TTFRenderer renderer;
    EXPECT_GT(renderer.cellWidth(), 0);
    EXPECT_GT(renderer.cellHeight(), 0);
}

TEST(TTFRendererTest, CellWidthAndHeightReasonableDefaults) {
    TTFRenderer renderer;
    // Typical text-mode cell: 8x16 or similar.
    EXPECT_GE(renderer.cellWidth(), 1);
    EXPECT_LE(renderer.cellWidth(), 64);
    EXPECT_GE(renderer.cellHeight(), 1);
    EXPECT_LE(renderer.cellHeight(), 64);
}

// ═══════════════════════════════════════════════════════════════════════════
// renderCell edge cases
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, RenderCell_NullBuffer_DoesNotCrash) {
    TTFRenderer renderer;
    // Should not crash with nullptr and zero dimensions.
    renderer.renderCell(nullptr, 0, 0, 0, 0, 0, 'A', 255, 255, 255, 0, 0, 0);
}

TEST(TTFRendererTest, RenderCell_BoundsChecking) {
    TTFRenderer renderer;
    // Small 8x16 buffer, render at origin.
    constexpr uint16_t w = 8;
    constexpr uint16_t h = 16;
    constexpr uint32_t pitch = w * 3;
    std::vector<uint8_t> buf(pitch * h, 0);

    // Should not crash. Font not loaded, so just fills background.
    renderer.renderCell(buf.data(), pitch, w, h, 0, 0, 'A',
                        255, 255, 255, 0, 0, 128);

    // Verify background was filled (blue channel should be 128).
    EXPECT_EQ(buf[2], 128);  // First pixel's blue channel
}

// ═══════════════════════════════════════════════════════════════════════════
// Copy semantics (deleted)
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, CopyConstructorDeleted) {
    // Static assertion: TTFRenderer is not copyable.
    EXPECT_FALSE(std::is_copy_constructible_v<TTFRenderer>);
}

TEST(TTFRendererTest, CopyAssignmentDeleted) {
    EXPECT_FALSE(std::is_copy_assignable_v<TTFRenderer>);
}

// ═══════════════════════════════════════════════════════════════════════════
// Point size edge case
// ═══════════════════════════════════════════════════════════════════════════

TEST(TTFRendererTest, PointSizeStoredCorrectly) {
    TTFRenderer renderer;
    // Default is 16, and loadFont would set it. Without loading, it stays 16.
    EXPECT_EQ(renderer.pointSize(), 16u);
}

} // namespace
} // namespace legends
