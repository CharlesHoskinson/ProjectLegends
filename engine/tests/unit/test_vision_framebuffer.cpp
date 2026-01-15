/**
 * @file test_vision_framebuffer.cpp
 * @brief Unit tests for vision_framebuffer.h
 */

#include <gtest/gtest.h>
#include "aibox/vision_framebuffer.h"

using namespace aibox::vision;

// ─────────────────────────────────────────────────────────────────────────────
// RgbColor Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(RgbColorTest, DefaultConstruction) {
    RgbColor color;
    EXPECT_EQ(color.r, 0);
    EXPECT_EQ(color.g, 0);
    EXPECT_EQ(color.b, 0);
}

TEST(RgbColorTest, ValueConstruction) {
    RgbColor color{255, 128, 64};
    EXPECT_EQ(color.r, 255);
    EXPECT_EQ(color.g, 128);
    EXPECT_EQ(color.b, 64);
}

TEST(RgbColorTest, FromVgaDacBasic) {
    // VGA DAC uses 6-bit values (0-63), need to convert to 8-bit (0-255)
    RgbColor color = RgbColor::from_vga_dac(63, 0, 31);

    // 63 * 255 / 63 = 255
    // 0 * 255 / 63 = 0
    // 31 * 255 / 63 = 125 (approximately)
    EXPECT_EQ(color.r, 255);
    EXPECT_EQ(color.g, 0);
    EXPECT_GE(color.b, 124);
    EXPECT_LE(color.b, 126);
}

TEST(RgbColorTest, FromVgaDacZero) {
    RgbColor color = RgbColor::from_vga_dac(0, 0, 0);
    EXPECT_EQ(color.r, 0);
    EXPECT_EQ(color.g, 0);
    EXPECT_EQ(color.b, 0);
}

TEST(RgbColorTest, FromVgaDacMax) {
    RgbColor color = RgbColor::from_vga_dac(63, 63, 63);
    EXPECT_EQ(color.r, 255);
    EXPECT_EQ(color.g, 255);
    EXPECT_EQ(color.b, 255);
}

TEST(RgbColorTest, Equality) {
    RgbColor a{100, 150, 200};
    RgbColor b{100, 150, 200};
    RgbColor c{100, 150, 201};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

TEST(RgbColorTest, ToPacked) {
    RgbColor color{0xAA, 0xBB, 0xCC};
    uint32_t packed = color.to_packed();
    EXPECT_EQ(packed, 0x00AABBCC);
}

TEST(RgbColorTest, FromPacked) {
    RgbColor color = RgbColor::from_packed(0x00AABBCC);
    EXPECT_EQ(color.r, 0xAA);
    EXPECT_EQ(color.g, 0xBB);
    EXPECT_EQ(color.b, 0xCC);
}

// ─────────────────────────────────────────────────────────────────────────────
// RgbaColor Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(RgbaColorTest, DefaultConstruction) {
    RgbaColor color;
    EXPECT_EQ(color.r, 0);
    EXPECT_EQ(color.g, 0);
    EXPECT_EQ(color.b, 0);
    EXPECT_EQ(color.a, 255);  // Default alpha is opaque
}

TEST(RgbaColorTest, ValueConstruction) {
    RgbaColor color{255, 128, 64, 200};
    EXPECT_EQ(color.r, 255);
    EXPECT_EQ(color.g, 128);
    EXPECT_EQ(color.b, 64);
    EXPECT_EQ(color.a, 200);
}

TEST(RgbaColorTest, FromRgbColor) {
    RgbColor rgb{100, 150, 200};
    RgbaColor rgba = RgbaColor::from_rgb(rgb);

    EXPECT_EQ(rgba.r, 100);
    EXPECT_EQ(rgba.g, 150);
    EXPECT_EQ(rgba.b, 200);
    EXPECT_EQ(rgba.a, 255);
}

TEST(RgbaColorTest, FromRgbColorWithAlpha) {
    RgbColor rgb{100, 150, 200};
    RgbaColor rgba = RgbaColor::from_rgb(rgb, 128);

    EXPECT_EQ(rgba.r, 100);
    EXPECT_EQ(rgba.g, 150);
    EXPECT_EQ(rgba.b, 200);
    EXPECT_EQ(rgba.a, 128);
}

TEST(RgbaColorTest, ToRgb) {
    RgbaColor rgba{100, 150, 200, 128};
    RgbColor rgb = rgba.to_rgb();

    EXPECT_EQ(rgb.r, 100);
    EXPECT_EQ(rgb.g, 150);
    EXPECT_EQ(rgb.b, 200);
}

TEST(RgbaColorTest, WithAlpha) {
    RgbaColor color{100, 150, 200, 255};
    RgbaColor modified = color.with_alpha(64);

    EXPECT_EQ(modified.r, 100);
    EXPECT_EQ(modified.g, 150);
    EXPECT_EQ(modified.b, 200);
    EXPECT_EQ(modified.a, 64);
}

TEST(RgbaColorTest, IsOpaque) {
    RgbaColor opaque{100, 150, 200, 255};
    RgbaColor transparent{100, 150, 200, 0};
    RgbaColor semi{100, 150, 200, 128};

    EXPECT_TRUE(opaque.is_opaque());
    EXPECT_FALSE(transparent.is_opaque());
    EXPECT_FALSE(semi.is_opaque());
}

TEST(RgbaColorTest, IsTransparent) {
    RgbaColor opaque{100, 150, 200, 255};
    RgbaColor transparent{100, 150, 200, 0};
    RgbaColor semi{100, 150, 200, 128};

    EXPECT_FALSE(opaque.is_transparent());
    EXPECT_TRUE(transparent.is_transparent());
    EXPECT_FALSE(semi.is_transparent());
}

TEST(RgbaColorTest, ToPacked) {
    RgbaColor color{0xAA, 0xBB, 0xCC, 0xDD};
    uint32_t packed = color.to_packed();
    EXPECT_EQ(packed, 0xDDAABBCC);
}

TEST(RgbaColorTest, FromPacked) {
    RgbaColor color = RgbaColor::from_packed(0xDDAABBCC);
    EXPECT_EQ(color.r, 0xAA);
    EXPECT_EQ(color.g, 0xBB);
    EXPECT_EQ(color.b, 0xCC);
    EXPECT_EQ(color.a, 0xDD);
}

TEST(RgbaColorTest, BlendOver) {
    RgbaColor fg{255, 0, 0, 128};  // Semi-transparent red
    RgbaColor bg{0, 0, 255, 255};  // Opaque blue

    RgbaColor result = fg.blend_over(bg);

    // Blended should be purple-ish
    EXPECT_GT(result.r, 100);
    EXPECT_LT(result.r, 150);
    EXPECT_GT(result.b, 100);
    EXPECT_LT(result.b, 150);
}

// ─────────────────────────────────────────────────────────────────────────────
// VgaModeInfo Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VgaModeInfoTest, DefaultConstruction) {
    VgaModeInfo info;
    EXPECT_EQ(info.width, 0);
    EXPECT_EQ(info.height, 0);
    EXPECT_EQ(info.bits_per_pixel, 8);
    EXPECT_FALSE(info.is_text_mode);
    EXPECT_FALSE(info.is_planar);
}

TEST(VgaModeInfoTest, Mode13h) {
    VgaModeInfo info = modes::MODE_13H;
    EXPECT_EQ(info.width, 320);
    EXPECT_EQ(info.height, 200);
    EXPECT_EQ(info.bits_per_pixel, 8);
    EXPECT_FALSE(info.is_text_mode);
    EXPECT_FALSE(info.is_planar);
}

TEST(VgaModeInfoTest, Mode12h) {
    VgaModeInfo info = modes::MODE_12H;
    EXPECT_EQ(info.width, 640);
    EXPECT_EQ(info.height, 480);
    EXPECT_EQ(info.bits_per_pixel, 4);
    EXPECT_FALSE(info.is_text_mode);
    EXPECT_TRUE(info.is_planar);
}

TEST(VgaModeInfoTest, TextMode80x25) {
    VgaModeInfo info = modes::TEXT_80x25;
    EXPECT_EQ(info.text_columns, 80);
    EXPECT_EQ(info.text_rows, 25);
    EXPECT_TRUE(info.is_text_mode);
}

TEST(VgaModeInfoTest, PixelCount) {
    VgaModeInfo info = modes::MODE_13H;
    EXPECT_EQ(info.pixel_count(), 64000);
}

TEST(VgaModeInfoTest, Stride) {
    VgaModeInfo info = modes::MODE_13H;
    EXPECT_EQ(info.stride(), 320);  // 320 * 8 / 8
}

TEST(VgaModeInfoTest, IsGraphics) {
    EXPECT_TRUE(modes::MODE_13H.is_graphics());
    EXPECT_TRUE(modes::MODE_12H.is_graphics());
    EXPECT_FALSE(modes::TEXT_80x25.is_graphics());
}

TEST(VgaModeInfoTest, Equality) {
    VgaModeInfo a = modes::MODE_13H;
    VgaModeInfo b = modes::MODE_13H;
    VgaModeInfo c = modes::MODE_12H;

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// VgaPalette Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VgaPaletteTest, DefaultConstruction) {
    VgaPalette palette;
    // Default palette should have standard VGA colors
    // Index 0 is black
    EXPECT_EQ(palette[0].r, 0);
    EXPECT_EQ(palette[0].g, 0);
    EXPECT_EQ(palette[0].b, 0);
}

TEST(VgaPaletteTest, SubscriptOperator) {
    VgaPalette palette;
    palette.set(10, RgbColor{100, 150, 200});

    RgbColor color = palette[10];
    EXPECT_EQ(color.r, 100);
    EXPECT_EQ(color.g, 150);
    EXPECT_EQ(color.b, 200);
}

TEST(VgaPaletteTest, OutOfBoundsWraps) {
    VgaPalette palette;
    palette.set(0, RgbColor{100, 150, 200});

    // Index 256 wraps to 0
    RgbColor color = palette[256];
    EXPECT_EQ(color.r, 100);
    EXPECT_EQ(color.g, 150);
    EXPECT_EQ(color.b, 200);
}

TEST(VgaPaletteTest, SetAndGet) {
    VgaPalette palette;
    palette.set(50, RgbColor{255, 128, 64});

    RgbColor color = palette[50];
    EXPECT_EQ(color.r, 255);
    EXPECT_EQ(color.g, 128);
    EXPECT_EQ(color.b, 64);
}

TEST(VgaPaletteTest, LoadFromDac) {
    VgaPalette palette;

    // Create mock DAC data (6-bit values)
    uint8_t dac_data[768];  // 256 * 3 bytes
    for (int i = 0; i < 256; ++i) {
        dac_data[i * 3 + 0] = static_cast<uint8_t>(i / 4);  // R (6-bit)
        dac_data[i * 3 + 1] = 0;  // G
        dac_data[i * 3 + 2] = 63 - static_cast<uint8_t>(i / 4);  // B (6-bit)
    }

    palette.load_from_dac(dac_data);

    // Check index 0: R=0/63, G=0, B=63/63
    EXPECT_EQ(palette[0].r, 0);
    EXPECT_EQ(palette[0].g, 0);
    EXPECT_EQ(palette[0].b, 255);

    // Check index 252: R=63/63=255, G=0, B=0/63=0
    EXPECT_EQ(palette[252].r, 255);
    EXPECT_EQ(palette[252].g, 0);
    EXPECT_EQ(palette[252].b, 0);
}

TEST(VgaPaletteTest, DataPointer) {
    VgaPalette palette;
    palette.set(0, RgbColor{255, 0, 0});
    palette.set(1, RgbColor{0, 255, 0});

    const RgbColor* data = palette.data();
    EXPECT_NE(data, nullptr);
    EXPECT_EQ(data[0].r, 255);
    EXPECT_EQ(data[1].g, 255);
}

TEST(VgaPaletteTest, IsDirty) {
    VgaPalette palette;

    // Initially dirty (just created)
    EXPECT_TRUE(palette.is_dirty());

    palette.clear_dirty();
    EXPECT_FALSE(palette.is_dirty());

    palette.set(0, RgbColor{100, 100, 100});
    EXPECT_TRUE(palette.is_dirty());
}

TEST(VgaPaletteTest, CheckDirtyAndClear) {
    VgaPalette palette;

    EXPECT_TRUE(palette.check_dirty_and_clear());
    EXPECT_FALSE(palette.is_dirty());
}

TEST(VgaPaletteTest, ExportRgb) {
    VgaPalette palette;
    palette.set(0, RgbColor{100, 150, 200});
    palette.set(1, RgbColor{50, 75, 100});

    uint8_t rgb_out[768];
    palette.export_rgb(rgb_out);

    EXPECT_EQ(rgb_out[0], 100);
    EXPECT_EQ(rgb_out[1], 150);
    EXPECT_EQ(rgb_out[2], 200);
    EXPECT_EQ(rgb_out[3], 50);
    EXPECT_EQ(rgb_out[4], 75);
    EXPECT_EQ(rgb_out[5], 100);
}

// ─────────────────────────────────────────────────────────────────────────────
// MockFramebuffer Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MockFramebufferTest, ConstructionMode13h) {
    MockFramebuffer fb(modes::MODE_13H);

    VgaModeInfo info = fb.get_mode_info();
    EXPECT_EQ(info.width, 320);
    EXPECT_EQ(info.height, 200);
    EXPECT_EQ(info.bits_per_pixel, 8);
}

TEST(MockFramebufferTest, GetIndexedPixels) {
    MockFramebuffer fb(modes::MODE_13H);

    auto pixels = fb.get_indexed_pixels();
    EXPECT_EQ(pixels.size(), 64000);  // 320 * 200
}

TEST(MockFramebufferTest, GetPalette) {
    MockFramebuffer fb(modes::MODE_13H);

    const VgaPalette& palette = fb.get_palette();
    // Palette should be accessible
    RgbColor color = palette[0];
    (void)color;  // Just verify it compiles
}

TEST(MockFramebufferTest, IsDirtyInitiallyTrue) {
    MockFramebuffer fb(modes::MODE_13H);
    EXPECT_TRUE(fb.is_dirty());
}

TEST(MockFramebufferTest, SetPixel) {
    MockFramebuffer fb(modes::MODE_13H);

    fb.set_pixel(10, 20, 42);

    auto pixels = fb.get_indexed_pixels();
    // pixel at (10, 20) = offset 20*320 + 10 = 6410
    EXPECT_EQ(pixels[6410], 42);
}

TEST(MockFramebufferTest, ClearDirtyFlag) {
    MockFramebuffer fb(modes::MODE_13H);

    EXPECT_TRUE(fb.is_dirty());
    fb.clear_dirty_flag();
    EXPECT_FALSE(fb.is_dirty());
}

TEST(MockFramebufferTest, FillWithColor) {
    MockFramebuffer fb(modes::MODE_13H);

    fb.fill(100);

    auto pixels = fb.get_indexed_pixels();
    for (size_t i = 0; i < pixels.size(); ++i) {
        EXPECT_EQ(pixels[i], 100);
    }
}

TEST(MockFramebufferTest, SetMode) {
    MockFramebuffer fb(modes::MODE_13H);

    fb.set_mode(modes::MODE_12H);

    VgaModeInfo info = fb.get_mode_info();
    EXPECT_EQ(info.width, 640);
    EXPECT_EQ(info.height, 480);
}

TEST(MockFramebufferTest, PaletteAccess) {
    MockFramebuffer fb(modes::MODE_13H);

    fb.palette().set(42, RgbColor{100, 150, 200});

    const VgaPalette& palette = fb.get_palette();
    EXPECT_EQ(palette[42].r, 100);
    EXPECT_EQ(palette[42].g, 150);
    EXPECT_EQ(palette[42].b, 200);
}

// ─────────────────────────────────────────────────────────────────────────────
// IFramebufferAccess Interface Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(IFramebufferAccessTest, PolymorphicAccess) {
    MockFramebuffer fb(modes::MODE_13H);
    IFramebufferAccess& iface = fb;

    VgaModeInfo info = iface.get_mode_info();
    EXPECT_EQ(info.width, 320);
    EXPECT_EQ(info.height, 200);
}

TEST(IFramebufferAccessTest, GetTextBuffer) {
    MockFramebuffer fb(modes::TEXT_80x25);

    auto text_buffer = fb.get_text_buffer();
    // Text buffer should be available for text modes
    // 80 * 25 = 2000 uint16_t entries
    EXPECT_EQ(text_buffer.size(), 2000);
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST(EdgeCaseTest, VerySmallFramebuffer) {
    VgaModeInfo small_mode;
    small_mode.width = 1;
    small_mode.height = 1;
    small_mode.bits_per_pixel = 8;

    MockFramebuffer fb(small_mode);

    auto pixels = fb.get_indexed_pixels();
    EXPECT_EQ(pixels.size(), 1);

    fb.set_pixel(0, 0, 255);
    EXPECT_EQ(pixels[0], 255);
}

TEST(EdgeCaseTest, OutOfBoundsSetPixelIgnored) {
    MockFramebuffer fb(modes::MODE_13H);

    // These should not crash
    fb.set_pixel(320, 0, 1);  // Out of bounds x
    fb.set_pixel(0, 200, 1);  // Out of bounds y

    // Verify corners are still 0
    auto pixels = fb.get_indexed_pixels();
    EXPECT_EQ(pixels[0], 0);
    EXPECT_EQ(pixels[319], 0);
}

TEST(EdgeCaseTest, ModeX) {
    VgaModeInfo info = modes::MODE_X;
    EXPECT_EQ(info.width, 320);
    EXPECT_EQ(info.height, 240);
    EXPECT_TRUE(info.is_planar);
}
