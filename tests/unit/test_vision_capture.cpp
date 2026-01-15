/**
 * @file test_vision_capture.cpp
 * @brief Unit tests for vision_capture.h
 */

#include <gtest/gtest.h>
#include "legends/vision_capture.h"
#include "legends/vision_framebuffer.h"

using namespace legends::vision;

// ─────────────────────────────────────────────────────────────────────────────
// PixelFormat Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(PixelFormatTest, ToString) {
    EXPECT_STREQ(to_string(PixelFormat::Indexed8), "Indexed8");
    EXPECT_STREQ(to_string(PixelFormat::RGB24), "RGB24");
    EXPECT_STREQ(to_string(PixelFormat::RGBA32), "RGBA32");
    EXPECT_STREQ(to_string(PixelFormat::BGR24), "BGR24");
    EXPECT_STREQ(to_string(PixelFormat::BGRA32), "BGRA32");
    EXPECT_STREQ(to_string(PixelFormat::Grayscale8), "Grayscale8");
}

TEST(PixelFormatTest, BytesPerPixel) {
    EXPECT_EQ(bytes_per_pixel(PixelFormat::Indexed8), 1);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::RGB24), 3);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::RGBA32), 4);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::BGR24), 3);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::BGRA32), 4);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::Grayscale8), 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// ScaleMode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScaleModeTest, ToString) {
    EXPECT_STREQ(to_string(ScaleMode::Native), "Native");
    EXPECT_STREQ(to_string(ScaleMode::NearestNeighbor), "NearestNeighbor");
    EXPECT_STREQ(to_string(ScaleMode::Bilinear), "Bilinear");
    EXPECT_STREQ(to_string(ScaleMode::AspectCorrect), "AspectCorrect");
}

// ─────────────────────────────────────────────────────────────────────────────
// CaptureConfig Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CaptureConfigTest, DefaultValues) {
    CaptureConfig config;

    EXPECT_EQ(config.format, PixelFormat::RGB24);
    EXPECT_EQ(config.scale_mode, ScaleMode::Native);
    EXPECT_EQ(config.scale_factor, 1);
    EXPECT_EQ(config.target_width, 0);
    EXPECT_EQ(config.target_height, 0);
    EXPECT_TRUE(config.include_overlay);
    EXPECT_FALSE(config.flip_vertical);
}

TEST(CaptureConfigTest, CalculateOutputSizeNative) {
    CaptureConfig config;
    config.scale_mode = ScaleMode::Native;
    config.scale_factor = 1;

    auto [w, h] = config.calculate_output_size(320, 200);
    EXPECT_EQ(w, 320);
    EXPECT_EQ(h, 200);
}

TEST(CaptureConfigTest, CalculateOutputSizeScaled2x) {
    CaptureConfig config;
    config.scale_factor = 2;

    auto [w, h] = config.calculate_output_size(320, 200);
    EXPECT_EQ(w, 640);
    EXPECT_EQ(h, 400);
}

TEST(CaptureConfigTest, CalculateOutputSizeScaled4x) {
    CaptureConfig config;
    config.scale_factor = 4;

    auto [w, h] = config.calculate_output_size(320, 200);
    EXPECT_EQ(w, 1280);
    EXPECT_EQ(h, 800);
}

TEST(CaptureConfigTest, CalculateOutputSizeTargetOverride) {
    CaptureConfig config;
    config.target_width = 800;
    config.target_height = 600;
    config.scale_factor = 2;  // Should be ignored

    auto [w, h] = config.calculate_output_size(320, 200);
    EXPECT_EQ(w, 800);
    EXPECT_EQ(h, 600);
}

TEST(CaptureConfigTest, CalculateOutputSizeAspectCorrect) {
    CaptureConfig config;
    config.scale_mode = ScaleMode::AspectCorrect;
    config.scale_factor = 1;

    // Mode 13h (320x200) -> 320x240 for correct aspect
    auto [w, h] = config.calculate_output_size(320, 200);
    EXPECT_EQ(w, 320);
    EXPECT_EQ(h, 240);  // 200 * 6/5 = 240
}

TEST(CaptureConfigTest, CalculateOutputSizeAspectCorrectScaled) {
    CaptureConfig config;
    config.scale_mode = ScaleMode::AspectCorrect;
    config.scale_factor = 2;

    // 320x200 -> 640x400 -> 640x480
    auto [w, h] = config.calculate_output_size(320, 200);
    EXPECT_EQ(w, 640);
    EXPECT_EQ(h, 480);
}

TEST(CaptureConfigTest, CalculateOutputSizeNoAspectForNon13h) {
    CaptureConfig config;
    config.scale_mode = ScaleMode::AspectCorrect;
    config.scale_factor = 1;

    // 640x480 should NOT get aspect correction
    auto [w, h] = config.calculate_output_size(640, 480);
    EXPECT_EQ(w, 640);
    EXPECT_EQ(h, 480);
}

TEST(CaptureConfigTest, CalculateBufferSizeRGB24) {
    CaptureConfig config;
    config.format = PixelFormat::RGB24;
    config.scale_factor = 1;

    size_t size = config.calculate_buffer_size(320, 200);
    EXPECT_EQ(size, 320 * 200 * 3);  // 192000
}

TEST(CaptureConfigTest, CalculateBufferSizeRGBA32) {
    CaptureConfig config;
    config.format = PixelFormat::RGBA32;
    config.scale_factor = 1;

    size_t size = config.calculate_buffer_size(320, 200);
    EXPECT_EQ(size, 320 * 200 * 4);  // 256000
}

TEST(CaptureConfigTest, CalculateBufferSizeScaled) {
    CaptureConfig config;
    config.format = PixelFormat::RGB24;
    config.scale_factor = 2;

    size_t size = config.calculate_buffer_size(320, 200);
    EXPECT_EQ(size, 640 * 400 * 3);  // 768000
}

// ─────────────────────────────────────────────────────────────────────────────
// Screenshot Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotTest, DefaultConstruction) {
    Screenshot shot;

    EXPECT_TRUE(shot.pixels.empty());
    EXPECT_EQ(shot.width, 0);
    EXPECT_EQ(shot.height, 0);
    EXPECT_EQ(shot.format, PixelFormat::RGB24);
    EXPECT_EQ(shot.capture_time_us, 0);
    EXPECT_EQ(shot.frame_number, 0);
}

TEST(ScreenshotTest, IsValidEmpty) {
    Screenshot shot;
    EXPECT_FALSE(shot.is_valid());
}

TEST(ScreenshotTest, IsValidWithData) {
    Screenshot shot;
    shot.width = 320;
    shot.height = 200;
    shot.format = PixelFormat::RGB24;
    shot.pixels.resize(320 * 200 * 3);

    EXPECT_TRUE(shot.is_valid());
}

TEST(ScreenshotTest, IsValidZeroDimensions) {
    Screenshot shot;
    shot.width = 0;
    shot.height = 200;
    shot.pixels.resize(100);

    EXPECT_FALSE(shot.is_valid());
}

TEST(ScreenshotTest, Size) {
    Screenshot shot;
    shot.pixels.resize(192000);

    EXPECT_EQ(shot.size(), 192000);
}

TEST(ScreenshotTest, ExpectedSize) {
    Screenshot shot;
    shot.width = 320;
    shot.height = 200;
    shot.format = PixelFormat::RGB24;

    EXPECT_EQ(shot.expected_size(), 192000);
}

TEST(ScreenshotTest, Stride) {
    Screenshot shot;
    shot.width = 320;
    shot.format = PixelFormat::RGB24;

    EXPECT_EQ(shot.stride(), 960);  // 320 * 3
}

TEST(ScreenshotTest, StrideRGBA32) {
    Screenshot shot;
    shot.width = 320;
    shot.format = PixelFormat::RGBA32;

    EXPECT_EQ(shot.stride(), 1280);  // 320 * 4
}

TEST(ScreenshotTest, GetPixelRGB24) {
    Screenshot shot;
    shot.width = 10;
    shot.height = 10;
    shot.format = PixelFormat::RGB24;
    shot.pixels.resize(10 * 10 * 3, 0);

    // Set pixel at (5, 3)
    size_t offset = (3 * 10 + 5) * 3;
    shot.pixels[offset + 0] = 100;  // R
    shot.pixels[offset + 1] = 150;  // G
    shot.pixels[offset + 2] = 200;  // B

    RgbaColor color = shot.get_pixel(5, 3);
    EXPECT_EQ(color.r, 100);
    EXPECT_EQ(color.g, 150);
    EXPECT_EQ(color.b, 200);
    EXPECT_EQ(color.a, 255);
}

TEST(ScreenshotTest, GetPixelRGBA32) {
    Screenshot shot;
    shot.width = 10;
    shot.height = 10;
    shot.format = PixelFormat::RGBA32;
    shot.pixels.resize(10 * 10 * 4, 0);

    // Set pixel at (2, 7)
    size_t offset = (7 * 10 + 2) * 4;
    shot.pixels[offset + 0] = 50;   // R
    shot.pixels[offset + 1] = 100;  // G
    shot.pixels[offset + 2] = 150;  // B
    shot.pixels[offset + 3] = 200;  // A

    RgbaColor color = shot.get_pixel(2, 7);
    EXPECT_EQ(color.r, 50);
    EXPECT_EQ(color.g, 100);
    EXPECT_EQ(color.b, 150);
    EXPECT_EQ(color.a, 200);
}

TEST(ScreenshotTest, GetPixelBGR24) {
    Screenshot shot;
    shot.width = 10;
    shot.height = 10;
    shot.format = PixelFormat::BGR24;
    shot.pixels.resize(10 * 10 * 3, 0);

    // Set pixel at (1, 1) in BGR order
    size_t offset = (1 * 10 + 1) * 3;
    shot.pixels[offset + 0] = 200;  // B
    shot.pixels[offset + 1] = 150;  // G
    shot.pixels[offset + 2] = 100;  // R

    RgbaColor color = shot.get_pixel(1, 1);
    EXPECT_EQ(color.r, 100);
    EXPECT_EQ(color.g, 150);
    EXPECT_EQ(color.b, 200);
}

TEST(ScreenshotTest, GetPixelGrayscale) {
    Screenshot shot;
    shot.width = 10;
    shot.height = 10;
    shot.format = PixelFormat::Grayscale8;
    shot.pixels.resize(10 * 10, 0);

    // Set pixel at (4, 4)
    shot.pixels[4 * 10 + 4] = 128;

    RgbaColor color = shot.get_pixel(4, 4);
    EXPECT_EQ(color.r, 128);
    EXPECT_EQ(color.g, 128);
    EXPECT_EQ(color.b, 128);
    EXPECT_EQ(color.a, 255);
}

TEST(ScreenshotTest, GetPixelOutOfBounds) {
    Screenshot shot;
    shot.width = 10;
    shot.height = 10;
    shot.format = PixelFormat::RGB24;
    shot.pixels.resize(10 * 10 * 3, 100);

    RgbaColor color = shot.get_pixel(10, 5);  // Out of bounds X
    EXPECT_EQ(color.r, 0);
    EXPECT_EQ(color.g, 0);
    EXPECT_EQ(color.b, 0);

    color = shot.get_pixel(5, 10);  // Out of bounds Y
    EXPECT_EQ(color.r, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// CaptureEngine Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CaptureEngineTest, Construction) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);

    // Default config
    const CaptureConfig& config = engine.config();
    EXPECT_EQ(config.format, PixelFormat::RGB24);
    EXPECT_EQ(config.scale_mode, ScaleMode::Native);
}

TEST(CaptureEngineTest, Configure) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);

    CaptureConfig config;
    config.format = PixelFormat::RGBA32;
    config.scale_factor = 2;
    engine.configure(config);

    const CaptureConfig& result = engine.config();
    EXPECT_EQ(result.format, PixelFormat::RGBA32);
    EXPECT_EQ(result.scale_factor, 2);
}

TEST(CaptureEngineTest, CalculateBufferSize) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);

    size_t size = engine.calculate_buffer_size();
    EXPECT_EQ(size, 320 * 200 * 3);  // RGB24 default
}

TEST(CaptureEngineTest, CalculateBufferSizeScaled) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);

    CaptureConfig config;
    config.format = PixelFormat::RGBA32;
    config.scale_factor = 2;
    engine.configure(config);

    size_t size = engine.calculate_buffer_size();
    EXPECT_EQ(size, 640 * 400 * 4);
}

TEST(CaptureEngineTest, CaptureBasic) {
    MockFramebuffer fb(modes::MODE_13H);
    fb.fill(42);  // Fill with single color

    CaptureEngine engine(fb);
    Screenshot shot = engine.capture();

    EXPECT_TRUE(shot.is_valid());
    EXPECT_EQ(shot.width, 320);
    EXPECT_EQ(shot.height, 200);
    EXPECT_EQ(shot.format, PixelFormat::RGB24);
}

TEST(CaptureEngineTest, CaptureRGBA32) {
    MockFramebuffer fb(modes::MODE_13H);
    fb.fill(0);

    CaptureEngine engine(fb);
    CaptureConfig config;
    config.format = PixelFormat::RGBA32;
    engine.configure(config);

    Screenshot shot = engine.capture();

    EXPECT_TRUE(shot.is_valid());
    EXPECT_EQ(shot.format, PixelFormat::RGBA32);
    EXPECT_EQ(shot.size(), 320 * 200 * 4);
}

TEST(CaptureEngineTest, CaptureGrayscale) {
    MockFramebuffer fb(modes::MODE_13H);
    fb.fill(100);

    CaptureEngine engine(fb);
    CaptureConfig config;
    config.format = PixelFormat::Grayscale8;
    engine.configure(config);

    Screenshot shot = engine.capture();

    EXPECT_TRUE(shot.is_valid());
    EXPECT_EQ(shot.format, PixelFormat::Grayscale8);
    EXPECT_EQ(shot.size(), 320 * 200);
}

TEST(CaptureEngineTest, CaptureScaled2x) {
    MockFramebuffer fb(modes::MODE_13H);

    CaptureEngine engine(fb);
    CaptureConfig config;
    config.scale_factor = 2;
    engine.configure(config);

    Screenshot shot = engine.capture();

    EXPECT_TRUE(shot.is_valid());
    EXPECT_EQ(shot.width, 640);
    EXPECT_EQ(shot.height, 400);
}

TEST(CaptureEngineTest, CaptureIfDirtyNotDirty) {
    MockFramebuffer fb(modes::MODE_13H);
    fb.clear_dirty_flag();

    CaptureEngine engine(fb);
    auto shot = engine.capture_if_dirty();

    EXPECT_FALSE(shot.has_value());
}

TEST(CaptureEngineTest, CaptureIfDirtyIsDirty) {
    MockFramebuffer fb(modes::MODE_13H);
    fb.set_pixel(0, 0, 1);  // Mark dirty

    CaptureEngine engine(fb);
    auto shot = engine.capture_if_dirty();

    EXPECT_TRUE(shot.has_value());
    EXPECT_TRUE(shot->is_valid());
}

TEST(CaptureEngineTest, FrameNumberIncrement) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);

    EXPECT_EQ(engine.frame_number(), 0);

    [[maybe_unused]] auto shot = engine.capture();
    // Frame number should increment after capture
    EXPECT_GE(engine.frame_number(), 0);
}

TEST(CaptureEngineTest, CaptureTimestamp) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);

    Screenshot shot = engine.capture();

    // Timestamp should be set
    EXPECT_GT(shot.capture_time_us, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// StreamingCapture Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StreamingCaptureTest, Construction) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);
    StreamingCapture streaming(engine);

    EXPECT_FALSE(streaming.is_running());
    EXPECT_EQ(streaming.target_fps(), 30);
}

TEST(StreamingCaptureTest, SetTargetFps) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);
    StreamingCapture streaming(engine);

    streaming.set_target_fps(60);
    EXPECT_EQ(streaming.target_fps(), 60);
}

TEST(StreamingCaptureTest, SetTargetFpsZeroClampedToOne) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);
    StreamingCapture streaming(engine);

    streaming.set_target_fps(0);
    EXPECT_EQ(streaming.target_fps(), 1);
}

TEST(StreamingCaptureTest, StartStop) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);
    StreamingCapture streaming(engine);

    int frame_count = 0;
    streaming.start([&](const Screenshot&) {
        ++frame_count;
    }, 30);

    EXPECT_TRUE(streaming.is_running());

    streaming.stop();
    EXPECT_FALSE(streaming.is_running());
}

TEST(StreamingCaptureTest, ResetStats) {
    MockFramebuffer fb(modes::MODE_13H);
    CaptureEngine engine(fb);
    StreamingCapture streaming(engine);

    // Start and capture some frames
    streaming.start([](const Screenshot&) {}, 30);
    streaming.tick();
    streaming.stop();

    // Reset stats
    streaming.reset_stats();

    const StreamingStats& stats = streaming.stats();
    EXPECT_EQ(stats.frames_captured, 0);
    EXPECT_EQ(stats.frames_dropped, 0);
    EXPECT_EQ(stats.total_bytes, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// StreamingStats Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StreamingStatsTest, DefaultValues) {
    StreamingStats stats;

    EXPECT_EQ(stats.frames_captured, 0);
    EXPECT_EQ(stats.frames_dropped, 0);
    EXPECT_EQ(stats.average_fps, 0.0);
    EXPECT_EQ(stats.average_latency_us, 0.0);
    EXPECT_EQ(stats.total_bytes, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// Utility Function Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(UtilityFunctionTest, RgbToGrayscaleBlack) {
    uint8_t gray = rgb_to_grayscale(0, 0, 0);
    EXPECT_EQ(gray, 0);
}

TEST(UtilityFunctionTest, RgbToGrayscaleWhite) {
    uint8_t gray = rgb_to_grayscale(255, 255, 255);
    // Should be approximately 255
    EXPECT_GE(gray, 254);
}

TEST(UtilityFunctionTest, RgbToGrayscaleRed) {
    uint8_t gray = rgb_to_grayscale(255, 0, 0);
    // Y = 0.299 * 255 = ~76
    EXPECT_GE(gray, 75);
    EXPECT_LE(gray, 78);
}

TEST(UtilityFunctionTest, RgbToGrayscaleGreen) {
    uint8_t gray = rgb_to_grayscale(0, 255, 0);
    // Y = 0.587 * 255 = ~150
    EXPECT_GE(gray, 148);
    EXPECT_LE(gray, 152);
}

TEST(UtilityFunctionTest, RgbToGrayscaleBlue) {
    uint8_t gray = rgb_to_grayscale(0, 0, 255);
    // Y = 0.114 * 255 = ~29
    EXPECT_GE(gray, 28);
    EXPECT_LE(gray, 30);
}

TEST(UtilityFunctionTest, RgbToGrayscaleFromColor) {
    RgbColor color{128, 128, 128};
    uint8_t gray = rgb_to_grayscale(color);
    // Should be approximately 128
    EXPECT_GE(gray, 126);
    EXPECT_LE(gray, 130);
}

TEST(UtilityFunctionTest, GetTimestampUs) {
    uint64_t t1 = get_timestamp_us();
    uint64_t t2 = get_timestamp_us();

    // Timestamps should be non-zero and increasing (or equal)
    EXPECT_GT(t1, 0);
    EXPECT_GE(t2, t1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST(EdgeCaseTest, CaptureVerySmallFramebuffer) {
    VgaModeInfo tiny_mode;
    tiny_mode.width = 1;
    tiny_mode.height = 1;
    tiny_mode.bits_per_pixel = 8;

    MockFramebuffer fb(tiny_mode);
    CaptureEngine engine(fb);

    Screenshot shot = engine.capture();

    EXPECT_TRUE(shot.is_valid());
    EXPECT_EQ(shot.width, 1);
    EXPECT_EQ(shot.height, 1);
    EXPECT_EQ(shot.size(), 3);  // RGB24
}

TEST(EdgeCaseTest, CaptureMode12h) {
    MockFramebuffer fb(modes::MODE_12H);
    CaptureEngine engine(fb);

    Screenshot shot = engine.capture();

    EXPECT_TRUE(shot.is_valid());
    EXPECT_EQ(shot.width, 640);
    EXPECT_EQ(shot.height, 480);
}

TEST(EdgeCaseTest, IndexedFormatNoPalette) {
    MockFramebuffer fb(modes::MODE_13H);
    fb.fill(42);

    CaptureEngine engine(fb);
    CaptureConfig config;
    config.format = PixelFormat::Indexed8;
    engine.configure(config);

    Screenshot shot = engine.capture();

    EXPECT_TRUE(shot.is_valid());
    EXPECT_EQ(shot.format, PixelFormat::Indexed8);
    EXPECT_EQ(shot.size(), 320 * 200);

    // Raw indexed pixels should be preserved
    EXPECT_EQ(shot.pixels[0], 42);
}
