/**
 * @file test_display_integration.cpp
 * @brief Unit tests for platform display integration (PR #18).
 *
 * Tests:
 * - Headless stub display provider integration
 * - DOSBoxContext display provider configuration
 * - HeadlessDisplay through context
 * - Custom display provider injection
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/platform/display.h"
#include "dosbox/platform/headless.h"
#include "aibox/headless_stub.h"

using namespace dosbox;
using namespace dosbox::platform;

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Stub Display Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessDisplayTest, DefaultNoProvider) {
    // Clear any existing provider
    aibox::headless::SetDisplayProvider(nullptr);

    EXPECT_FALSE(aibox::headless::HasDisplayProvider());
    EXPECT_EQ(aibox::headless::GetDisplayProvider(), nullptr);
}

TEST(HeadlessDisplayTest, SetDisplayProvider) {
    HeadlessDisplay display;

    aibox::headless::SetDisplayProvider(&display);

    EXPECT_TRUE(aibox::headless::HasDisplayProvider());
    EXPECT_EQ(aibox::headless::GetDisplayProvider(), &display);

    // Clean up
    aibox::headless::SetDisplayProvider(nullptr);
}

TEST(HeadlessDisplayTest, UploadFrameUsesProvider) {
    HeadlessDisplay display;
    display.set_mode(320, 200, PixelFormat::Indexed8, false);

    aibox::headless::SetDisplayProvider(&display);

    // Create test frame data
    std::vector<uint8_t> pixels(320 * 200, 0x42);

    // Upload frame through headless stub
    aibox::headless::UploadFrame(pixels.data(), pixels.size(), 320, 200, 8);

    // Display should have received the frame
    EXPECT_TRUE(display.has_frame());
    EXPECT_EQ(display.frame_count(), 1u);

    auto captured = display.capture_frame();
    EXPECT_EQ(captured.size(), pixels.size());
    EXPECT_EQ(captured[0], 0x42);

    // Clean up
    aibox::headless::SetDisplayProvider(nullptr);
}

TEST(HeadlessDisplayTest, SetPaletteUsesProvider) {
    HeadlessDisplay display;
    display.set_mode(320, 200, PixelFormat::Indexed8, false);

    aibox::headless::SetDisplayProvider(&display);

    // Create RGB palette (768 bytes)
    std::vector<uint8_t> rgb_palette(768);
    for (size_t i = 0; i < 256; ++i) {
        rgb_palette[i * 3 + 0] = static_cast<uint8_t>(i);      // R
        rgb_palette[i * 3 + 1] = static_cast<uint8_t>(i / 2);  // G
        rgb_palette[i * 3 + 2] = static_cast<uint8_t>(i / 4);  // B
    }

    // Set palette through headless stub
    aibox::headless::SetPalette(rgb_palette.data(), rgb_palette.size());

    // Verify palette was converted to RGBA and set
    auto stored_palette = display.get_palette();
    EXPECT_EQ(stored_palette.size(), 1024u);  // 256 * 4 RGBA

    // Check first few entries
    EXPECT_EQ(stored_palette[0], 0);    // R
    EXPECT_EQ(stored_palette[1], 0);    // G
    EXPECT_EQ(stored_palette[2], 0);    // B
    EXPECT_EQ(stored_palette[3], 255);  // A (added)

    EXPECT_EQ(stored_palette[4], 1);    // R
    EXPECT_EQ(stored_palette[5], 0);    // G
    EXPECT_EQ(stored_palette[6], 0);    // B
    EXPECT_EQ(stored_palette[7], 255);  // A

    // Clean up
    aibox::headless::SetDisplayProvider(nullptr);
}

// ═══════════════════════════════════════════════════════════════════════════════
// DOSBoxContext Display Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextDisplayTest, HasBuiltInHeadlessDisplay) {
    DOSBoxContext ctx;

    // Context has its own headless display
    auto& display = ctx.headless_display();

    // Should be empty initially
    EXPECT_FALSE(display.has_frame());
    EXPECT_EQ(display.frame_count(), 0u);
}

TEST(ContextDisplayTest, DefaultNoCustomProvider) {
    DOSBoxContext ctx;

    EXPECT_EQ(ctx.get_display_provider(), nullptr);
}

TEST(ContextDisplayTest, SetCustomDisplayProvider) {
    DOSBoxContext ctx;
    HeadlessDisplay custom_display;

    ctx.set_display_provider(&custom_display);

    EXPECT_EQ(ctx.get_display_provider(), &custom_display);
}

TEST(ContextDisplayTest, CurrentContextUsesBuiltInDisplay) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Clear any previous state
    aibox::headless::SetDisplayProvider(nullptr);

    // Set as current context
    ContextGuard guard(ctx);

    // Should have wired up the built-in headless display
    EXPECT_TRUE(aibox::headless::HasDisplayProvider());
    EXPECT_EQ(aibox::headless::GetDisplayProvider(), &ctx.headless_display());
}

TEST(ContextDisplayTest, CurrentContextUsesCustomProvider) {
    DOSBoxContext ctx;
    ctx.initialize();
    HeadlessDisplay custom_display;

    // Set custom provider
    ctx.set_display_provider(&custom_display);

    // Set as current context
    ContextGuard guard(ctx);

    // Should use custom provider
    EXPECT_EQ(aibox::headless::GetDisplayProvider(), &custom_display);
}

TEST(ContextDisplayTest, ContextSwitchingUpdatesProvider) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Upload frame to ctx1's display
    ctx1.headless_display().set_mode(320, 200, PixelFormat::Indexed8, false);
    std::vector<uint8_t> frame1(320 * 200, 0x11);
    FrameInfo info1{320, 200, PixelFormat::Indexed8, 320, false};
    ctx1.headless_display().upload_frame(frame1, info1);

    // Upload different frame to ctx2's display
    ctx2.headless_display().set_mode(640, 480, PixelFormat::BGRA8888, false);
    std::vector<uint8_t> frame2(640 * 480 * 4, 0x22);
    FrameInfo info2{640, 480, PixelFormat::BGRA8888, 640 * 4, false};
    ctx2.headless_display().upload_frame(frame2, info2);

    {
        ContextGuard guard1(ctx1);
        auto* provider = aibox::headless::GetDisplayProvider();
        EXPECT_EQ(provider, &ctx1.headless_display());
        EXPECT_TRUE(provider->has_frame());
        auto frame_info = provider->get_frame_info();
        EXPECT_EQ(frame_info.width, 320);
    }

    {
        ContextGuard guard2(ctx2);
        auto* provider = aibox::headless::GetDisplayProvider();
        EXPECT_EQ(provider, &ctx2.headless_display());
        EXPECT_TRUE(provider->has_frame());
        auto frame_info = provider->get_frame_info();
        EXPECT_EQ(frame_info.width, 640);
    }

    // Back to ctx1
    {
        ContextGuard guard1(ctx1);
        auto frame_info = aibox::headless::GetDisplayProvider()->get_frame_info();
        EXPECT_EQ(frame_info.width, 320);
    }
}

TEST(ContextDisplayTest, ClearCurrentContextClearsProvider) {
    DOSBoxContext ctx;
    ctx.initialize();

    set_current_context(&ctx);
    EXPECT_TRUE(aibox::headless::HasDisplayProvider());

    set_current_context(nullptr);
    EXPECT_FALSE(aibox::headless::HasDisplayProvider());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Backend Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessBackendDisplayTest, BackendDisplayIntegration) {
    auto backend = make_headless_backend();
    DOSBoxContext ctx;
    ctx.initialize();

    // Use headless backend display with context
    ctx.set_display_provider(&backend->display);

    ContextGuard guard(ctx);

    // Display should flow through backend
    backend->display.set_mode(320, 200, PixelFormat::Indexed8, false);

    // Upload frame through headless stub
    std::vector<uint8_t> pixels(320 * 200, 0x55);
    aibox::headless::UploadFrame(pixels.data(), pixels.size(), 320, 200, 8);

    EXPECT_TRUE(backend->display.has_frame());
    EXPECT_EQ(backend->display.frame_count(), 1u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Frame Capture Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(FrameCaptureTest, CaptureFrameFromContext) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    // Set up display mode
    ctx.headless_display().set_mode(320, 200, PixelFormat::Indexed8, false);

    // Create and upload test frame
    std::vector<uint8_t> pixels(320 * 200);
    for (size_t i = 0; i < pixels.size(); ++i) {
        pixels[i] = static_cast<uint8_t>(i % 256);
    }

    aibox::headless::UploadFrame(pixels.data(), pixels.size(), 320, 200, 8);

    // Capture frame
    auto captured = ctx.headless_display().capture_frame();

    EXPECT_EQ(captured.size(), pixels.size());
    for (size_t i = 0; i < 100; ++i) {
        EXPECT_EQ(captured[i], pixels[i]);
    }
}

TEST(FrameCaptureTest, CapturePreservesAcrossContextSwitch) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Set up both displays
    ctx1.headless_display().set_mode(320, 200, PixelFormat::Indexed8, false);
    ctx2.headless_display().set_mode(320, 200, PixelFormat::Indexed8, false);

    // Upload different frames to each context
    std::vector<uint8_t> frame1(320 * 200, 0xAA);
    std::vector<uint8_t> frame2(320 * 200, 0xBB);

    {
        ContextGuard guard1(ctx1);
        aibox::headless::UploadFrame(frame1.data(), frame1.size(), 320, 200, 8);
    }

    {
        ContextGuard guard2(ctx2);
        aibox::headless::UploadFrame(frame2.data(), frame2.size(), 320, 200, 8);
    }

    // Verify frames are preserved
    auto captured1 = ctx1.headless_display().capture_frame();
    auto captured2 = ctx2.headless_display().capture_frame();

    EXPECT_EQ(captured1[0], 0xAA);
    EXPECT_EQ(captured2[0], 0xBB);
}
