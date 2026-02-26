// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Integration tests for dynamic resolution handling using PAL Headless context.

#include <gtest/gtest.h>
#include <pal/platform.h>
#include <pal/context.h>
#include <pal/window.h>

#include <cstring>
#include <memory>

namespace {

class DynamicResolutionTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        ASSERT_EQ(pal::Platform::initialize(pal::Backend::Headless), pal::Result::Success);
        window_ = pal::Platform::createWindow();
        ASSERT_NE(window_, nullptr);
        pal::WindowConfig wcfg;
        ASSERT_EQ(window_->create(wcfg), pal::Result::Success);
        context_ = pal::Platform::createContext(*window_);
        ASSERT_NE(context_, nullptr);
    }

    void TearDown() override {
        context_.reset();
        window_.reset();
        pal::Platform::shutdown();
    }

    std::unique_ptr<pal::IWindow>  window_;
    std::unique_ptr<pal::IContext> context_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Context Recreation
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(DynamicResolutionTest, CreateInitial) {
    auto res = context_->createSoftware(640, 480, pal::PixelFormat::RGB888);
    EXPECT_EQ(res, pal::Result::Success);
    EXPECT_TRUE(context_->isCreated());
}

TEST_F(DynamicResolutionTest, RecreateNewResolution) {
    ASSERT_EQ(context_->createSoftware(640, 480, pal::PixelFormat::RGB888), pal::Result::Success);
    context_->destroy();
    EXPECT_FALSE(context_->isCreated());
    auto res = context_->createSoftware(320, 200, pal::PixelFormat::RGB888);
    EXPECT_EQ(res, pal::Result::Success);
    EXPECT_TRUE(context_->isCreated());
}

TEST_F(DynamicResolutionTest, RecreateUpscale) {
    ASSERT_EQ(context_->createSoftware(320, 200, pal::PixelFormat::RGB888), pal::Result::Success);
    context_->destroy();
    auto res = context_->createSoftware(800, 600, pal::PixelFormat::RGB888);
    EXPECT_EQ(res, pal::Result::Success);
}

TEST_F(DynamicResolutionTest, SurfaceWritableAfterRecreate) {
    ASSERT_EQ(context_->createSoftware(640, 480, pal::PixelFormat::RGB888), pal::Result::Success);
    context_->destroy();
    ASSERT_EQ(context_->createSoftware(320, 200, pal::PixelFormat::RGB888), pal::Result::Success);

    pal::SoftwareContext sctx;
    auto res = context_->lockSurface(sctx);
    EXPECT_EQ(res, pal::Result::Success);
    EXPECT_NE(sctx.pixels, nullptr);
    EXPECT_EQ(sctx.width, 320u);
    EXPECT_EQ(sctx.height, 200u);

    // Write a pixel to verify the surface is writable
    if (sctx.pixels) {
        std::memset(sctx.pixels, 0xFF, sctx.pitch);
    }

    context_->unlockSurface();
}

// ═══════════════════════════════════════════════════════════════════════════
// Logical Size
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(DynamicResolutionTest, SetLogicalSizeHeadlessNoOp) {
    ASSERT_EQ(context_->createSoftware(640, 480, pal::PixelFormat::RGB888), pal::Result::Success);
    // setLogicalSize is a no-op on headless; just verify no crash
    context_->setLogicalSize(640, 480);
}

TEST_F(DynamicResolutionTest, SetLogicalSizeZeroNoCrash) {
    ASSERT_EQ(context_->createSoftware(640, 480, pal::PixelFormat::RGB888), pal::Result::Success);
    context_->setLogicalSize(0, 0); // should not crash
}

TEST_F(DynamicResolutionTest, SetLogicalSizeBeforeCreateNoCrash) {
    // Context not created yet — should not crash
    context_->setLogicalSize(800, 600);
}

// ═══════════════════════════════════════════════════════════════════════════
// Full Workflow
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(DynamicResolutionTest, FullResolutionChangeWorkflow) {
    // 1. Create initial context at 640x480
    ASSERT_EQ(context_->createSoftware(640, 480, pal::PixelFormat::RGB888), pal::Result::Success);
    context_->setLogicalSize(640, 480);

    // 2. Lock and write a frame
    {
        pal::SoftwareContext sctx;
        ASSERT_EQ(context_->lockSurface(sctx), pal::Result::Success);
        EXPECT_EQ(sctx.width, 640u);
        EXPECT_EQ(sctx.height, 480u);
        context_->unlockSurface();
    }

    // 3. Simulate engine resolution change: destroy + recreate at 320x200
    context_->destroy();
    ASSERT_EQ(context_->createSoftware(320, 200, pal::PixelFormat::RGB888), pal::Result::Success);
    context_->setLogicalSize(320, 200);

    // 4. Lock and write a frame at new resolution
    {
        pal::SoftwareContext sctx;
        ASSERT_EQ(context_->lockSurface(sctx), pal::Result::Success);
        EXPECT_EQ(sctx.width, 320u);
        EXPECT_EQ(sctx.height, 200u);
        if (sctx.pixels) {
            std::memset(sctx.pixels, 0x42, sctx.pitch);
        }
        context_->unlockSurface();
    }
}

} // namespace
