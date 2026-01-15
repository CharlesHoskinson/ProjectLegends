// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors

#include <gtest/gtest.h>
#include "pal/platform.h"
#include "pal/context.h"
#include <cstring>

namespace pal {
namespace {

class PalContextTest : public ::testing::Test {
protected:
    void SetUp() override {
        Platform::shutdown();
        ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
        window_ = Platform::createWindow();
        ASSERT_NE(window_, nullptr);
        WindowConfig config;
        ASSERT_EQ(window_->create(config), Result::Success);
        context_ = Platform::createContext(*window_);
        ASSERT_NE(context_, nullptr);
    }

    void TearDown() override {
        context_.reset();
        window_.reset();
        Platform::shutdown();
    }

    std::unique_ptr<IWindow> window_;
    std::unique_ptr<IContext> context_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Software Context Creation Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalContextTest, CreateSoftwareContext) {
    Result result = context_->createSoftware(640, 480, PixelFormat::RGBA8888);
    EXPECT_EQ(result, Result::Success);
    EXPECT_TRUE(context_->isCreated());
    EXPECT_EQ(context_->getType(), ContextType::Software);
}

TEST_F(PalContextTest, CreateSoftwareWithRGB888) {
    Result result = context_->createSoftware(640, 480, PixelFormat::RGB888);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalContextTest, CreateSoftwareWithRGB565) {
    Result result = context_->createSoftware(640, 480, PixelFormat::RGB565);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalContextTest, CreateSoftwareWithBGRA8888) {
    Result result = context_->createSoftware(640, 480, PixelFormat::BGRA8888);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalContextTest, CreateSoftwareWithIndexed8) {
    Result result = context_->createSoftware(640, 480, PixelFormat::Indexed8);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalContextTest, CreateSoftwareZeroWidthFails) {
    Result result = context_->createSoftware(0, 480, PixelFormat::RGBA8888);
    EXPECT_EQ(result, Result::InvalidParameter);
    EXPECT_FALSE(context_->isCreated());
}

TEST_F(PalContextTest, CreateSoftwareZeroHeightFails) {
    Result result = context_->createSoftware(640, 0, PixelFormat::RGBA8888);
    EXPECT_EQ(result, Result::InvalidParameter);
}

TEST_F(PalContextTest, CreateSoftwareUnknownFormatFails) {
    Result result = context_->createSoftware(640, 480, PixelFormat::Unknown);
    EXPECT_EQ(result, Result::InvalidParameter);
}

TEST_F(PalContextTest, CreateSoftwareTwiceFails) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);
    EXPECT_EQ(context_->createSoftware(320, 240, PixelFormat::RGB888), Result::AlreadyInitialized);
}

// ═══════════════════════════════════════════════════════════════════════════
// OpenGL Context Creation Tests (Headless = Stub)
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalContextTest, CreateOpenGLContext) {
    Result result = context_->createOpenGL(3, 3, true);
    EXPECT_EQ(result, Result::Success);
    EXPECT_TRUE(context_->isCreated());
    EXPECT_EQ(context_->getType(), ContextType::OpenGL);
}

TEST_F(PalContextTest, CreateOpenGL21Compat) {
    Result result = context_->createOpenGL(2, 1, false);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalContextTest, CreateOpenGLTwiceFails) {
    ASSERT_EQ(context_->createOpenGL(3, 3, true), Result::Success);
    EXPECT_EQ(context_->createOpenGL(2, 1, false), Result::AlreadyInitialized);
}

// ═══════════════════════════════════════════════════════════════════════════
// Context Lifecycle Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalContextTest, DestroyAfterCreate) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);
    context_->destroy();
    EXPECT_FALSE(context_->isCreated());
    EXPECT_EQ(context_->getType(), ContextType::None);
}

TEST_F(PalContextTest, DestroyWithoutCreateIsSafe) {
    EXPECT_FALSE(context_->isCreated());
    context_->destroy();  // Should not crash
    EXPECT_FALSE(context_->isCreated());
}

TEST_F(PalContextTest, RecreateAfterDestroy) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);
    context_->destroy();
    EXPECT_EQ(context_->createSoftware(320, 240, PixelFormat::RGB888), Result::Success);
    EXPECT_TRUE(context_->isCreated());
}

TEST_F(PalContextTest, SwitchSoftwareToOpenGL) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);
    context_->destroy();
    EXPECT_EQ(context_->createOpenGL(3, 3, true), Result::Success);
    EXPECT_EQ(context_->getType(), ContextType::OpenGL);
}

// ═══════════════════════════════════════════════════════════════════════════
// Surface Lock/Unlock Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalContextTest, LockSoftwareSurface) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);

    SoftwareContext ctx;
    Result result = context_->lockSurface(ctx);
    EXPECT_EQ(result, Result::Success);
    EXPECT_NE(ctx.pixels, nullptr);
    EXPECT_GT(ctx.pitch, 0u);
    EXPECT_EQ(ctx.width, 640u);
    EXPECT_EQ(ctx.height, 480u);
    EXPECT_EQ(ctx.format, PixelFormat::RGBA8888);
    EXPECT_TRUE(context_->isLocked());
}

TEST_F(PalContextTest, UnlockSoftwareSurface) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);

    SoftwareContext ctx;
    ASSERT_EQ(context_->lockSurface(ctx), Result::Success);
    EXPECT_TRUE(context_->isLocked());

    context_->unlockSurface();
    EXPECT_FALSE(context_->isLocked());
}

TEST_F(PalContextTest, DoubleLockFails) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);

    SoftwareContext ctx;
    ASSERT_EQ(context_->lockSurface(ctx), Result::Success);
    EXPECT_EQ(context_->lockSurface(ctx), Result::AlreadyLocked);
}

TEST_F(PalContextTest, UnlockWithoutLockIsSafe) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);
    context_->unlockSurface();  // Should not crash
    EXPECT_FALSE(context_->isLocked());
}

TEST_F(PalContextTest, LockBeforeCreateFails) {
    SoftwareContext ctx;
    EXPECT_EQ(context_->lockSurface(ctx), Result::NotInitialized);
}

TEST_F(PalContextTest, LockOnOpenGLContextFails) {
    ASSERT_EQ(context_->createOpenGL(3, 3, true), Result::Success);
    SoftwareContext ctx;
    EXPECT_EQ(context_->lockSurface(ctx), Result::InvalidOperation);
}

TEST_F(PalContextTest, WriteToLockedSurface) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);

    SoftwareContext ctx;
    ASSERT_EQ(context_->lockSurface(ctx), Result::Success);

    // Write a pattern
    std::memset(ctx.pixels, 0xAB, ctx.pitch * ctx.height);

    context_->unlockSurface();
    // Should not crash - data was written
}

TEST_F(PalContextTest, PitchIsCorrect) {
    ASSERT_EQ(context_->createSoftware(641, 480, PixelFormat::RGBA8888), Result::Success);

    SoftwareContext ctx;
    ASSERT_EQ(context_->lockSurface(ctx), Result::Success);

    // Pitch should be at least width * bytes_per_pixel
    EXPECT_GE(ctx.pitch, 641u * 4u);
    // Pitch is often aligned to 4 bytes
    EXPECT_EQ(ctx.pitch % 4u, 0u);
}

// ═══════════════════════════════════════════════════════════════════════════
// OpenGL Operations Tests (Headless = Stubs)
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalContextTest, MakeCurrentSucceeds) {
    ASSERT_EQ(context_->createOpenGL(3, 3, true), Result::Success);
    EXPECT_EQ(context_->makeCurrent(), Result::Success);
}

TEST_F(PalContextTest, MakeCurrentBeforeCreateFails) {
    EXPECT_EQ(context_->makeCurrent(), Result::NotInitialized);
}

TEST_F(PalContextTest, MakeCurrentOnSoftwareContextFails) {
    ASSERT_EQ(context_->createSoftware(640, 480, PixelFormat::RGBA8888), Result::Success);
    EXPECT_EQ(context_->makeCurrent(), Result::InvalidOperation);
}

TEST_F(PalContextTest, SwapBuffersNoOp) {
    ASSERT_EQ(context_->createOpenGL(3, 3, true), Result::Success);
    context_->swapBuffers();  // Should not crash
}

TEST_F(PalContextTest, GetProcAddressReturnsNull) {
    ASSERT_EQ(context_->createOpenGL(3, 3, true), Result::Success);
    // Headless has no real GL
    EXPECT_EQ(context_->getProcAddress("glCreateProgram"), nullptr);
}

// ═══════════════════════════════════════════════════════════════════════════
// Type Query Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalContextTest, GetTypeBeforeCreate) {
    EXPECT_EQ(context_->getType(), ContextType::None);
}

TEST_F(PalContextTest, ToStringContextType) {
    EXPECT_STREQ(toString(ContextType::None), "None");
    EXPECT_STREQ(toString(ContextType::Software), "Software");
    EXPECT_STREQ(toString(ContextType::OpenGL), "OpenGL");
    EXPECT_STREQ(toString(ContextType::Vulkan), "Vulkan");
    EXPECT_STREQ(toString(ContextType::GPU), "GPU");
}

} // namespace
} // namespace pal
