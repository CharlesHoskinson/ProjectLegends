// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors

#include <gtest/gtest.h>
#include "pal/platform.h"
#include "pal/window.h"

namespace pal {
namespace {

class PalWindowTest : public ::testing::Test {
protected:
    void SetUp() override {
        Platform::shutdown();
        ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
        window_ = Platform::createWindow();
        ASSERT_NE(window_, nullptr);
    }

    void TearDown() override {
        window_.reset();
        Platform::shutdown();
    }

    std::unique_ptr<IWindow> window_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Lifecycle Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalWindowTest, CreateWithDefaultConfig) {
    WindowConfig config;
    Result result = window_->create(config);
    EXPECT_EQ(result, Result::Success);
    EXPECT_TRUE(window_->isCreated());
}

TEST_F(PalWindowTest, CreateWithCustomSize) {
    WindowConfig config;
    config.width = 1280;
    config.height = 720;
    ASSERT_EQ(window_->create(config), Result::Success);

    uint32_t w, h;
    window_->getSize(w, h);
    EXPECT_EQ(w, 1280u);
    EXPECT_EQ(h, 720u);
}

TEST_F(PalWindowTest, CreateWithZeroWidthFails) {
    WindowConfig config;
    config.width = 0;
    config.height = 480;
    EXPECT_EQ(window_->create(config), Result::InvalidParameter);
    EXPECT_FALSE(window_->isCreated());
}

TEST_F(PalWindowTest, CreateWithZeroHeightFails) {
    WindowConfig config;
    config.width = 640;
    config.height = 0;
    EXPECT_EQ(window_->create(config), Result::InvalidParameter);
    EXPECT_FALSE(window_->isCreated());
}

TEST_F(PalWindowTest, CreateTwiceFails) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->create(config), Result::AlreadyExists);
}

TEST_F(PalWindowTest, DestroyAfterCreate) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    window_->destroy();
    EXPECT_FALSE(window_->isCreated());
}

TEST_F(PalWindowTest, DestroyWithoutCreateIsSafe) {
    EXPECT_FALSE(window_->isCreated());
    window_->destroy();  // Should not crash
    EXPECT_FALSE(window_->isCreated());
}

TEST_F(PalWindowTest, RecreateAfterDestroy) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    window_->destroy();
    EXPECT_EQ(window_->create(config), Result::Success);
    EXPECT_TRUE(window_->isCreated());
}

// ═══════════════════════════════════════════════════════════════════════════
// Property Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalWindowTest, ResizeUpdatesSize) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);

    EXPECT_EQ(window_->resize(1024, 768), Result::Success);

    uint32_t w, h;
    window_->getSize(w, h);
    EXPECT_EQ(w, 1024u);
    EXPECT_EQ(h, 768u);
}

TEST_F(PalWindowTest, ResizeToZeroWidthFails) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->resize(0, 480), Result::InvalidParameter);
}

TEST_F(PalWindowTest, ResizeToZeroHeightFails) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->resize(640, 0), Result::InvalidParameter);
}

TEST_F(PalWindowTest, ResizeBeforeCreateFails) {
    EXPECT_EQ(window_->resize(800, 600), Result::NotInitialized);
}

TEST_F(PalWindowTest, SetTitleSucceeds) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->setTitle("New Title"), Result::Success);
}

TEST_F(PalWindowTest, SetTitleNullFails) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->setTitle(nullptr), Result::InvalidParameter);
}

TEST_F(PalWindowTest, SetTitleEmptySucceeds) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->setTitle(""), Result::Success);
}

TEST_F(PalWindowTest, SetTitleBeforeCreateFails) {
    EXPECT_EQ(window_->setTitle("Title"), Result::NotInitialized);
}

// ═══════════════════════════════════════════════════════════════════════════
// Fullscreen Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalWindowTest, SetFullscreenTrue) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->setFullscreen(true), Result::Success);
    EXPECT_TRUE(window_->isFullscreen());
}

TEST_F(PalWindowTest, SetFullscreenFalse) {
    WindowConfig config;
    config.fullscreen = true;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_TRUE(window_->isFullscreen());

    EXPECT_EQ(window_->setFullscreen(false), Result::Success);
    EXPECT_FALSE(window_->isFullscreen());
}

TEST_F(PalWindowTest, ToggleFullscreen) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_FALSE(window_->isFullscreen());

    EXPECT_EQ(window_->setFullscreen(true), Result::Success);
    EXPECT_TRUE(window_->isFullscreen());

    EXPECT_EQ(window_->setFullscreen(false), Result::Success);
    EXPECT_FALSE(window_->isFullscreen());
}

TEST_F(PalWindowTest, SetFullscreenBeforeCreateFails) {
    EXPECT_EQ(window_->setFullscreen(true), Result::NotInitialized);
}

TEST_F(PalWindowTest, CreateWithFullscreenTrue) {
    WindowConfig config;
    config.fullscreen = true;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_TRUE(window_->isFullscreen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Display Enumeration Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalWindowTest, GetDisplayCountReturnsAtLeastOne) {
    EXPECT_GE(window_->getDisplayCount(), 1u);
}

TEST_F(PalWindowTest, GetDisplayInfoValidIndex) {
    DisplayInfo info;
    EXPECT_EQ(window_->getDisplayInfo(0, info), Result::Success);
    EXPECT_GT(info.width, 0u);
    EXPECT_GT(info.height, 0u);
    EXPECT_GT(info.refresh_rate, 0.0f);
}

TEST_F(PalWindowTest, GetDisplayInfoInvalidIndex) {
    DisplayInfo info;
    uint32_t count = window_->getDisplayCount();
    EXPECT_EQ(window_->getDisplayInfo(count, info), Result::InvalidParameter);
}

// ═══════════════════════════════════════════════════════════════════════════
// Presentation Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalWindowTest, PresentSucceeds) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->present(), Result::Success);
}

TEST_F(PalWindowTest, PresentBeforeCreateFails) {
    EXPECT_EQ(window_->present(), Result::NotInitialized);
}

TEST_F(PalWindowTest, SetVsyncTrue) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->setVsync(true), Result::Success);
}

TEST_F(PalWindowTest, SetVsyncFalse) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_EQ(window_->setVsync(false), Result::Success);
}

// ═══════════════════════════════════════════════════════════════════════════
// Native Handle Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalWindowTest, GetNativeHandleBeforeCreateReturnsNull) {
    EXPECT_EQ(window_->getNativeHandle(), nullptr);
}

TEST_F(PalWindowTest, GetNativeHandleAfterCreate) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    EXPECT_NE(window_->getNativeHandle(), nullptr);
}

TEST_F(PalWindowTest, GetNativeHandleAfterDestroy) {
    WindowConfig config;
    ASSERT_EQ(window_->create(config), Result::Success);
    window_->destroy();
    EXPECT_EQ(window_->getNativeHandle(), nullptr);
}

} // namespace
} // namespace pal
