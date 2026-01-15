// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors

#include <gtest/gtest.h>
#include "pal/platform.h"
#include "pal/input_source.h"

namespace pal {
namespace {

class PalInputSourceTest : public ::testing::Test {
protected:
    void SetUp() override {
        Platform::shutdown();
        ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
        input_ = Platform::createInputSource();
        ASSERT_NE(input_, nullptr);
    }

    void TearDown() override {
        input_.reset();
        Platform::shutdown();
    }

    std::unique_ptr<IInputSource> input_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Lifecycle Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalInputSourceTest, InitializeSucceeds) {
    Result result = input_->initialize();
    EXPECT_EQ(result, Result::Success);
    EXPECT_TRUE(input_->isInitialized());
}

TEST_F(PalInputSourceTest, InitializeTwiceFails) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    EXPECT_EQ(input_->initialize(), Result::AlreadyInitialized);
}

TEST_F(PalInputSourceTest, ShutdownAfterInitialize) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    input_->shutdown();
    EXPECT_FALSE(input_->isInitialized());
}

TEST_F(PalInputSourceTest, ShutdownWithoutInitializeIsSafe) {
    EXPECT_FALSE(input_->isInitialized());
    input_->shutdown();  // Should not crash
    EXPECT_FALSE(input_->isInitialized());
}

TEST_F(PalInputSourceTest, ReinitializeAfterShutdown) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    input_->shutdown();
    EXPECT_EQ(input_->initialize(), Result::Success);
    EXPECT_TRUE(input_->isInitialized());
}

// ═══════════════════════════════════════════════════════════════════════════
// Polling Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalInputSourceTest, PollReturnsZeroWhenEmpty) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    InputEvent events[64];
    uint32_t count = input_->poll(events, 64);
    EXPECT_EQ(count, 0u);
}

TEST_F(PalInputSourceTest, PollWithNullBufferReturnsZero) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    uint32_t count = input_->poll(nullptr, 64);
    EXPECT_EQ(count, 0u);
}

TEST_F(PalInputSourceTest, PollWithZeroMaxReturnsZero) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    InputEvent events[64];
    uint32_t count = input_->poll(events, 0);
    EXPECT_EQ(count, 0u);
}

TEST_F(PalInputSourceTest, PollBeforeInitializeReturnsZero) {
    InputEvent events[64];
    uint32_t count = input_->poll(events, 64);
    EXPECT_EQ(count, 0u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Mouse Capture Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalInputSourceTest, InitiallyNotCaptured) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    EXPECT_FALSE(input_->isMouseCaptured());
}

TEST_F(PalInputSourceTest, SetMouseCaptureTrue) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    EXPECT_EQ(input_->setMouseCapture(true), Result::Success);
    EXPECT_TRUE(input_->isMouseCaptured());
}

TEST_F(PalInputSourceTest, SetMouseCaptureFalse) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    input_->setMouseCapture(true);
    EXPECT_EQ(input_->setMouseCapture(false), Result::Success);
    EXPECT_FALSE(input_->isMouseCaptured());
}

TEST_F(PalInputSourceTest, SetMouseCaptureBeforeInitializeFails) {
    EXPECT_EQ(input_->setMouseCapture(true), Result::NotInitialized);
}

// ═══════════════════════════════════════════════════════════════════════════
// Relative Mouse Mode Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalInputSourceTest, InitiallyNotRelative) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    EXPECT_FALSE(input_->isRelativeMouseMode());
}

TEST_F(PalInputSourceTest, SetRelativeMouseModeTrue) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    EXPECT_EQ(input_->setRelativeMouseMode(true), Result::Success);
    EXPECT_TRUE(input_->isRelativeMouseMode());
}

TEST_F(PalInputSourceTest, SetRelativeMouseModeFalse) {
    ASSERT_EQ(input_->initialize(), Result::Success);
    input_->setRelativeMouseMode(true);
    EXPECT_EQ(input_->setRelativeMouseMode(false), Result::Success);
    EXPECT_FALSE(input_->isRelativeMouseMode());
}

TEST_F(PalInputSourceTest, SetRelativeMouseBeforeInitializeFails) {
    EXPECT_EQ(input_->setRelativeMouseMode(true), Result::NotInitialized);
}

// ═══════════════════════════════════════════════════════════════════════════
// Input Event Type Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalInputSourceTest, InputEventDefaultsToNone) {
    InputEvent event;
    EXPECT_EQ(event.type, InputEventType::None);
    EXPECT_EQ(event.host_timestamp_us, 0u);
}

TEST_F(PalInputSourceTest, ToStringInputEventType) {
    EXPECT_STREQ(toString(InputEventType::None), "None");
    EXPECT_STREQ(toString(InputEventType::KeyDown), "KeyDown");
    EXPECT_STREQ(toString(InputEventType::KeyUp), "KeyUp");
    EXPECT_STREQ(toString(InputEventType::MouseMotion), "MouseMotion");
    EXPECT_STREQ(toString(InputEventType::MouseButtonDown), "MouseButtonDown");
    EXPECT_STREQ(toString(InputEventType::MouseButtonUp), "MouseButtonUp");
    EXPECT_STREQ(toString(InputEventType::MouseWheel), "MouseWheel");
    EXPECT_STREQ(toString(InputEventType::JoystickAxis), "JoystickAxis");
    EXPECT_STREQ(toString(InputEventType::JoystickButton), "JoystickButton");
    EXPECT_STREQ(toString(InputEventType::WindowClose), "WindowClose");
    EXPECT_STREQ(toString(InputEventType::WindowResize), "WindowResize");
    EXPECT_STREQ(toString(InputEventType::WindowFocus), "WindowFocus");
    EXPECT_STREQ(toString(InputEventType::WindowUnfocus), "WindowUnfocus");
}

// ═══════════════════════════════════════════════════════════════════════════
// Note: Headless injection tests would require accessing the concrete type
// These basic tests verify the interface contract
// ═══════════════════════════════════════════════════════════════════════════

} // namespace
} // namespace pal
