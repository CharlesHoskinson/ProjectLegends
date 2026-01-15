// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors

#include <gtest/gtest.h>
#include "pal/platform.h"

namespace pal {
namespace {

class PalPlatformTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Ensure clean state before each test
        Platform::shutdown();
    }

    void TearDown() override {
        Platform::shutdown();
    }
};

// ═══════════════════════════════════════════════════════════════════════════
// Initialization Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalPlatformTest, InitializeHeadlessSucceeds) {
    Result result = Platform::initialize(Backend::Headless);
    EXPECT_EQ(result, Result::Success);
    EXPECT_TRUE(Platform::isInitialized());
    EXPECT_EQ(Platform::getActiveBackend(), Backend::Headless);
}

TEST_F(PalPlatformTest, DoubleInitializeFails) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    EXPECT_EQ(Platform::initialize(Backend::Headless), Result::AlreadyInitialized);
}

TEST_F(PalPlatformTest, ShutdownAfterInitialize) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    Platform::shutdown();
    EXPECT_FALSE(Platform::isInitialized());
    EXPECT_EQ(Platform::getActiveBackend(), Backend::None);
}

TEST_F(PalPlatformTest, ShutdownWithoutInitializeIsSafe) {
    EXPECT_FALSE(Platform::isInitialized());
    Platform::shutdown();  // Should not crash
    EXPECT_FALSE(Platform::isInitialized());
}

TEST_F(PalPlatformTest, InitializeNoneFails) {
    Result result = Platform::initialize(Backend::None);
    EXPECT_EQ(result, Result::InvalidParameter);
    EXPECT_FALSE(Platform::isInitialized());
}

TEST_F(PalPlatformTest, GetBackendName) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    EXPECT_STREQ(Platform::getBackendName(), "Headless");
}

TEST_F(PalPlatformTest, ToStringBackend) {
    EXPECT_STREQ(toString(Backend::None), "None");
    EXPECT_STREQ(toString(Backend::SDL2), "SDL2");
    EXPECT_STREQ(toString(Backend::SDL3), "SDL3");
    EXPECT_STREQ(toString(Backend::Headless), "Headless");
}

// ═══════════════════════════════════════════════════════════════════════════
// Factory Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalPlatformTest, CreateWindowBeforeInitializeReturnsNull) {
    auto window = Platform::createWindow();
    EXPECT_EQ(window, nullptr);
}

TEST_F(PalPlatformTest, CreateWindowAfterInitialize) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    auto window = Platform::createWindow();
    EXPECT_NE(window, nullptr);
}

TEST_F(PalPlatformTest, CreateContextBeforeInitializeReturnsNull) {
    // Need a dummy window - but should fail anyway
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    auto window = Platform::createWindow();
    ASSERT_NE(window, nullptr);
    Platform::shutdown();

    auto context = Platform::createContext(*window);
    EXPECT_EQ(context, nullptr);
}

TEST_F(PalPlatformTest, CreateContextAfterInitialize) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    auto window = Platform::createWindow();
    ASSERT_NE(window, nullptr);
    auto context = Platform::createContext(*window);
    EXPECT_NE(context, nullptr);
}

TEST_F(PalPlatformTest, CreateAudioSinkBeforeInitializeReturnsNull) {
    auto sink = Platform::createAudioSink();
    EXPECT_EQ(sink, nullptr);
}

TEST_F(PalPlatformTest, CreateAudioSinkAfterInitialize) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    auto sink = Platform::createAudioSink();
    EXPECT_NE(sink, nullptr);
}

TEST_F(PalPlatformTest, CreateHostClockBeforeInitializeReturnsNull) {
    auto clock = Platform::createHostClock();
    EXPECT_EQ(clock, nullptr);
}

TEST_F(PalPlatformTest, CreateHostClockAfterInitialize) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    auto clock = Platform::createHostClock();
    EXPECT_NE(clock, nullptr);
}

TEST_F(PalPlatformTest, CreateInputSourceBeforeInitializeReturnsNull) {
    auto input = Platform::createInputSource();
    EXPECT_EQ(input, nullptr);
}

TEST_F(PalPlatformTest, CreateInputSourceAfterInitialize) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    auto input = Platform::createInputSource();
    EXPECT_NE(input, nullptr);
}

TEST_F(PalPlatformTest, CreateAllServicesSucceeds) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);

    auto window = Platform::createWindow();
    ASSERT_NE(window, nullptr);

    auto context = Platform::createContext(*window);
    ASSERT_NE(context, nullptr);

    auto sink = Platform::createAudioSink();
    ASSERT_NE(sink, nullptr);

    auto clock = Platform::createHostClock();
    ASSERT_NE(clock, nullptr);

    auto input = Platform::createInputSource();
    ASSERT_NE(input, nullptr);
}

TEST_F(PalPlatformTest, ReinitializeAfterShutdown) {
    ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    Platform::shutdown();
    EXPECT_FALSE(Platform::isInitialized());

    EXPECT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    EXPECT_TRUE(Platform::isInitialized());
}

} // namespace
} // namespace pal
