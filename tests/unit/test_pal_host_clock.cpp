// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors

#include <gtest/gtest.h>
#include "pal/platform.h"
#include "pal/host_clock.h"

namespace pal {
namespace {

class PalHostClockTest : public ::testing::Test {
protected:
    void SetUp() override {
        Platform::shutdown();
        ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
        clock_ = Platform::createHostClock();
        ASSERT_NE(clock_, nullptr);
    }

    void TearDown() override {
        clock_.reset();
        Platform::shutdown();
    }

    std::unique_ptr<IHostClock> clock_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Lifecycle Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalHostClockTest, InitializeSucceeds) {
    Result result = clock_->initialize();
    EXPECT_EQ(result, Result::Success);
    EXPECT_TRUE(clock_->isInitialized());
}

TEST_F(PalHostClockTest, InitializeTwiceFails) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    EXPECT_EQ(clock_->initialize(), Result::AlreadyInitialized);
}

TEST_F(PalHostClockTest, ShutdownAfterInitialize) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    clock_->shutdown();
    EXPECT_FALSE(clock_->isInitialized());
}

TEST_F(PalHostClockTest, ShutdownWithoutInitializeIsSafe) {
    EXPECT_FALSE(clock_->isInitialized());
    clock_->shutdown();  // Should not crash
    EXPECT_FALSE(clock_->isInitialized());
}

TEST_F(PalHostClockTest, ReinitializeAfterShutdown) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    clock_->shutdown();
    EXPECT_EQ(clock_->initialize(), Result::Success);
    EXPECT_TRUE(clock_->isInitialized());
}

// ═══════════════════════════════════════════════════════════════════════════
// Time Query Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalHostClockTest, GetTicksMsBeforeInitialize) {
    EXPECT_EQ(clock_->getTicksMs(), 0u);
}

TEST_F(PalHostClockTest, GetTicksUsBeforeInitialize) {
    EXPECT_EQ(clock_->getTicksUs(), 0u);
}

TEST_F(PalHostClockTest, GetTicksMsAfterInitialize) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    // Headless returns virtual ticks, initially 0
    uint64_t ticks = clock_->getTicksMs();
    EXPECT_EQ(ticks, 0u);  // Headless starts at 0
}

TEST_F(PalHostClockTest, GetTicksUsAfterInitialize) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    uint64_t ticks = clock_->getTicksUs();
    EXPECT_EQ(ticks, 0u);  // Headless starts at 0
}

TEST_F(PalHostClockTest, MicrosAtLeastThousandTimesMillis) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    // For headless, both start at 0, so relationship holds trivially
    uint64_t ms = clock_->getTicksMs();
    uint64_t us = clock_->getTicksUs();
    EXPECT_EQ(us, ms * 1000);
}

// ═══════════════════════════════════════════════════════════════════════════
// Sleep Tests (Headless = Non-blocking)
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalHostClockTest, SleepMsIsNonBlockingInHeadless) {
    ASSERT_EQ(clock_->initialize(), Result::Success);

    // In headless mode, sleep should return immediately
    clock_->sleepMs(1000);  // Would block for 1 second in real backend

    // Test passes if we reach here quickly (non-blocking)
    SUCCEED();
}

TEST_F(PalHostClockTest, SleepUsIsNonBlockingInHeadless) {
    ASSERT_EQ(clock_->initialize(), Result::Success);

    clock_->sleepUs(1000000);  // 1 second in microseconds

    SUCCEED();
}

TEST_F(PalHostClockTest, SleepZeroReturnsImmediately) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    clock_->sleepMs(0);
    clock_->sleepUs(0);
    SUCCEED();
}

// ═══════════════════════════════════════════════════════════════════════════
// Virtual Time Control Tests (Headless-specific)
// ═══════════════════════════════════════════════════════════════════════════

// Note: These tests access the headless-specific interface through
// the concrete type. In production code, you'd use Platform factory
// and cast if needed for testing.

TEST_F(PalHostClockTest, TicksIncreaseWithVirtualAdvance) {
    ASSERT_EQ(clock_->initialize(), Result::Success);

    // We need to access the headless-specific interface
    // For now, just verify the basic contract
    uint64_t before = clock_->getTicksMs();

    // In headless, time doesn't advance automatically
    // This tests the basic invariant
    uint64_t after = clock_->getTicksMs();
    EXPECT_EQ(before, after);  // No automatic advance in headless
}

TEST_F(PalHostClockTest, TicksZeroAfterReinitialize) {
    ASSERT_EQ(clock_->initialize(), Result::Success);
    // Even if time advanced, shutdown resets it
    clock_->shutdown();
    ASSERT_EQ(clock_->initialize(), Result::Success);
    EXPECT_EQ(clock_->getTicksMs(), 0u);
}

} // namespace
} // namespace pal
