/**
 * @file test_timing_integration.cpp
 * @brief Unit tests for platform timing integration (PR #17).
 *
 * Tests:
 * - Headless stub timing provider integration
 * - DOSBoxContext timing provider configuration
 * - Virtual timing through context
 * - Custom timing provider injection
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/platform/timing.h"
#include "dosbox/platform/headless.h"
#include "aibox/headless_stub.h"

using namespace dosbox;
using namespace dosbox::platform;

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Stub Timing Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessTimingTest, DefaultNoProvider) {
    // Clear any existing provider
    aibox::headless::SetTimingProvider(nullptr);

    EXPECT_FALSE(aibox::headless::HasTimingProvider());
    EXPECT_EQ(aibox::headless::GetTimingProvider(), nullptr);
}

TEST(HeadlessTimingTest, SetTimingProvider) {
    VirtualTiming timing;

    aibox::headless::SetTimingProvider(&timing);

    EXPECT_TRUE(aibox::headless::HasTimingProvider());
    EXPECT_EQ(aibox::headless::GetTimingProvider(), &timing);

    // Clean up
    aibox::headless::SetTimingProvider(nullptr);
}

TEST(HeadlessTimingTest, GetTicksUsesProvider) {
    VirtualTiming timing;

    // Advance timing
    timing.advance_time(500);

    // Set as provider
    aibox::headless::SetTimingProvider(&timing);

    // GetTicks should use provider
    EXPECT_EQ(aibox::headless::GetTicks(), 500u);

    // Advance more
    timing.advance_time(250);
    EXPECT_EQ(aibox::headless::GetTicks(), 750u);

    // Clean up
    aibox::headless::SetTimingProvider(nullptr);
}

TEST(HeadlessTimingTest, AdvanceTicksUsesProvider) {
    VirtualTiming timing;
    aibox::headless::SetTimingProvider(&timing);

    // AdvanceTicks should go through provider
    aibox::headless::AdvanceTicks(100);
    EXPECT_EQ(timing.get_ticks(), 100u);

    aibox::headless::AdvanceTicks(50);
    EXPECT_EQ(timing.get_ticks(), 150u);

    // Clean up
    aibox::headless::SetTimingProvider(nullptr);
}

TEST(HeadlessTimingTest, FallbackToInternalTicks) {
    // Reset internal ticks
    aibox::headless::ResetTicks();
    aibox::headless::SetTimingProvider(nullptr);

    // Should use internal ticks
    EXPECT_EQ(aibox::headless::GetTicks(), 0u);

    aibox::headless::AdvanceTicks(100);
    EXPECT_EQ(aibox::headless::GetTicks(), 100u);

    // Reset for other tests
    aibox::headless::ResetTicks();
}

// ═══════════════════════════════════════════════════════════════════════════════
// DOSBoxContext Timing Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextTimingTest, HasBuiltInVirtualTiming) {
    DOSBoxContext ctx;

    // Context has its own virtual timing
    auto& vt = ctx.virtual_timing();
    EXPECT_TRUE(vt.is_deterministic());
    EXPECT_EQ(vt.get_ticks(), 0u);
}

TEST(ContextTimingTest, DefaultNoCustomProvider) {
    DOSBoxContext ctx;

    EXPECT_EQ(ctx.get_timing_provider(), nullptr);
}

TEST(ContextTimingTest, SetCustomTimingProvider) {
    DOSBoxContext ctx;
    HostTiming host_timing;

    ctx.set_timing_provider(&host_timing);

    EXPECT_EQ(ctx.get_timing_provider(), &host_timing);
}

TEST(ContextTimingTest, CurrentContextUsesBuiltInTiming) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Clear any previous state
    aibox::headless::SetTimingProvider(nullptr);

    // Set as current context
    ContextGuard guard(ctx);

    // Should have wired up the built-in virtual timing
    EXPECT_TRUE(aibox::headless::HasTimingProvider());
    EXPECT_EQ(aibox::headless::GetTimingProvider(), &ctx.virtual_timing());
}

TEST(ContextTimingTest, CurrentContextUsesCustomProvider) {
    DOSBoxContext ctx;
    ctx.initialize();
    VirtualTiming custom_timing;

    // Set custom provider
    ctx.set_timing_provider(&custom_timing);

    // Set as current context
    ContextGuard guard(ctx);

    // Should use custom provider
    EXPECT_EQ(aibox::headless::GetTimingProvider(), &custom_timing);
}

TEST(ContextTimingTest, ContextSwitchingUpdatesProvider) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Advance ctx2's timing
    ctx2.virtual_timing().advance_time(1000);

    {
        ContextGuard guard1(ctx1);
        EXPECT_EQ(aibox::headless::GetTicks(), 0u);
    }

    {
        ContextGuard guard2(ctx2);
        EXPECT_EQ(aibox::headless::GetTicks(), 1000u);
    }

    // Back to ctx1
    {
        ContextGuard guard1(ctx1);
        EXPECT_EQ(aibox::headless::GetTicks(), 0u);
    }
}

TEST(ContextTimingTest, ClearCurrentContextClearsProvider) {
    DOSBoxContext ctx;
    ctx.initialize();

    set_current_context(&ctx);
    EXPECT_TRUE(aibox::headless::HasTimingProvider());

    set_current_context(nullptr);
    EXPECT_FALSE(aibox::headless::HasTimingProvider());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Backend Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessBackendTimingTest, BackendTimingIntegration) {
    auto backend = make_headless_backend();
    DOSBoxContext ctx;
    ctx.initialize();

    // Use headless backend timing with context
    ctx.set_timing_provider(&backend->timing);

    ContextGuard guard(ctx);

    // Timing should flow through backend
    EXPECT_EQ(aibox::headless::GetTicks(), 0u);

    backend->timing.advance_time(100);
    EXPECT_EQ(aibox::headless::GetTicks(), 100u);

    // AdvanceTicks should also work
    aibox::headless::AdvanceTicks(50);
    EXPECT_EQ(backend->timing.get_ticks(), 150u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Virtual Timing State Preservation Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(VirtualTimingStateTest, TimingPreservedAcrossContextSwitch) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Advance both contexts differently
    ctx1.virtual_timing().advance_time(100);
    ctx2.virtual_timing().advance_time(500);

    // Switch contexts
    {
        ContextGuard guard1(ctx1);
        aibox::headless::AdvanceTicks(50);
    }

    {
        ContextGuard guard2(ctx2);
        aibox::headless::AdvanceTicks(200);
    }

    // Verify state preserved
    EXPECT_EQ(ctx1.virtual_timing().get_ticks(), 150u);
    EXPECT_EQ(ctx2.virtual_timing().get_ticks(), 700u);
}

TEST(VirtualTimingStateTest, ResetDoesNotAffectOtherContext) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    ctx1.virtual_timing().advance_time(100);
    ctx2.virtual_timing().advance_time(200);

    // Reset ctx1
    ctx1.virtual_timing().reset();

    EXPECT_EQ(ctx1.virtual_timing().get_ticks(), 0u);
    EXPECT_EQ(ctx2.virtual_timing().get_ticks(), 200u);
}
