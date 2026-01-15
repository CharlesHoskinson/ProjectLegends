/**
 * @file test_dosbox_timing.cpp
 * @brief Unit tests for DOSBox timing state migration (PR #10).
 *
 * Tests:
 * - TimingState struct fields
 * - Timing state reset
 * - State hash includes timing
 * - Determinism: same timing = same hash
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// TimingState Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(TimingStateTest, DefaultValues) {
    TimingState timing;

    EXPECT_EQ(timing.total_cycles, 0u);
    EXPECT_EQ(timing.virtual_ticks_ms, 0u);
    EXPECT_EQ(timing.ticks_done, 0);
    EXPECT_EQ(timing.ticks_scheduled, 0u);
    EXPECT_EQ(timing.ticks_remain, 0u);
    EXPECT_EQ(timing.ticks_added, 0u);
    EXPECT_EQ(timing.ticks_last, 0u);
    EXPECT_EQ(timing.sdl_ticks_last, 0u);
    EXPECT_EQ(timing.sdl_ticks_next, 0u);
    EXPECT_FALSE(timing.locked);
}

TEST(TimingStateTest, Reset) {
    TimingState timing;

    // Set some values
    timing.total_cycles = 1000000;
    timing.virtual_ticks_ms = 500;
    timing.ticks_done = 100;
    timing.ticks_scheduled = 200;
    timing.ticks_remain = 50;
    timing.ticks_added = 25;
    timing.ticks_last = 12345;
    timing.sdl_ticks_last = 54321;
    timing.locked = true;

    // Reset
    timing.reset();

    // Verify all fields reset
    EXPECT_EQ(timing.total_cycles, 0u);
    EXPECT_EQ(timing.virtual_ticks_ms, 0u);
    EXPECT_EQ(timing.ticks_done, 0);
    EXPECT_EQ(timing.ticks_scheduled, 0u);
    EXPECT_EQ(timing.ticks_remain, 0u);
    EXPECT_EQ(timing.ticks_added, 0u);
    EXPECT_EQ(timing.ticks_last, 0u);
    EXPECT_EQ(timing.sdl_ticks_last, 0u);
    EXPECT_EQ(timing.sdl_ticks_next, 0u);
    EXPECT_FALSE(timing.locked);
}

TEST(TimingStateTest, HashInto) {
    TimingState timing1;
    TimingState timing2;

    timing1.total_cycles = 1000;
    timing1.virtual_ticks_ms = 100;

    timing2.total_cycles = 1000;
    timing2.virtual_ticks_ms = 100;

    // Same timing should produce same hash
    HashBuilder builder1;
    timing1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    timing2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);

    // Different timing should produce different hash
    timing2.total_cycles = 2000;

    HashBuilder builder3;
    timing2.hash_into(builder3);
    auto hash3 = builder3.finalize();

    EXPECT_NE(hash1, hash3);
}

TEST(TimingStateTest, HashExcludesWallClock) {
    TimingState timing1;
    TimingState timing2;

    // Same determinism-relevant state
    timing1.total_cycles = 1000;
    timing1.virtual_ticks_ms = 100;
    timing1.ticks_done = 50;

    timing2.total_cycles = 1000;
    timing2.virtual_ticks_ms = 100;
    timing2.ticks_done = 50;

    // Different wall-clock state (should NOT affect hash)
    timing1.sdl_ticks_last = 12345;
    timing1.sdl_ticks_next = 12345 + 1000;
    timing1.ticks_last = 54321;
    timing1.ticks_last_rt = 99999;
    timing1.ticks_last_rt_time = 123.456;

    timing2.sdl_ticks_last = 99999;
    timing2.sdl_ticks_next = 88888;
    timing2.ticks_last = 11111;
    timing2.ticks_last_rt = 22222;
    timing2.ticks_last_rt_time = 789.012;

    // Hashes should be the same (wall-clock excluded)
    HashBuilder builder1;
    timing1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    timing2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash with Context Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(TimingHashTest, HashChangesWithTiming) {
    // Create and initialize context
    DOSBoxContext ctx;
    ctx.initialize();

    // Set context as current
    ContextGuard guard(ctx);

    // Get initial hash
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify timing state
    ctx.timing.total_cycles += 1000;
    ctx.timing.virtual_ticks_ms += 10;

    // Get new hash
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    // Hashes should be different
    EXPECT_NE(hash1, hash2);
}

TEST(TimingHashTest, SameTimingProducesSameHash) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;

    ctx1.initialize();
    ctx2.initialize();

    // Set same timing values
    ctx1.timing.total_cycles = 5000;
    ctx1.timing.virtual_ticks_ms = 100;
    ctx1.timing.ticks_done = 50;

    ctx2.timing.total_cycles = 5000;
    ctx2.timing.virtual_ticks_ms = 100;
    ctx2.timing.ticks_done = 50;

    // Get hash with ctx1
    {
        ContextGuard guard(ctx1);
        auto result1 = get_state_hash(HashMode::Fast);
        ASSERT_TRUE(result1.has_value());

        // Get hash with ctx2
        set_current_context(&ctx2);
        auto result2 = get_state_hash(HashMode::Fast);
        ASSERT_TRUE(result2.has_value());

        // Should be same
        EXPECT_EQ(result1.value(), result2.value());
    }
}

TEST(TimingHashTest, FastAndFullModesDiffer) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto fast = get_state_hash(HashMode::Fast);
    auto full = get_state_hash(HashMode::Full);

    ASSERT_TRUE(fast.has_value());
    ASSERT_TRUE(full.has_value());

    // Fast and full should produce different hashes
    EXPECT_NE(fast.value(), full.value());
}

TEST(TimingHashTest, NoContextProducesPlaceholder) {
    // Ensure no context is set
    set_current_context(nullptr);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());

    // Without context, should still be deterministic
    EXPECT_EQ(result1.value(), result2.value());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context Timing Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextTimingTest, StepUpdatesTiming) {
    DOSBoxContext ctx;
    ctx.initialize();

    EXPECT_EQ(ctx.timing.total_cycles, 0u);
    EXPECT_EQ(ctx.timing.virtual_ticks_ms, 0u);

    // Step 10ms
    auto result = ctx.step(10);
    ASSERT_TRUE(result.has_value());

    EXPECT_GT(ctx.timing.total_cycles, 0u);
    EXPECT_EQ(ctx.timing.virtual_ticks_ms, 10u);
}

TEST(ContextTimingTest, ResetClearsTiming) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Execute some steps
    ctx.step(100);
    EXPECT_GT(ctx.timing.total_cycles, 0u);

    // Reset
    ctx.reset();

    // Timing should be cleared
    EXPECT_EQ(ctx.timing.total_cycles, 0u);
    EXPECT_EQ(ctx.timing.virtual_ticks_ms, 0u);
}

TEST(ContextTimingTest, TimingAccumulatesAcrossSteps) {
    DOSBoxContext ctx;
    ctx.initialize();

    ctx.step(10);
    uint64_t cycles1 = ctx.timing.total_cycles;
    uint32_t ticks1 = ctx.timing.virtual_ticks_ms;

    ctx.step(10);
    uint64_t cycles2 = ctx.timing.total_cycles;
    uint32_t ticks2 = ctx.timing.virtual_ticks_ms;

    // Should accumulate
    EXPECT_GT(cycles2, cycles1);
    EXPECT_EQ(ticks2, 20u);
}
