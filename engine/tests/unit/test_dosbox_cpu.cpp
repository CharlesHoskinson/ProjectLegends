/**
 * @file test_dosbox_cpu.cpp
 * @brief Unit tests for DOSBox CPU state migration (PR #11).
 *
 * Tests:
 * - CpuState struct fields
 * - CPU state reset
 * - State hash includes CPU state
 * - Determinism: same CPU state = same hash
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// CpuState Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(CpuStateTest, DefaultValues) {
    CpuState cpu;

    // Cycle counters
    EXPECT_EQ(cpu.cycles, 0);
    EXPECT_EQ(cpu.cycle_left, 3000);
    EXPECT_EQ(cpu.cycle_max, 3000);
    EXPECT_EQ(cpu.cycle_old_max, 3000);
    EXPECT_EQ(cpu.cycle_percent_used, 100);
    EXPECT_EQ(cpu.cycle_limit, -1);
    EXPECT_EQ(cpu.cycle_up, 0);
    EXPECT_EQ(cpu.cycle_down, 0);
    EXPECT_EQ(cpu.cycles_set, 3000);
    EXPECT_EQ(cpu.io_delay_removed, 0);

    // Auto-adjustment flags
    EXPECT_FALSE(cpu.cycle_auto_adjust);
    EXPECT_FALSE(cpu.skip_cycle_auto_adjust);

    // NMI state
    EXPECT_TRUE(cpu.nmi_gate);
    EXPECT_FALSE(cpu.nmi_active);
    EXPECT_FALSE(cpu.nmi_pending);

    // Flags
    EXPECT_EQ(cpu.extflags_toggle, 0u);
    EXPECT_FALSE(cpu.halted);

    // Limit (for config)
    EXPECT_EQ(cpu.cycle_limit, 3000);
}

TEST(CpuStateTest, Reset) {
    CpuState cpu;

    // Set some non-default values
    cpu.cycles = 1000000;
    cpu.cycle_left = 500;
    cpu.cycle_max = 10000;
    cpu.cycle_old_max = 8000;
    cpu.cycle_percent_used = 50;
    cpu.cycle_limit = 5000;
    cpu.cycle_up = 100;
    cpu.cycle_down = 50;
    cpu.cycles_set = 7000;
    cpu.io_delay_removed = 123;
    cpu.cycle_auto_adjust = true;
    cpu.skip_cycle_auto_adjust = true;
    cpu.nmi_gate = false;
    cpu.nmi_active = true;
    cpu.nmi_pending = true;
    cpu.extflags_toggle = 0xDEADBEEF;
    cpu.halted = true;

    // Reset
    cpu.reset();

    // Verify all fields reset to defaults
    EXPECT_EQ(cpu.cycles, 0);
    EXPECT_EQ(cpu.cycle_left, 3000);
    EXPECT_EQ(cpu.cycle_max, 3000);
    EXPECT_EQ(cpu.cycle_old_max, 3000);
    EXPECT_EQ(cpu.cycle_percent_used, 100);
    EXPECT_EQ(cpu.cycle_limit, -1);
    EXPECT_EQ(cpu.cycle_up, 0);
    EXPECT_EQ(cpu.cycle_down, 0);
    EXPECT_EQ(cpu.cycles_set, 3000);
    EXPECT_EQ(cpu.io_delay_removed, 0);
    EXPECT_FALSE(cpu.cycle_auto_adjust);
    EXPECT_FALSE(cpu.skip_cycle_auto_adjust);
    EXPECT_TRUE(cpu.nmi_gate);
    EXPECT_FALSE(cpu.nmi_active);
    EXPECT_FALSE(cpu.nmi_pending);
    EXPECT_EQ(cpu.extflags_toggle, 0u);
    EXPECT_FALSE(cpu.halted);
}

TEST(CpuStateTest, HashInto) {
    CpuState cpu1;
    CpuState cpu2;

    cpu1.cycles = 5000;
    cpu1.cycle_left = 1000;
    cpu1.halted = true;

    cpu2.cycles = 5000;
    cpu2.cycle_left = 1000;
    cpu2.halted = true;

    // Same CPU state should produce same hash
    HashBuilder builder1;
    cpu1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    cpu2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);

    // Different CPU state should produce different hash
    cpu2.cycles = 6000;

    HashBuilder builder3;
    cpu2.hash_into(builder3);
    auto hash3 = builder3.finalize();

    EXPECT_NE(hash1, hash3);
}

TEST(CpuStateTest, HashIncludesAllFields) {
    CpuState base;
    base.cycles = 1000;
    base.cycle_left = 500;

    HashBuilder base_builder;
    base.hash_into(base_builder);
    auto base_hash = base_builder.finalize();

    // Test that each field affects the hash
    auto test_field_affects_hash = [&base, &base_hash](auto modifier) {
        CpuState modified = base;
        modifier(modified);

        HashBuilder builder;
        modified.hash_into(builder);
        auto hash = builder.finalize();

        EXPECT_NE(base_hash, hash);
    };

    // Test cycle counters
    test_field_affects_hash([](CpuState& c) { c.cycles++; });
    test_field_affects_hash([](CpuState& c) { c.cycle_left++; });
    test_field_affects_hash([](CpuState& c) { c.cycle_max++; });
    test_field_affects_hash([](CpuState& c) { c.cycle_old_max++; });
    test_field_affects_hash([](CpuState& c) { c.cycle_percent_used++; });
    test_field_affects_hash([](CpuState& c) { c.cycle_limit++; });
    test_field_affects_hash([](CpuState& c) { c.cycle_up++; });
    test_field_affects_hash([](CpuState& c) { c.cycle_down++; });
    test_field_affects_hash([](CpuState& c) { c.cycles_set++; });
    test_field_affects_hash([](CpuState& c) { c.io_delay_removed++; });

    // Test flags
    test_field_affects_hash([](CpuState& c) { c.cycle_auto_adjust = !c.cycle_auto_adjust; });
    test_field_affects_hash([](CpuState& c) { c.skip_cycle_auto_adjust = !c.skip_cycle_auto_adjust; });

    // Test NMI state
    test_field_affects_hash([](CpuState& c) { c.nmi_gate = !c.nmi_gate; });
    test_field_affects_hash([](CpuState& c) { c.nmi_active = !c.nmi_active; });
    test_field_affects_hash([](CpuState& c) { c.nmi_pending = !c.nmi_pending; });

    // Test other flags
    test_field_affects_hash([](CpuState& c) { c.extflags_toggle++; });
    test_field_affects_hash([](CpuState& c) { c.halted = !c.halted; });
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash with CPU Context Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(CpuHashTest, HashChangesWithCpuState) {
    // Create and initialize context
    DOSBoxContext ctx;
    ctx.initialize();

    // Set context as current
    ContextGuard guard(ctx);

    // Get initial hash
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify CPU state
    ctx.cpu_state.cycles += 1000;
    ctx.cpu_state.halted = true;

    // Get new hash
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    // Hashes should be different
    EXPECT_NE(hash1, hash2);
}

TEST(CpuHashTest, SameCpuStateProducesSameHash) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;

    ctx1.initialize();
    ctx2.initialize();

    // Set same CPU values
    ctx1.cpu_state.cycles = 5000;
    ctx1.cpu_state.cycle_left = 1000;
    ctx1.cpu_state.halted = true;

    ctx2.cpu_state.cycles = 5000;
    ctx2.cpu_state.cycle_left = 1000;
    ctx2.cpu_state.halted = true;

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

TEST(CpuHashTest, NMIStateAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Toggle NMI state
    ctx.cpu_state.nmi_active = true;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

TEST(CpuHashTest, CycleAutoAdjustAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Enable cycle auto-adjust
    ctx.cpu_state.cycle_auto_adjust = true;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context CPU Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextCpuTest, StepUpdatesCpuCycles) {
    DOSBoxContext ctx;
    ctx.initialize();

    EXPECT_EQ(ctx.cpu_state.cycles, 0);

    // Step 10ms
    auto result = ctx.step(10);
    ASSERT_TRUE(result.has_value());

    EXPECT_GT(ctx.cpu_state.cycles, 0);
}

TEST(ContextCpuTest, ResetClearsCpuState) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Execute some steps
    ctx.step(100);
    EXPECT_GT(ctx.cpu_state.cycles, 0);

    // Modify other CPU state
    ctx.cpu_state.halted = true;
    ctx.cpu_state.nmi_active = true;

    // Reset
    ctx.reset();

    // CPU state should be reset
    EXPECT_EQ(ctx.cpu_state.cycles, 0);
    EXPECT_FALSE(ctx.cpu_state.halted);
    EXPECT_FALSE(ctx.cpu_state.nmi_active);
    EXPECT_TRUE(ctx.cpu_state.nmi_gate);  // Default is true
}

TEST(ContextCpuTest, CyclesAccumulateAcrossSteps) {
    DOSBoxContext ctx;
    ctx.initialize();

    ctx.step(10);
    int64_t cycles1 = ctx.cpu_state.cycles;

    ctx.step(10);
    int64_t cycles2 = ctx.cpu_state.cycles;

    // Should accumulate
    EXPECT_GT(cycles2, cycles1);
}

TEST(ContextCpuTest, ConfigAppliesCyclesLimit) {
    ContextConfig config;
    config.cpu_cycles = 5000;

    DOSBoxContext ctx(config);
    ctx.initialize();

    // Config should apply cycle_limit
    EXPECT_EQ(ctx.cpu_state.cycle_limit, 5000);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Combined Timing + CPU Hash Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(CombinedHashTest, BothTimingAndCpuAffectHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify only timing
    ctx.timing.total_cycles += 1000;
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();
    EXPECT_NE(hash1, hash2);

    // Reset timing, modify only CPU
    ctx.timing.total_cycles -= 1000;
    ctx.cpu_state.cycles += 1000;
    auto result3 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result3.has_value());
    auto hash3 = result3.value();
    EXPECT_NE(hash1, hash3);
    EXPECT_NE(hash2, hash3);
}

TEST(CombinedHashTest, DeterministicAfterStep) {
    ContextConfig config;
    config.cpu_cycles = 3000;

    // Create two contexts with same config
    DOSBoxContext ctx1(config);
    DOSBoxContext ctx2(config);

    ctx1.initialize();
    ctx2.initialize();

    // Step both by same amount
    ctx1.step(100);
    ctx2.step(100);

    // Get hashes
    set_current_context(&ctx1);
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());

    set_current_context(&ctx2);
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());

    // Hashes should be identical (deterministic)
    EXPECT_EQ(result1.value(), result2.value());

    // Clean up
    set_current_context(nullptr);
}
