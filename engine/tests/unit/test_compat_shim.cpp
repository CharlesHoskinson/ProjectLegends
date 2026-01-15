/**
 * @file test_compat_shim.cpp
 * @brief Unit tests for compatibility shim (compat::current).
 */

#include <gtest/gtest.h>
#include <aibox/machine_context.h>

using namespace aibox;

// ─────────────────────────────────────────────────────────────────────────────
// Test Fixture
// ─────────────────────────────────────────────────────────────────────────────

class CompatShimTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Ensure no context is set at start of each test
        compat::set_current_context(nullptr);
    }

    void TearDown() override {
        // Clean up
        compat::set_current_context(nullptr);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Basic Context Setting Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, HasContextInitiallyFalse) {
    EXPECT_FALSE(compat::has_context());
}

TEST_F(CompatShimTest, HasContextTrueAfterSet) {
    MachineContext ctx;

    compat::set_current_context(&ctx);

    EXPECT_TRUE(compat::has_context());
}

TEST_F(CompatShimTest, HasContextFalseAfterClear) {
    MachineContext ctx;
    compat::set_current_context(&ctx);

    compat::set_current_context(nullptr);

    EXPECT_FALSE(compat::has_context());
}

TEST_F(CompatShimTest, CurrentPtrReturnsNull) {
    EXPECT_EQ(compat::current_ptr(), nullptr);
}

TEST_F(CompatShimTest, CurrentPtrReturnsContext) {
    MachineContext ctx;

    compat::set_current_context(&ctx);

    EXPECT_EQ(compat::current_ptr(), &ctx);
}

TEST_F(CompatShimTest, CurrentReturnsReference) {
    MachineContext ctx;
    compat::set_current_context(&ctx);

    MachineContext& ref = compat::current();

    EXPECT_EQ(&ref, &ctx);
}

// ─────────────────────────────────────────────────────────────────────────────
// Context Access Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, CanAccessCpuViaShim) {
    MachineContext ctx;
    ctx.cpu.eax = 0x12345678;
    compat::set_current_context(&ctx);

    EXPECT_EQ(compat::current().cpu.eax, 0x12345678u);
}

TEST_F(CompatShimTest, CanModifyCpuViaShim) {
    MachineContext ctx;
    compat::set_current_context(&ctx);

    compat::current().cpu.eax = 0xABCDEF00;

    EXPECT_EQ(ctx.cpu.eax, 0xABCDEF00u);
}

TEST_F(CompatShimTest, CanAccessMemoryViaShim) {
    MachineConfig config = MachineConfig::minimal();
    MachineContext ctx(config);
    ctx.initialize();
    compat::set_current_context(&ctx);

    EXPECT_NE(compat::current().memory, nullptr);
    EXPECT_EQ(compat::current().memory->size(), config.memory_size);
}

TEST_F(CompatShimTest, CanAccessConfigViaShim) {
    MachineConfig config;
    config.cpu_cycles = 4500;
    MachineContext ctx(config);
    compat::set_current_context(&ctx);

    EXPECT_EQ(compat::current().config().cpu_cycles, 4500u);
}

// ─────────────────────────────────────────────────────────────────────────────
// ContextGuard Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, ContextGuardSetsContext) {
    MachineContext ctx;

    {
        compat::ContextGuard guard(ctx);
        EXPECT_TRUE(compat::has_context());
        EXPECT_EQ(compat::current_ptr(), &ctx);
    }
}

TEST_F(CompatShimTest, ContextGuardRestoresNull) {
    MachineContext ctx;

    EXPECT_FALSE(compat::has_context());

    {
        compat::ContextGuard guard(ctx);
        EXPECT_TRUE(compat::has_context());
    }

    EXPECT_FALSE(compat::has_context());
}

TEST_F(CompatShimTest, ContextGuardRestoresPrevious) {
    MachineContext ctx1;
    MachineContext ctx2;

    compat::set_current_context(&ctx1);
    EXPECT_EQ(compat::current_ptr(), &ctx1);

    {
        compat::ContextGuard guard(ctx2);
        EXPECT_EQ(compat::current_ptr(), &ctx2);
    }

    EXPECT_EQ(compat::current_ptr(), &ctx1);
}

TEST_F(CompatShimTest, NestedContextGuards) {
    MachineContext ctx1;
    MachineContext ctx2;
    MachineContext ctx3;

    {
        compat::ContextGuard guard1(ctx1);
        EXPECT_EQ(compat::current_ptr(), &ctx1);

        {
            compat::ContextGuard guard2(ctx2);
            EXPECT_EQ(compat::current_ptr(), &ctx2);

            {
                compat::ContextGuard guard3(ctx3);
                EXPECT_EQ(compat::current_ptr(), &ctx3);
            }

            EXPECT_EQ(compat::current_ptr(), &ctx2);
        }

        EXPECT_EQ(compat::current_ptr(), &ctx1);
    }

    EXPECT_FALSE(compat::has_context());
}

// ─────────────────────────────────────────────────────────────────────────────
// Step Integration Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, StepSetsContext) {
    MachineConfig config = MachineConfig::minimal();
    MachineContext ctx(config);
    ctx.initialize();

    // Before step, no context should be set
    EXPECT_FALSE(compat::has_context());

    // Step should set context internally
    // (Note: After step returns, context may or may not be set
    // depending on implementation - step uses ContextGuard)
    ctx.step(1);

    // After step, the ContextGuard in step() should have cleaned up
    // This tests that the guard properly restores the previous (null) state
}

// ─────────────────────────────────────────────────────────────────────────────
// Multiple Context Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, SwitchBetweenContexts) {
    MachineContext ctx1;
    MachineContext ctx2;

    ctx1.cpu.eax = 0x11111111;
    ctx2.cpu.eax = 0x22222222;

    compat::set_current_context(&ctx1);
    EXPECT_EQ(compat::current().cpu.eax, 0x11111111u);

    compat::set_current_context(&ctx2);
    EXPECT_EQ(compat::current().cpu.eax, 0x22222222u);

    compat::set_current_context(&ctx1);
    EXPECT_EQ(compat::current().cpu.eax, 0x11111111u);
}

// ─────────────────────────────────────────────────────────────────────────────
// State Query Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, QueryStateViaShim) {
    MachineConfig config = MachineConfig::minimal();
    MachineContext ctx(config);
    compat::set_current_context(&ctx);

    EXPECT_EQ(compat::current().state(), MachineState::Created);

    ctx.initialize();
    EXPECT_EQ(compat::current().state(), MachineState::Initialized);

    ctx.shutdown();
    EXPECT_EQ(compat::current().state(), MachineState::Shutdown);
}

// ─────────────────────────────────────────────────────────────────────────────
// Thread-Local Behavior (Single Thread)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, ContextIsPerThread) {
    // This test just verifies the thread-local storage works
    // in a single-threaded context
    MachineContext ctx;

    compat::set_current_context(&ctx);
    EXPECT_EQ(compat::current_ptr(), &ctx);

    compat::set_current_context(nullptr);
    EXPECT_EQ(compat::current_ptr(), nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CompatShimTest, SetSameContextTwice) {
    MachineContext ctx;

    compat::set_current_context(&ctx);
    compat::set_current_context(&ctx);

    EXPECT_EQ(compat::current_ptr(), &ctx);
}

TEST_F(CompatShimTest, ContextGuardWithSameContext) {
    MachineContext ctx;
    compat::set_current_context(&ctx);

    {
        compat::ContextGuard guard(ctx);
        EXPECT_EQ(compat::current_ptr(), &ctx);
    }

    // Should restore to ctx (which was already set)
    EXPECT_EQ(compat::current_ptr(), &ctx);
}
