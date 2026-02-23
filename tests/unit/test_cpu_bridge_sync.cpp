/**
 * @file test_cpu_bridge_sync.cpp
 * @brief Unit tests for CPU bridge execution and context sync.
 */

#include <gtest/gtest.h>
#include <dosbox/cpu_bridge.h>
#include <dosbox/dosbox_context.h>

using namespace dosbox;

class CpuBridgeTest : public ::testing::Test {
protected:
    DOSBoxContext ctx{};

    void SetUp() override {
        init_cpu_bridge();
    }
};

TEST_F(CpuBridgeTest, IsReadyAfterInit) {
    EXPECT_TRUE(is_cpu_bridge_ready());
}

TEST_F(CpuBridgeTest, ExecuteCyclesUpdatesContext) {
    ctx.timing.total_cycles = 0;
    auto result = execute_cycles(&ctx, 3000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 3000u);
    EXPECT_EQ(ctx.timing.total_cycles, 3000u);
}

TEST_F(CpuBridgeTest, ExecuteCyclesAccumulates) {
    ctx.timing.total_cycles = 0;
    execute_cycles(&ctx, 1000);
    execute_cycles(&ctx, 2000);

    EXPECT_EQ(ctx.timing.total_cycles, 3000u);
}

TEST_F(CpuBridgeTest, NullContextReturnsError) {
    auto result = execute_cycles(nullptr, 1000);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Error);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(CpuBridgeTest, StopRequestedHaltsExecution) {
    ctx.request_stop();
    auto result = execute_cycles(&ctx, 100000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::UserRequest);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(CpuBridgeTest, ExecuteMsConvertsToycles) {
    ctx.timing.total_cycles = 0;
    auto result = execute_ms(&ctx, 10, 3000); // 10ms * 3000 = 30000 cycles

    EXPECT_EQ(result.cycles_executed, 30000u);
    EXPECT_EQ(ctx.timing.total_cycles, 30000u);
}

TEST_F(CpuBridgeTest, ExecuteMsUpdatesVirtualTicks) {
    ctx.timing.virtual_ticks_ms = 0;
    execute_ms(&ctx, 10, 3000);

    EXPECT_EQ(ctx.timing.virtual_ticks_ms, 10u);
}

TEST_F(CpuBridgeTest, ZeroCyclesCompletesImmediately) {
    auto result = execute_cycles(&ctx, 0);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(CpuBridgeTest, CallbackIdIsNegativeOneByDefault) {
    auto result = execute_cycles(&ctx, 100);
    EXPECT_EQ(result.callback_id, -1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Contract / postcondition tests (Phase C.3)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CpuBridgeTest, PostconditionCompletedMeansAllCyclesConsumed) {
    ctx.timing.total_cycles = 0;
    auto result = execute_cycles(&ctx, 7777);

    // gsl_Ensures in execute_cycles guarantees this on Completed
    ASSERT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 7777u);
}

TEST_F(CpuBridgeTest, PostconditionStopRequestConsumesFewer) {
    ctx.timing.total_cycles = 0;
    ctx.request_stop();
    auto result = execute_cycles(&ctx, 10000);

    ASSERT_EQ(result.stop_reason, CpuStopReason::UserRequest);
    EXPECT_LT(result.cycles_executed, 10000u);
}

TEST_F(CpuBridgeTest, ExecuteMsRequiresPositiveCyclesPerMs) {
    // cycles_per_ms > 0 is a gsl_Expects precondition.
    // Valid calls must provide a positive rate.
    ctx.timing.total_cycles = 0;
    auto result = execute_ms(&ctx, 5, 3000);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 15000u);
}
