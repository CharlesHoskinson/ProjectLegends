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
    ContextConfig config_ = ContextConfig::minimal();
    std::unique_ptr<DOSBoxContext> ctx_;

    void SetUp() override {
        init_cpu_bridge();
        ctx_ = std::make_unique<DOSBoxContext>(config_);
        auto result = ctx_->initialize();
        ASSERT_TRUE(result.has_value()) << "Context init failed";
        set_current_context(ctx_.get());
    }

    void TearDown() override {
        set_current_context(nullptr);
        if (ctx_) {
            ctx_->shutdown();
            ctx_.reset();
        }
    }
};

TEST_F(CpuBridgeTest, IsReadyAfterInit) {
    EXPECT_TRUE(is_cpu_bridge_ready());
}

TEST_F(CpuBridgeTest, ExecuteCyclesUpdatesContext) {
    ctx_->timing.total_cycles = 0;
    auto result = execute_cycles(ctx_.get(), 3000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 3000u);
    EXPECT_EQ(ctx_->timing.total_cycles, 3000u);
}

TEST_F(CpuBridgeTest, ExecuteCyclesAccumulates) {
    ctx_->timing.total_cycles = 0;
    execute_cycles(ctx_.get(), 1000);
    execute_cycles(ctx_.get(), 2000);

    EXPECT_EQ(ctx_->timing.total_cycles, 3000u);
}

TEST_F(CpuBridgeTest, NullContextReturnsError) {
    auto result = execute_cycles(nullptr, 1000);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Error);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(CpuBridgeTest, StopRequestedHaltsExecution) {
    ctx_->request_stop();
    auto result = execute_cycles(ctx_.get(), 100000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::UserRequest);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(CpuBridgeTest, ExecuteMsConvertsToycles) {
    ctx_->timing.total_cycles = 0;
    auto result = execute_ms(ctx_.get(), 10, 3000); // 10ms * 3000 = 30000 cycles

    EXPECT_EQ(result.cycles_executed, 30000u);
    EXPECT_EQ(ctx_->timing.total_cycles, 30000u);
}

TEST_F(CpuBridgeTest, ExecuteMsUpdatesVirtualTicks) {
    ctx_->timing.virtual_ticks_ms = 0;
    execute_ms(ctx_.get(), 10, 3000);

    EXPECT_EQ(ctx_->timing.virtual_ticks_ms, 10u);
}

TEST_F(CpuBridgeTest, ZeroCyclesCompletesImmediately) {
    auto result = execute_cycles(ctx_.get(), 0);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(CpuBridgeTest, CallbackIdIsNegativeOneByDefault) {
    auto result = execute_cycles(ctx_.get(), 100);
    EXPECT_EQ(result.callback_id, -1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Contract / postcondition tests (Phase C.3)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CpuBridgeTest, PostconditionCompletedMeansAllCyclesConsumed) {
    ctx_->timing.total_cycles = 0;
    auto result = execute_cycles(ctx_.get(), 7777);

    // Completed means all requested cycles were consumed (clamped to budget)
    ASSERT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 7777u);
}

TEST_F(CpuBridgeTest, PostconditionStopRequestConsumesFewer) {
    ctx_->timing.total_cycles = 0;
    ctx_->request_stop();
    auto result = execute_cycles(ctx_.get(), 10000);

    ASSERT_EQ(result.stop_reason, CpuStopReason::UserRequest);
    EXPECT_LT(result.cycles_executed, 10000u);
}

TEST_F(CpuBridgeTest, ExecuteMsRequiresPositiveCyclesPerMs) {
    // cycles_per_ms > 0 is a gsl_Expects precondition.
    // Valid calls must provide a positive rate.
    ctx_->timing.total_cycles = 0;
    auto result = execute_ms(ctx_.get(), 5, 3000);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result.cycles_executed, 15000u);
}
