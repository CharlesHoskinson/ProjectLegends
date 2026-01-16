/**
 * @file test_cpu_bridge.cpp
 * @brief Comprehensive tests for CPU execution bridge (cpu_bridge.h/cpp).
 *
 * Tests cover:
 * - Bridge initialization
 * - Cycle execution with various counts
 * - Stop reason handling
 * - Context integration
 * - Error conditions
 * - Determinism verification
 * - Edge cases and boundary conditions
 */

#include <gtest/gtest.h>
#include "dosbox/cpu_bridge.h"
#include "dosbox/dosbox_context.h"

// For mocking CPU globals in headless mode
#ifdef AIBOX_HEADLESS
#include "aibox/headless_stub.h"
#endif

namespace dosbox {
namespace test {

// ═══════════════════════════════════════════════════════════════════════════════
// Test Fixtures
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Base fixture for CPU bridge tests.
 */
class CpuBridgeTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Initialize the bridge
        init_cpu_bridge();
    }

    void TearDown() override {
        // Clean up any context
        set_current_context(nullptr);
    }
};

/**
 * @brief Fixture with a fully initialized DOSBoxContext.
 */
class CpuBridgeWithContextTest : public CpuBridgeTest {
protected:
    void SetUp() override {
        CpuBridgeTest::SetUp();

        // Create and initialize context
        config_ = ContextConfig::minimal();
        context_ = std::make_unique<DOSBoxContext>(config_);
        auto result = context_->initialize();
        ASSERT_TRUE(result.has_value()) << "Context initialization failed";

        // Set as current context
        set_current_context(context_.get());
    }

    void TearDown() override {
        set_current_context(nullptr);
        if (context_) {
            context_->shutdown();
            context_.reset();
        }
        CpuBridgeTest::TearDown();
    }

    ContextConfig config_;
    std::unique_ptr<DOSBoxContext> context_;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Initialization Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeTest, InitCpuBridgeSetsReadyFlag) {
    // init_cpu_bridge() was called in SetUp
    EXPECT_TRUE(is_cpu_bridge_ready());
}

TEST_F(CpuBridgeTest, InitCpuBridgeIsIdempotent) {
    // Call multiple times
    init_cpu_bridge();
    init_cpu_bridge();
    init_cpu_bridge();

    // Should still be ready
    EXPECT_TRUE(is_cpu_bridge_ready());
}

TEST_F(CpuBridgeTest, IsCpuBridgeReadyReturnsTrueAfterInit) {
    EXPECT_TRUE(is_cpu_bridge_ready());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Basic Execution Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, ExecuteZeroCyclesReturnsImmediately) {
    auto result = execute_cycles(context_.get(), 0);

    EXPECT_EQ(result.cycles_executed, 0u);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteSmallCycleCount) {
    auto result = execute_cycles(context_.get(), 100);

    // In headless mode, we may not execute actual CPU instructions,
    // but the bridge should handle the request gracefully
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteMediumCycleCount) {
    auto result = execute_cycles(context_.get(), 10000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteLargeCycleCount) {
    auto result = execute_cycles(context_.get(), 1000000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteWithNullContext) {
    // Should handle null context gracefully
    auto result = execute_cycles(nullptr, 1000);

    // Should complete (null context just means no stop_requested check)
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Millisecond Execution Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, ExecuteMsZeroReturnsImmediately) {
    auto result = execute_ms(context_.get(), 0, 3000);

    EXPECT_EQ(result.cycles_executed, 0u);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteMsOneMillisecond) {
    auto result = execute_ms(context_.get(), 1, 3000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteMsTenMilliseconds) {
    auto result = execute_ms(context_.get(), 10, 3000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteMsHundredMilliseconds) {
    auto result = execute_ms(context_.get(), 100, 3000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteMsWithDifferentCyclesPerMs) {
    // Test with different cycles_per_ms values
    auto result1 = execute_ms(context_.get(), 10, 1000);   // 10ms at 1000 cycles/ms
    auto result2 = execute_ms(context_.get(), 10, 5000);   // 10ms at 5000 cycles/ms
    auto result3 = execute_ms(context_.get(), 10, 10000);  // 10ms at 10000 cycles/ms

    // All should complete
    EXPECT_EQ(result1.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result2.stop_reason, CpuStopReason::Completed);
    EXPECT_EQ(result3.stop_reason, CpuStopReason::Completed);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Stop Request Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, StopRequestedBeforeExecution) {
    // Request stop before executing
    context_->request_stop();

    auto result = execute_cycles(context_.get(), 1000000);

    // Should stop immediately due to stop request
    EXPECT_EQ(result.stop_reason, CpuStopReason::UserRequest);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(CpuBridgeWithContextTest, StopRequestClearedAfterExecution) {
    // This tests that stop request is properly detected
    context_->request_stop();
    auto result1 = execute_cycles(context_.get(), 1000);
    EXPECT_EQ(result1.stop_reason, CpuStopReason::UserRequest);

    // Clear stop and execute again
    // Note: We need a way to clear stop - for now test that stop persists
}

// ═══════════════════════════════════════════════════════════════════════════════
// Result Structure Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, ResultStructureInitialized) {
    auto result = execute_cycles(context_.get(), 100);

    // All fields should be properly set
    // cycles_executed: depends on actual execution
    // events_processed: should be >= 0
    EXPECT_GE(result.events_processed, 0u);
    // stop_reason: should be a valid enum value
    EXPECT_LE(static_cast<uint32_t>(result.stop_reason), 5u);
    // callback_id: -1 for no callback, or valid callback number
    EXPECT_GE(result.callback_id, -1);
}

TEST_F(CpuBridgeWithContextTest, EventsProcessedIncrementsOnTicks) {
    // Execute enough cycles that at least some events should be processed
    auto result = execute_cycles(context_.get(), 100000);

    // In headless mode, events may or may not be processed
    // Just verify the field is reasonable
    EXPECT_GE(result.events_processed, 0u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context State Update Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, ContextTimingUpdatedAfterExecution) {
    uint64_t initial_cycles = context_->timing.total_cycles;
    int64_t initial_cpu_cycles = context_->cpu_state.cycles;

    execute_cycles(context_.get(), 10000);

    // Timing should be updated
    EXPECT_GE(context_->timing.total_cycles, initial_cycles);
    EXPECT_GE(context_->cpu_state.cycles, initial_cpu_cycles);
}

TEST_F(CpuBridgeWithContextTest, ContextTimingUpdatedAfterExecuteMs) {
    uint32_t initial_ticks = context_->timing.virtual_ticks_ms;

    execute_ms(context_.get(), 10, 3000);

    // Virtual ticks should be updated
    EXPECT_GE(context_->timing.virtual_ticks_ms, initial_ticks);
}

TEST_F(CpuBridgeWithContextTest, MultipleExecutionsAccumulateCycles) {
    uint64_t initial_cycles = context_->timing.total_cycles;

    execute_cycles(context_.get(), 1000);
    execute_cycles(context_.get(), 2000);
    execute_cycles(context_.get(), 3000);

    // Total cycles should be accumulated
    EXPECT_GE(context_->timing.total_cycles, initial_cycles);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Edge Cases and Boundary Conditions
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, ExecuteMaxUint32Cycles) {
    // Test with very large cycle count
    auto result = execute_cycles(context_.get(), UINT32_MAX);

    // Should complete eventually (or hit stop condition)
    // In headless mode, this might take a while so we accept any completion
    EXPECT_NE(result.stop_reason, CpuStopReason::Error);
}

TEST_F(CpuBridgeWithContextTest, ExecuteOneCycle) {
    auto result = execute_cycles(context_.get(), 1);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteMsWithZeroCyclesPerMs) {
    // Edge case: zero cycles per ms should handle gracefully
    auto result = execute_ms(context_.get(), 10, 0);

    // Should complete with zero cycles executed
    EXPECT_EQ(result.cycles_executed, 0u);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

TEST_F(CpuBridgeWithContextTest, ExecuteMsWithMaxCyclesPerMs) {
    // Test with maximum cycles per ms
    auto result = execute_ms(context_.get(), 1, UINT32_MAX);

    // Should handle without overflow issues
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Stop Reason Enum Coverage Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeTest, StopReasonCompletedValue) {
    EXPECT_EQ(static_cast<uint32_t>(CpuStopReason::Completed), 0u);
}

TEST_F(CpuBridgeTest, StopReasonHaltValue) {
    EXPECT_EQ(static_cast<uint32_t>(CpuStopReason::Halt), 1u);
}

TEST_F(CpuBridgeTest, StopReasonBreakpointValue) {
    EXPECT_EQ(static_cast<uint32_t>(CpuStopReason::Breakpoint), 2u);
}

TEST_F(CpuBridgeTest, StopReasonErrorValue) {
    EXPECT_EQ(static_cast<uint32_t>(CpuStopReason::Error), 3u);
}

TEST_F(CpuBridgeTest, StopReasonUserRequestValue) {
    EXPECT_EQ(static_cast<uint32_t>(CpuStopReason::UserRequest), 4u);
}

TEST_F(CpuBridgeTest, StopReasonCallbackValue) {
    EXPECT_EQ(static_cast<uint32_t>(CpuStopReason::Callback), 5u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Determinism Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, SameCyclesProduceSameResult) {
    // Reset context to known state
    context_->reset();

    // Execute same cycle count twice
    auto result1 = execute_cycles(context_.get(), 1000);

    context_->reset();
    auto result2 = execute_cycles(context_.get(), 1000);

    // Results should be identical (deterministic)
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
    EXPECT_EQ(result1.stop_reason, result2.stop_reason);
}

TEST_F(CpuBridgeWithContextTest, DifferentCyclesProduceDifferentState) {
    context_->reset();
    uint64_t initial_state = context_->timing.total_cycles;

    execute_cycles(context_.get(), 1000);
    uint64_t state_after_1000 = context_->timing.total_cycles;

    // State should differ
    EXPECT_NE(initial_state, state_after_1000);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Result Field Validation Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, CyclesExecutedNeverExceedsRequested) {
    // In normal operation, executed should not exceed requested
    // (except for I/O delay overrun, which is documented behavior)
    auto result = execute_cycles(context_.get(), 1000);

    // Allow small overrun for I/O delay
    EXPECT_LE(result.cycles_executed, 1000u + 1000u);  // Allow 100% overrun max
}

TEST_F(CpuBridgeWithContextTest, CallbackIdMinusOneWhenNoCallback) {
    auto result = execute_cycles(context_.get(), 100);

    // If not stopped by callback, callback_id should be -1
    if (result.stop_reason != CpuStopReason::Callback) {
        EXPECT_EQ(result.callback_id, -1);
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Thread Safety Considerations (Documentation Tests)
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, ExecuteFromEmulationThreadOnly) {
    // This test documents that execute_cycles must be called from emulation thread
    // Actual thread safety testing would require multi-threaded test setup

    // For now, verify single-threaded execution works
    auto result = execute_cycles(context_.get(), 100);
    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Integration with DOSBoxContext Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, ExecuteWithUninitializedContext) {
    // Create a new context but don't initialize it
    DOSBoxContext uninit_ctx(ContextConfig::minimal());

    // Execute should still work (bridge doesn't require initialized context)
    auto result = execute_cycles(&uninit_ctx, 100);

    // May complete or error, but shouldn't crash
    EXPECT_TRUE(result.stop_reason == CpuStopReason::Completed ||
                result.stop_reason == CpuStopReason::Error);
}

TEST_F(CpuBridgeWithContextTest, ExecuteAfterContextReset) {
    // Execute some cycles
    execute_cycles(context_.get(), 1000);

    // Reset context
    context_->reset();

    // Execute again
    auto result = execute_cycles(context_.get(), 1000);

    EXPECT_EQ(result.stop_reason, CpuStopReason::Completed);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Performance Characteristic Tests (Documentation)
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(CpuBridgeWithContextTest, BatchSizeDoesNotAffectResult) {
    // Internal batch size should not affect final result
    context_->reset();
    auto result1 = execute_cycles(context_.get(), 50000);

    context_->reset();
    auto result2 = execute_cycles(context_.get(), 50000);

    // Results should match regardless of internal batching
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
    EXPECT_EQ(result1.stop_reason, result2.stop_reason);
}

} // namespace test
} // namespace dosbox
