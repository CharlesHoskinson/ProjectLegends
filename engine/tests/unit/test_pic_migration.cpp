/**
 * @file test_pic_migration.cpp
 * @brief Sprint 2: PIC Migration Tests
 *
 * Tests for PIC ticker handlers and full controller register state
 * in DOSBoxContext.
 *
 * Original test IDs (Phase 5):
 * - TEST-P05-U01 through TEST-P05-I02: Ticker infrastructure
 *
 * Sprint 2 Completion tests:
 * - Controller register defaults and modification
 * - IRQ raise/lower through controller
 * - IMR/ISR register modification
 * - enable_slave_pic flag behavior
 * - Controller isolation between instances
 * - Hash changes on register modification
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ===============================================================================
// Test Helpers
// ===============================================================================

namespace {

// Global counters for ticker tests
int g_ticker_call_count = 0;
int g_ticker2_call_count = 0;

void test_ticker() {
    g_ticker_call_count++;
}

void test_ticker2() {
    g_ticker2_call_count++;
}

void reset_ticker_counts() {
    g_ticker_call_count = 0;
    g_ticker2_call_count = 0;
}

}  // namespace

// ===============================================================================
// Unit Tests
// ===============================================================================

/**
 * TEST-P05-U01: Empty Ticker List Default
 * Verify new context has null ticker list.
 */
TEST(PicMigration, EmptyTickerListDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.pic.ticker_list, nullptr);
}

/**
 * TEST-P05-U02: Add Single Ticker
 * Verify ticker can be added to context.
 */
TEST(PicMigration, AddSingleTicker) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.pic.add_ticker(test_ticker);

    EXPECT_NE(ctx.pic.ticker_list, nullptr);
    EXPECT_EQ(ctx.pic.ticker_list->handler, test_ticker);

    ctx.pic.shutdown_tickers();
}

/**
 * TEST-P05-U03: Execute Ticker Handlers
 * Verify all registered handlers are called.
 */
TEST(PicMigration, ExecuteHandlers) {
    DOSBoxContext ctx(ContextConfig::minimal());
    reset_ticker_counts();

    ctx.pic.add_ticker(test_ticker);
    ctx.pic.add_ticker(test_ticker2);

    ctx.pic.execute_tickers();
    EXPECT_EQ(g_ticker_call_count, 1);
    EXPECT_EQ(g_ticker2_call_count, 1);

    ctx.pic.execute_tickers();
    EXPECT_EQ(g_ticker_call_count, 2);
    EXPECT_EQ(g_ticker2_call_count, 2);

    ctx.pic.shutdown_tickers();
}

/**
 * TEST-P05-U04: Remove Ticker Handler
 * Verify handler can be removed and stops being called.
 */
TEST(PicMigration, RemoveHandler) {
    DOSBoxContext ctx(ContextConfig::minimal());
    reset_ticker_counts();

    ctx.pic.add_ticker(test_ticker);
    ctx.pic.add_ticker(test_ticker2);

    ctx.pic.execute_tickers();
    EXPECT_EQ(g_ticker_call_count, 1);
    EXPECT_EQ(g_ticker2_call_count, 1);

    // Remove first ticker
    ctx.pic.remove_ticker(test_ticker);

    ctx.pic.execute_tickers();
    EXPECT_EQ(g_ticker_call_count, 1);  // Not incremented
    EXPECT_EQ(g_ticker2_call_count, 2); // Still called

    ctx.pic.shutdown_tickers();
}

/**
 * TEST-P05-U05: Cleanup on Destroy
 * Verify all tickers are cleaned up properly.
 */
TEST(PicMigration, CleanupOnDestroy) {
    {
        DOSBoxContext ctx(ContextConfig::minimal());

        ctx.pic.add_ticker(test_ticker);
        ctx.pic.add_ticker(test_ticker);
        ctx.pic.add_ticker(test_ticker2);

        EXPECT_NE(ctx.pic.ticker_list, nullptr);

        ctx.pic.shutdown_tickers();

        EXPECT_EQ(ctx.pic.ticker_list, nullptr);
    }
    // No crash = cleanup succeeded
}

/**
 * TEST-P05-U06: Add Multiple Tickers
 * Verify multiple tickers form a proper linked list.
 */
TEST(PicMigration, AddMultipleTickers) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.pic.add_ticker(test_ticker);
    ctx.pic.add_ticker(test_ticker2);

    // List should be: test_ticker2 -> test_ticker -> nullptr
    ASSERT_NE(ctx.pic.ticker_list, nullptr);
    EXPECT_EQ(ctx.pic.ticker_list->handler, test_ticker2);  // Most recent first

    ASSERT_NE(ctx.pic.ticker_list->next, nullptr);
    EXPECT_EQ(ctx.pic.ticker_list->next->handler, test_ticker);

    EXPECT_EQ(ctx.pic.ticker_list->next->next, nullptr);

    ctx.pic.shutdown_tickers();
}

/**
 * TEST-P05-U07: Remove Non-Existent Handler
 * Verify removing non-existent handler is safe.
 */
TEST(PicMigration, RemoveNonExistent) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.pic.add_ticker(test_ticker);

    // Remove handler that wasn't added
    ctx.pic.remove_ticker(test_ticker2);  // Should be no-op

    // Original handler should still be there
    EXPECT_NE(ctx.pic.ticker_list, nullptr);
    EXPECT_EQ(ctx.pic.ticker_list->handler, test_ticker);

    ctx.pic.shutdown_tickers();
}

// ===============================================================================
// Integration Tests
// ===============================================================================

/**
 * TEST-P05-I01: Context Initializes With PIC
 * Verify context can be initialized and PIC state is valid.
 */
TEST(PicIntegration, ContextInitializesWithPic) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    // PIC state should be valid
    EXPECT_EQ(ctx.pic.ticker_list, nullptr);  // No handlers registered yet
    EXPECT_EQ(ctx.pic.ticks, 0);

    ctx.shutdown();
}

/**
 * TEST-P05-I02: Ticker Isolation Between Instances
 * Verify tickers don't leak between context instances.
 */
TEST(PicIntegration, TickerIsolation) {
    reset_ticker_counts();

    // First instance - add ticker
    {
        DOSBoxContext ctx1(ContextConfig::defaults());
        ctx1.initialize();

        ctx1.pic.add_ticker(test_ticker);
        ctx1.pic.execute_tickers();
        EXPECT_EQ(g_ticker_call_count, 1);

        ctx1.pic.shutdown_tickers();
        ctx1.shutdown();
    }

    // Second instance - should have empty ticker list
    {
        DOSBoxContext ctx2(ContextConfig::defaults());
        ctx2.initialize();

        EXPECT_EQ(ctx2.pic.ticker_list, nullptr);

        // Execute should be no-op
        ctx2.pic.execute_tickers();
        EXPECT_EQ(g_ticker_call_count, 1);  // Not incremented

        ctx2.shutdown();
    }
}

/**
 * TEST-P05-I03: Ticks Counter Works
 * Verify PIC ticks counter can be incremented.
 */
TEST(PicIntegration, TicksCounter) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    uint64_t initial_ticks = ctx.pic.ticks;

    // Manually increment (normally done by TIMER_AddTick)
    ctx.pic.ticks++;
    ctx.pic.ticks++;
    ctx.pic.ticks++;

    EXPECT_EQ(ctx.pic.ticks, initial_ticks + 3);

    ctx.shutdown();
}

// ===============================================================================
// Controller Register Tests (Sprint 2 Completion)
// ===============================================================================

/**
 * TEST-CTRL-U01: Controller Register Defaults
 * Verify controllers have correct initial register values.
 */
TEST(PicController, RegisterDefaults) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Master controller
    EXPECT_EQ(ctx.pic.controllers[0].controller_index, 0u);
    EXPECT_EQ(ctx.pic.controllers[0].imr, 0xFFu);
    EXPECT_EQ(ctx.pic.controllers[0].isr, 0u);
    EXPECT_EQ(ctx.pic.controllers[0].irr, 0u);
    EXPECT_EQ(ctx.pic.controllers[0].active_irq, 8u);
    EXPECT_FALSE(ctx.pic.controllers[0].auto_eoi);
    EXPECT_FALSE(ctx.pic.controllers[0].special);

    // Slave controller
    EXPECT_EQ(ctx.pic.controllers[1].controller_index, 1u);
    EXPECT_EQ(ctx.pic.controllers[1].imr, 0xFFu);
    EXPECT_EQ(ctx.pic.controllers[1].isr, 0u);
}

/**
 * TEST-CTRL-U02: IMR Register Modification
 * Verify IMR can be set and read.
 */
TEST(PicController, ImrModification) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.pic.controllers[0].imr = 0xFE;  // Unmask IRQ0
    ctx.pic.controllers[0].imrr = ~ctx.pic.controllers[0].imr;

    EXPECT_EQ(ctx.pic.controllers[0].imr, 0xFEu);
    EXPECT_EQ(ctx.pic.controllers[0].imrr, 0x01u);

    // Backward-compat accessor
    EXPECT_EQ(ctx.pic.master_imr(), 0xFEu);
}

/**
 * TEST-CTRL-U03: ISR Register Modification
 * Verify ISR can be set and read.
 */
TEST(PicController, IsrModification) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.pic.controllers[0].isr = 0x01;  // IRQ0 in service
    ctx.pic.controllers[0].isrr = ~ctx.pic.controllers[0].isr;

    EXPECT_EQ(ctx.pic.controllers[0].isr, 0x01u);
    EXPECT_EQ(ctx.pic.controllers[0].isrr, 0xFEu);
    EXPECT_EQ(ctx.pic.master_isr(), 0x01u);
}

/**
 * TEST-CTRL-U04: Auto-EOI Mode
 * Verify auto_eoi can be toggled.
 */
TEST(PicController, AutoEoiMode) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_FALSE(ctx.pic.controllers[0].auto_eoi);

    ctx.pic.controllers[0].auto_eoi = true;
    EXPECT_TRUE(ctx.pic.controllers[0].auto_eoi);
    EXPECT_TRUE(ctx.pic.auto_eoi());
}

/**
 * TEST-CTRL-U05: Controller Reset
 * Verify controller reset restores defaults.
 */
TEST(PicController, ControllerReset) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.pic.controllers[0].imr = 0x00;
    ctx.pic.controllers[0].isr = 0xFF;
    ctx.pic.controllers[0].auto_eoi = true;
    ctx.pic.controllers[0].vector_base = 0x70;

    ctx.pic.controllers[0].reset();

    EXPECT_EQ(ctx.pic.controllers[0].imr, 0xFFu);
    EXPECT_EQ(ctx.pic.controllers[0].isr, 0u);
    EXPECT_FALSE(ctx.pic.controllers[0].auto_eoi);
    EXPECT_EQ(ctx.pic.controllers[0].vector_base, 0u);
}

/**
 * TEST-CTRL-U06: IRR Register (Request Register)
 * Verify IRR can be modified to simulate IRQ requests.
 */
TEST(PicController, IrrModification) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Simulate IRQ0 request
    ctx.pic.controllers[0].irr = 0x01;
    EXPECT_EQ(ctx.pic.controllers[0].irr, 0x01u);

    // Simulate IRQ0 + IRQ1 request
    ctx.pic.controllers[0].irr = 0x03;
    EXPECT_EQ(ctx.pic.controllers[0].irr, 0x03u);
}

/**
 * TEST-CTRL-U07: Enable Slave PIC Flag
 * Verify enable_slave_pic flag defaults and can be modified.
 */
TEST(PicController, EnableSlavePicFlag) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_TRUE(ctx.pic.enable_slave_pic);

    ctx.pic.enable_slave_pic = false;
    EXPECT_FALSE(ctx.pic.enable_slave_pic);
}

/**
 * TEST-CTRL-U08: PicState Reset Resets Controllers
 * Verify PicState::reset() resets both controllers.
 */
TEST(PicController, PicStateResetResetsControllers) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.pic.controllers[0].imr = 0x00;
    ctx.pic.controllers[1].isr = 0xFF;
    ctx.pic.enable_slave_pic = false;

    ctx.pic.reset();

    EXPECT_EQ(ctx.pic.controllers[0].imr, 0xFFu);
    EXPECT_EQ(ctx.pic.controllers[1].isr, 0u);
    EXPECT_TRUE(ctx.pic.enable_slave_pic);
    EXPECT_EQ(ctx.pic.controllers[0].controller_index, 0u);
    EXPECT_EQ(ctx.pic.controllers[1].controller_index, 1u);
}

/**
 * TEST-CTRL-I01: Controller Isolation Between Instances
 * Verify PIC controller state is isolated per instance.
 */
TEST(PicController, ControllerIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    ctx1.pic.controllers[0].imr = 0x00;
    ctx1.pic.controllers[0].auto_eoi = true;
    ctx1.pic.enable_slave_pic = false;

    ctx2.pic.controllers[0].imr = 0xFE;
    ctx2.pic.controllers[1].vector_base = 0x70;

    // Verify isolation
    EXPECT_EQ(ctx1.pic.controllers[0].imr, 0x00u);
    EXPECT_TRUE(ctx1.pic.controllers[0].auto_eoi);
    EXPECT_FALSE(ctx1.pic.enable_slave_pic);

    EXPECT_EQ(ctx2.pic.controllers[0].imr, 0xFEu);
    EXPECT_FALSE(ctx2.pic.controllers[0].auto_eoi);
    EXPECT_TRUE(ctx2.pic.enable_slave_pic);
    EXPECT_EQ(ctx2.pic.controllers[1].vector_base, 0x70u);
}

/**
 * TEST-CTRL-I02: Hash Changes on Controller Register Modification
 * Verify modifying controller registers changes the state hash.
 */
TEST(PicController, HashChangesOnRegisterModification) {
    DOSBoxContext ctx(ContextConfig::minimal());
    ctx.initialize();

    auto hash1 = get_state_hash(&ctx, HashMode::Fast);
    ASSERT_TRUE(hash1.has_value());

    ctx.pic.controllers[0].imr = 0x00;

    auto hash2 = get_state_hash(&ctx, HashMode::Fast);
    ASSERT_TRUE(hash2.has_value());

    EXPECT_NE(hash1.value(), hash2.value());

    ctx.shutdown();
}
