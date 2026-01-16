/**
 * @file test_pic_migration.cpp
 * @brief Sprint 2 Phase 5: PIC Ticker Migration Tests
 *
 * Tests for migrating PIC ticker handlers to DOSBoxContext.
 * These tests verify the ticker_list and its integration with
 * the context-based architecture.
 *
 * Test IDs from phase-05-pic-ticker.md:
 * - TEST-P05-U01: Empty Ticker List Default
 * - TEST-P05-U02: Add Single Ticker
 * - TEST-P05-U03: Execute Ticker Handlers
 * - TEST-P05-U04: Remove Ticker Handler
 * - TEST-P05-U05: Cleanup on Destroy
 * - TEST-P05-I01: Timer Interrupts Work
 * - TEST-P05-I02: Ticker Isolation Between Instances
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"

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
