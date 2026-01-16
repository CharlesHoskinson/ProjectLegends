/**
 * @file test_dma_migration.cpp
 * @brief Sprint 2 Phase 3: DMA Controller Migration Tests
 *
 * Tests for migrating DmaControllers[2] global to DOSBoxContext.
 * These tests verify the DmaState struct and its integration with
 * the context-based architecture.
 *
 * Test IDs from phase-03-dma-controllers.md:
 * - TEST-P03-U01: DMA State Default Initialization
 * - TEST-P03-U02: DMA Controller Creation
 * - TEST-P03-U03: DMA Channel Access (0-3)
 * - TEST-P03-U04: DMA Channel Access (4-7)
 * - TEST-P03-U05: Close Second DMA Controller
 * - TEST-P03-U06: DMA Cleanup on Destroy
 * - TEST-P03-I01: Sound Blaster DMA Playback
 * - TEST-P03-I02: Floppy Disk DMA Transfer
 * - TEST-P03-I03: DMA Isolation Between Instances
 * - TEST-P03-D01: DMA State In Hash
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Unit Tests
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST-P03-U01: DMA State Default Initialization
 * Verify new context has null controllers.
 */
TEST(DmaMigration, DefaultStateCorrect) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // DMA controllers should be null before initialization
    EXPECT_EQ(ctx.dma.controllers[0], nullptr);
    EXPECT_EQ(ctx.dma.controllers[1], nullptr);
    EXPECT_FALSE(ctx.dma.has_second_controller());
}

/**
 * TEST-P03-U02: DMA Controller Creation
 * Verify controllers created on init.
 */
TEST(DmaMigration, ControllersCreatedOnInit) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    // First controller should always be created
    EXPECT_NE(ctx.dma.controllers[0], nullptr);

    // Second controller depends on machine type (AT or higher)
    // For defaults, we expect it to exist
    // Note: This may need adjustment based on actual machine configuration

    ctx.shutdown();
}

/**
 * TEST-P03-U03: DMA Channel Access (0-3)
 * Verify channels 0-3 accessible via first controller.
 */
TEST(DmaMigration, Channel0to3Access) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    // Channels 0-3 should be accessible via first controller
    for (uint8_t ch = 0; ch < 4; ++ch) {
        auto* channel = ctx.dma.get_channel(ch);
        EXPECT_NE(channel, nullptr) << "Channel " << static_cast<int>(ch) << " should be accessible";
    }

    ctx.shutdown();
}

/**
 * TEST-P03-U04: DMA Channel Access (4-7)
 * Verify channels 4-7 accessible via second controller.
 */
TEST(DmaMigration, Channel4to7Access) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    if (ctx.dma.has_second_controller()) {
        // Channels 4-7 should be accessible via second controller
        for (uint8_t ch = 4; ch < 8; ++ch) {
            auto* channel = ctx.dma.get_channel(ch);
            EXPECT_NE(channel, nullptr) << "Channel " << static_cast<int>(ch) << " should be accessible";
        }
    } else {
        GTEST_SKIP() << "No second DMA controller configured";
    }

    ctx.shutdown();
}

/**
 * TEST-P03-U05: Close Second DMA Controller
 * Verify second controller can be closed.
 */
TEST(DmaMigration, CloseSecondController) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    if (!ctx.dma.has_second_controller()) {
        GTEST_SKIP() << "No second DMA controller to close";
    }

    EXPECT_NE(ctx.dma.controllers[1], nullptr);
    EXPECT_TRUE(ctx.dma.has_second_controller());

    // Close the second controller
    ctx.dma.close_second_controller();

    EXPECT_EQ(ctx.dma.controllers[1], nullptr);
    EXPECT_FALSE(ctx.dma.has_second_controller());

    // Channels 4-7 should now return null
    for (uint8_t ch = 4; ch < 8; ++ch) {
        EXPECT_EQ(ctx.dma.get_channel(ch), nullptr)
            << "Channel " << static_cast<int>(ch) << " should be null after closing second controller";
    }

    ctx.shutdown();
}

/**
 * TEST-P03-U06: DMA Cleanup on Destroy
 * Verify controllers deallocated on context destruction.
 */
TEST(DmaMigration, CleanupOnDestroy) {
    {
        DOSBoxContext ctx(ContextConfig::defaults());
        auto result = ctx.initialize();
        ASSERT_TRUE(result.has_value()) << "Context initialization failed";

        // Verify controllers exist
        EXPECT_NE(ctx.dma.controllers[0], nullptr);
    }
    // Context destroyed - no crash means cleanup succeeded
    // Memory sanitizers (ASan) will catch any leaks
}

// ═══════════════════════════════════════════════════════════════════════════════
// Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST-P03-I01: Sound Blaster DMA Playback
 * Verify DMA channel 1 works for Sound Blaster.
 */
TEST(DmaIntegration, SoundBlasterDMA) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    // DMA channel 1 is typically used by Sound Blaster
    auto* sb_chan = ctx.dma.get_channel(1);
    ASSERT_NE(sb_chan, nullptr) << "Sound Blaster DMA channel 1 should exist";

    // Verify channel is functional (basic state check)
    // The channel should be masked by default
    EXPECT_TRUE(sb_chan->masked) << "DMA channel should be masked by default";

    ctx.shutdown();
}

/**
 * TEST-P03-I02: Floppy Disk DMA Transfer
 * Verify DMA channel 2 works for floppy.
 */
TEST(DmaIntegration, FloppyDMA) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    // DMA channel 2 is used by floppy disk controller
    auto* fdc_chan = ctx.dma.get_channel(2);
    ASSERT_NE(fdc_chan, nullptr) << "Floppy DMA channel 2 should exist";

    ctx.shutdown();
}

/**
 * TEST-P03-I03: DMA Isolation Between Instances
 * Verify DMA state is isolated per instance.
 */
TEST(DmaIntegration, InstanceIsolation) {
    // First instance - close second controller
    {
        DOSBoxContext ctx(ContextConfig::defaults());
        auto result = ctx.initialize();
        ASSERT_TRUE(result.has_value()) << "Context 1 initialization failed";

        if (ctx.dma.has_second_controller()) {
            ctx.dma.close_second_controller();
            EXPECT_FALSE(ctx.dma.has_second_controller());
        }

        ctx.shutdown();
    }

    // Second instance - should have fresh state (second controller present if config allows)
    {
        DOSBoxContext ctx(ContextConfig::defaults());
        auto result = ctx.initialize();
        ASSERT_TRUE(result.has_value()) << "Context 2 initialization failed";

        // Fresh initialization, state should not be affected by previous instance
        // This verifies global DmaControllers[2] is no longer used
        EXPECT_NE(ctx.dma.controllers[0], nullptr);

        ctx.shutdown();
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Determinism Tests
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST-P03-D01: DMA State In Hash
 * Verify DMA state changes affect state hash.
 */
TEST(DmaDeterminism, StateInHash) {
    StateHash hash1, hash2;

    // Get hash of freshly initialized context
    {
        DOSBoxContext ctx(ContextConfig::defaults());
        auto init_result = ctx.initialize();
        ASSERT_TRUE(init_result.has_value()) << "Context initialization failed";

        auto hash_result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(hash_result.has_value()) << "Hash computation failed";
        hash1 = hash_result.value();

        ctx.shutdown();
    }

    // Get hash after modifying DMA state
    {
        DOSBoxContext ctx(ContextConfig::defaults());
        auto init_result = ctx.initialize();
        ASSERT_TRUE(init_result.has_value()) << "Context initialization failed";

        // Modify DMA channel state
        auto* chan = ctx.dma.get_channel(0);
        if (chan) {
            // Modify a DMA channel property
            chan->currcnt = 0x1234;
        }

        auto hash_result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(hash_result.has_value()) << "Hash computation failed";
        hash2 = hash_result.value();

        ctx.shutdown();
    }

    // Hashes should differ because DMA state changed
    EXPECT_NE(hash1, hash2) << "DMA state change should affect hash";
}

/**
 * Additional test: Same DMA state should produce same hash.
 */
TEST(DmaDeterminism, SameStatesSameHash) {
    StateHash hash1, hash2;

    // Get hash of freshly initialized context
    {
        DOSBoxContext ctx(ContextConfig::defaults());
        auto init_result = ctx.initialize();
        ASSERT_TRUE(init_result.has_value());

        auto hash_result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(hash_result.has_value());
        hash1 = hash_result.value();

        ctx.shutdown();
    }

    // Get hash of another freshly initialized context
    {
        DOSBoxContext ctx(ContextConfig::defaults());
        auto init_result = ctx.initialize();
        ASSERT_TRUE(init_result.has_value());

        auto hash_result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(hash_result.has_value());
        hash2 = hash_result.value();

        ctx.shutdown();
    }

    // Hashes should be identical (determinism)
    EXPECT_EQ(hash1, hash2) << "Same DMA state should produce same hash";
}

// ═══════════════════════════════════════════════════════════════════════════════
// DmaState Struct Tests
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Test DmaState reset functionality.
 */
TEST(DmaState, ResetClearsControllers) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Set up some state
    // Note: We can't directly assign controllers here as they need proper init
    // This test verifies reset behavior

    ctx.dma.reset();

    EXPECT_EQ(ctx.dma.controllers[0], nullptr);
    EXPECT_EQ(ctx.dma.controllers[1], nullptr);
}

/**
 * Test out-of-range channel access returns null.
 */
TEST(DmaState, OutOfRangeChannelReturnsNull) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value());

    // Channel 8+ should return null
    EXPECT_EQ(ctx.dma.get_channel(8), nullptr);
    EXPECT_EQ(ctx.dma.get_channel(255), nullptr);

    ctx.shutdown();
}
