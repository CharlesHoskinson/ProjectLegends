/**
 * @file test_vga_migration.cpp
 * @brief Unit tests for VGA state in DOSBoxContext.
 *
 * Tests for VGA state members: vsync, assigned_lfb, cur_mode,
 * and full VGA hardware state (Sprint 2 Completion).
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ===============================================================================
// Unit Tests
// ===============================================================================

/**
 * TEST-P06-U01: VSync Default State
 * Verify new context has default vsync values.
 */
TEST(VgaMigration, VsyncDefaultState) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.vga.vsync.period, 0.0);
    EXPECT_FALSE(ctx.vga.vsync.manual);
    EXPECT_FALSE(ctx.vga.vsync.persistent);
    EXPECT_FALSE(ctx.vga.vsync.faithful);
}

/**
 * TEST-P06-U02: VSync State Modification
 * Verify vsync state can be modified.
 */
TEST(VgaMigration, VsyncModification) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    ctx.vga.vsync.manual = true;
    ctx.vga.vsync.period = 16.67;  // ~60Hz
    ctx.vga.vsync.persistent = true;
    ctx.vga.vsync.faithful = true;

    EXPECT_TRUE(ctx.vga.vsync.manual);
    EXPECT_NEAR(ctx.vga.vsync.period, 16.67, 0.01);
    EXPECT_TRUE(ctx.vga.vsync.persistent);
    EXPECT_TRUE(ctx.vga.vsync.faithful);

    ctx.shutdown();
}

/**
 * TEST-P06-U03: LFB Assignment
 * Verify assigned_lfb can be set and read.
 */
TEST(VgaMigration, LfbAssignment) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    EXPECT_EQ(ctx.vga.assigned_lfb, 0);

    ctx.vga.assigned_lfb = 0xE0000000;
    EXPECT_EQ(ctx.vga.assigned_lfb, 0xE0000000);

    ctx.vga.assigned_lfb = 0xA0000;
    EXPECT_EQ(ctx.vga.assigned_lfb, 0xA0000);

    ctx.shutdown();
}

/**
 * TEST-P06-U04: CurMode Default (nullptr)
 * Verify new context has nullptr cur_mode.
 */
TEST(VgaMigration, CurModeDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.vga.cur_mode, nullptr);
}

/**
 * TEST-P06-U05: CurMode Set/Get
 * Verify cur_mode pointer can be set and read.
 */
TEST(VgaMigration, CurModeSetGet) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    // cur_mode starts as nullptr
    EXPECT_EQ(ctx.vga.cur_mode, nullptr);

    // We can't easily test with real VideoModeBlock without including int10.h,
    // but we can test the pointer storage mechanism with a dummy address
    // (in real usage, this would point to ModeList_VGA entries)

    // For this test, we just verify the member exists and can be assigned
    // Real integration tests will use actual mode blocks
    struct VideoModeBlock* dummy = reinterpret_cast<struct VideoModeBlock*>(0x12345678);
    ctx.vga.cur_mode = dummy;
    EXPECT_EQ(ctx.vga.cur_mode, dummy);

    ctx.vga.cur_mode = nullptr;
    EXPECT_EQ(ctx.vga.cur_mode, nullptr);

    ctx.shutdown();
}

/**
 * TEST-P06-U06: VSync Reset
 * Verify vsync.reset() clears all values.
 */
TEST(VgaMigration, VsyncReset) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    // Set values
    ctx.vga.vsync.period = 16.67;
    ctx.vga.vsync.manual = true;
    ctx.vga.vsync.persistent = true;
    ctx.vga.vsync.faithful = true;

    // Reset
    ctx.vga.vsync.reset();

    // Verify defaults
    EXPECT_EQ(ctx.vga.vsync.period, 0.0);
    EXPECT_FALSE(ctx.vga.vsync.manual);
    EXPECT_FALSE(ctx.vga.vsync.persistent);
    EXPECT_FALSE(ctx.vga.vsync.faithful);

    ctx.shutdown();
}

/**
 * TEST-P06-U07: VgaState Reset Includes New Members
 * Verify VgaState::reset() resets vsync, assigned_lfb, cur_mode.
 */
TEST(VgaMigration, VgaStateResetIncludesNewMembers) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    // Set values
    ctx.vga.vsync.period = 16.67;
    ctx.vga.vsync.manual = true;
    ctx.vga.assigned_lfb = 0xE0000000;
    ctx.vga.cur_mode = reinterpret_cast<struct VideoModeBlock*>(0x12345678);

    // Reset entire VgaState
    ctx.vga.reset();

    // Verify all reset
    EXPECT_EQ(ctx.vga.vsync.period, 0.0);
    EXPECT_FALSE(ctx.vga.vsync.manual);
    EXPECT_EQ(ctx.vga.assigned_lfb, 0);
    EXPECT_EQ(ctx.vga.cur_mode, nullptr);

    ctx.shutdown();
}

// ===============================================================================
// Integration Tests
// ===============================================================================

/**
 * TEST-P06-I01: VGA State Isolation
 * Verify VGA state doesn't leak between context instances.
 */
TEST(VgaIntegration, StateIsolation) {
    // First instance - modify VGA state
    {
        DOSBoxContext ctx1(ContextConfig::defaults());
        ctx1.initialize();

        ctx1.vga.vsync.manual = true;
        ctx1.vga.vsync.period = 16.67;
        ctx1.vga.assigned_lfb = 0xE0000000;
        ctx1.vga.cur_mode = reinterpret_cast<struct VideoModeBlock*>(0xDEADBEEF);

        ctx1.shutdown();
    }

    // Second instance - should have defaults
    {
        DOSBoxContext ctx2(ContextConfig::defaults());
        ctx2.initialize();

        EXPECT_FALSE(ctx2.vga.vsync.manual);
        EXPECT_EQ(ctx2.vga.vsync.period, 0.0);
        EXPECT_EQ(ctx2.vga.assigned_lfb, 0);
        EXPECT_EQ(ctx2.vga.cur_mode, nullptr);

        ctx2.shutdown();
    }
}

/**
 * TEST-P06-I02: Context Initializes With VGA
 * Verify context can be initialized and VGA state is valid.
 */
TEST(VgaIntegration, ContextInitializesWithVga) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    // VGA state should be valid
    EXPECT_EQ(ctx.vga.vsync.period, 0.0);
    EXPECT_FALSE(ctx.vga.vsync.manual);
    EXPECT_EQ(ctx.vga.assigned_lfb, 0);
    // cur_mode may or may not be set depending on initialization

    ctx.shutdown();
}

// ===============================================================================
// VGA Hardware State Tests (Sprint 2 Completion)
// ===============================================================================

/**
 * TEST-HW-U01: HW is Null Before Init
 * Verify hw pointer is null before initialization.
 */
TEST(VgaHardware, HwNullBeforeInit) {
    DOSBoxContext ctx(ContextConfig::minimal());
    EXPECT_EQ(ctx.vga.hw, nullptr);
}

/**
 * TEST-HW-U02: HW is Non-Null After Init
 * Verify hw pointer is allocated after initialization.
 */
TEST(VgaHardware, HwNonNullAfterInit) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    // In headless mode, hw may stay nullptr (VGA registers not needed)
    // In full mode, hw should be non-null
#ifndef AIBOX_HEADLESS
    EXPECT_NE(ctx.vga.hw, nullptr);
#endif

    ctx.shutdown();
}

/**
 * TEST-HW-U03: HW Deallocated on Shutdown
 * Verify hw pointer is null after shutdown.
 */
TEST(VgaHardware, HwDeallocatedOnShutdown) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();
    ctx.shutdown();

    EXPECT_EQ(ctx.vga.hw, nullptr);
}

/**
 * TEST-HW-U04: Existing Display Config Fields Still Work
 * Verify the stable API surface fields still function.
 */
TEST(VgaHardware, DisplayConfigFieldsWork) {
    DOSBoxContext ctx(ContextConfig::defaults());
    ctx.initialize();

    ctx.vga.width = 800;
    ctx.vga.height = 600;
    ctx.vga.bpp = 16;
    ctx.vga.mode = VgaMode::LIN16;

    EXPECT_EQ(ctx.vga.width, 800u);
    EXPECT_EQ(ctx.vga.height, 600u);
    EXPECT_EQ(ctx.vga.bpp, 16u);
    EXPECT_EQ(ctx.vga.mode, VgaMode::LIN16);

    ctx.shutdown();
}

/**
 * TEST-HW-I01: VGA State Isolation With HW
 * Verify full VGA hardware state is isolated per instance.
 */
TEST(VgaHardware, HwIsolationBetweenInstances) {
    DOSBoxContext ctx1(ContextConfig::defaults());
    DOSBoxContext ctx2(ContextConfig::defaults());
    ctx1.initialize();
    ctx2.initialize();

#ifndef AIBOX_HEADLESS
    // Both should have independent hw pointers
    ASSERT_NE(ctx1.vga.hw, nullptr);
    ASSERT_NE(ctx2.vga.hw, nullptr);
    EXPECT_NE(ctx1.vga.hw, ctx2.vga.hw);
#endif

    // Config fields are independent
    ctx1.vga.width = 1024;
    ctx2.vga.width = 640;
    EXPECT_EQ(ctx1.vga.width, 1024u);
    EXPECT_EQ(ctx2.vga.width, 640u);

    ctx1.shutdown();
    ctx2.shutdown();
}

/**
 * TEST-HW-I02: Hash Changes on VGA Config Modification
 * Verify modifying VGA display config changes the state hash.
 */
TEST(VgaHardware, HashChangesOnConfigModification) {
    DOSBoxContext ctx(ContextConfig::minimal());
    ctx.initialize();

    auto hash1 = get_state_hash(&ctx, HashMode::Fast);
    ASSERT_TRUE(hash1.has_value());

    ctx.vga.width = 1280;
    ctx.vga.height = 1024;

    auto hash2 = get_state_hash(&ctx, HashMode::Fast);
    ASSERT_TRUE(hash2.has_value());

    EXPECT_NE(hash1.value(), hash2.value());

    ctx.shutdown();
}
