/**
 * @file test_multi_instance_smoke.cpp
 * @brief Sprint 2 Completion: Multi-Instance Smoke Test
 *
 * Validates that all 3 completed migrations (Keyboard, PIC, VGA)
 * actually enable independent DOSBoxContext instances. This test
 * is the gate for Sprint 4+.
 *
 * Tests:
 * - Create two contexts independently
 * - Modify keyboard/PIC/VGA state in each
 * - Verify state isolation (A unaffected by B)
 * - Hash A and B independently, verify they differ
 * - Destroy both, verify no leaks
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Multi-Instance Smoke Test
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * SMOKE-01: Independent Context Creation
 * Create two contexts and verify they are independent objects.
 */
TEST(MultiInstanceSmoke, IndependentContextCreation) {
    DOSBoxContext ctxA(ContextConfig::minimal());
    DOSBoxContext ctxB(ContextConfig::minimal());

    EXPECT_NE(&ctxA, &ctxB);

    auto resultA = ctxA.initialize();
    auto resultB = ctxB.initialize();
    ASSERT_TRUE(resultA.has_value());
    ASSERT_TRUE(resultB.has_value());

    EXPECT_TRUE(ctxA.is_initialized());
    EXPECT_TRUE(ctxB.is_initialized());

    ctxA.shutdown();
    ctxB.shutdown();
}

/**
 * SMOKE-02: Keyboard State Isolation
 * Modify keyboard/PS2 mouse state in A, verify B is unaffected.
 */
TEST(MultiInstanceSmoke, KeyboardStateIsolation) {
    DOSBoxContext ctxA(ContextConfig::minimal());
    DOSBoxContext ctxB(ContextConfig::minimal());
    ctxA.initialize();
    ctxB.initialize();

    // Modify A's keyboard state
    ctxA.keyboard.buffer[0] = 0x1E;
    ctxA.keyboard.buffer_used = 1;
    ctxA.keyboard.leftalt_pressed = true;
    ctxA.keyboard.ps2mouse.l = true;
    ctxA.keyboard.ps2mouse.acx = 42.0f;
    ctxA.keyboard.ps2mouse.intellimouse_mode = true;
    ctxA.keyboard.enable_aux = true;

    // Modify B's keyboard state differently
    ctxB.keyboard.buffer[0] = 0x2E;
    ctxB.keyboard.buffer_used = 1;
    ctxB.keyboard.rightshift_pressed = true;
    ctxB.keyboard.ps2mouse.r = true;
    ctxB.keyboard.ps2mouse.acy = -10.0f;

    // Verify A is unaffected by B
    EXPECT_EQ(ctxA.keyboard.buffer[0], 0x1Eu);
    EXPECT_TRUE(ctxA.keyboard.leftalt_pressed);
    EXPECT_FALSE(ctxA.keyboard.rightshift_pressed);
    EXPECT_TRUE(ctxA.keyboard.ps2mouse.l);
    EXPECT_FALSE(ctxA.keyboard.ps2mouse.r);
    EXPECT_FLOAT_EQ(ctxA.keyboard.ps2mouse.acx, 42.0f);
    EXPECT_FLOAT_EQ(ctxA.keyboard.ps2mouse.acy, 0.0f);  // Not modified in A
    EXPECT_TRUE(ctxA.keyboard.enable_aux);

    // Verify B is unaffected by A
    EXPECT_EQ(ctxB.keyboard.buffer[0], 0x2Eu);
    EXPECT_FALSE(ctxB.keyboard.leftalt_pressed);
    EXPECT_TRUE(ctxB.keyboard.rightshift_pressed);
    EXPECT_FALSE(ctxB.keyboard.ps2mouse.l);
    EXPECT_TRUE(ctxB.keyboard.ps2mouse.r);
    EXPECT_FLOAT_EQ(ctxB.keyboard.ps2mouse.acy, -10.0f);
    EXPECT_FALSE(ctxB.keyboard.ps2mouse.intellimouse_mode);
    EXPECT_FALSE(ctxB.keyboard.enable_aux);

    ctxA.shutdown();
    ctxB.shutdown();
}

/**
 * SMOKE-03: PIC Controller State Isolation
 * Modify PIC controller registers in A, verify B is unaffected.
 */
TEST(MultiInstanceSmoke, PicControllerIsolation) {
    DOSBoxContext ctxA(ContextConfig::minimal());
    DOSBoxContext ctxB(ContextConfig::minimal());
    ctxA.initialize();
    ctxB.initialize();

    // Modify A's PIC state
    ctxA.pic.controllers[0].imr = 0x00;  // Unmask all
    ctxA.pic.controllers[0].auto_eoi = true;
    ctxA.pic.controllers[1].vector_base = 0x70;
    ctxA.pic.enable_slave_pic = false;
    ctxA.pic.ticks = 1000;

    // Modify B's PIC state differently
    ctxB.pic.controllers[0].imr = 0xFE;  // Unmask only IRQ0
    ctxB.pic.controllers[0].irr = 0x01;
    ctxB.pic.ticks = 500;

    // Verify A is unaffected by B
    EXPECT_EQ(ctxA.pic.controllers[0].imr, 0x00u);
    EXPECT_TRUE(ctxA.pic.controllers[0].auto_eoi);
    EXPECT_EQ(ctxA.pic.controllers[0].irr, 0u);  // Not modified in A
    EXPECT_EQ(ctxA.pic.controllers[1].vector_base, 0x70u);
    EXPECT_FALSE(ctxA.pic.enable_slave_pic);
    EXPECT_EQ(ctxA.pic.ticks, 1000u);

    // Verify B is unaffected by A
    EXPECT_EQ(ctxB.pic.controllers[0].imr, 0xFEu);
    EXPECT_FALSE(ctxB.pic.controllers[0].auto_eoi);
    EXPECT_EQ(ctxB.pic.controllers[0].irr, 0x01u);
    EXPECT_TRUE(ctxB.pic.enable_slave_pic);
    EXPECT_EQ(ctxB.pic.ticks, 500u);

    ctxA.shutdown();
    ctxB.shutdown();
}

/**
 * SMOKE-04: VGA State Isolation
 * Modify VGA display config in A, verify B is unaffected.
 */
TEST(MultiInstanceSmoke, VgaStateIsolation) {
    DOSBoxContext ctxA(ContextConfig::defaults());
    DOSBoxContext ctxB(ContextConfig::defaults());
    ctxA.initialize();
    ctxB.initialize();

    // Modify A's VGA state
    ctxA.vga.width = 1024;
    ctxA.vga.height = 768;
    ctxA.vga.mode = VgaMode::LIN16;
    ctxA.vga.vsync.manual = true;
    ctxA.vga.assigned_lfb = 0xE0000000;

    // Modify B's VGA state differently
    ctxB.vga.width = 320;
    ctxB.vga.height = 200;
    ctxB.vga.mode = VgaMode::VGA;
    ctxB.vga.dac_8bit = true;

    // Verify isolation
    EXPECT_EQ(ctxA.vga.width, 1024u);
    EXPECT_EQ(ctxA.vga.mode, VgaMode::LIN16);
    EXPECT_TRUE(ctxA.vga.vsync.manual);
    EXPECT_FALSE(ctxA.vga.dac_8bit);

    EXPECT_EQ(ctxB.vga.width, 320u);
    EXPECT_EQ(ctxB.vga.mode, VgaMode::VGA);
    EXPECT_FALSE(ctxB.vga.vsync.manual);
    EXPECT_TRUE(ctxB.vga.dac_8bit);

#ifndef AIBOX_HEADLESS
    // HW pointers should be independent
    ASSERT_NE(ctxA.vga.hw, nullptr);
    ASSERT_NE(ctxB.vga.hw, nullptr);
    EXPECT_NE(ctxA.vga.hw, ctxB.vga.hw);
#endif

    ctxA.shutdown();
    ctxB.shutdown();
}

/**
 * SMOKE-05: Independent Hashes After Different Modifications
 * Modify A and B differently, verify their hashes differ.
 */
TEST(MultiInstanceSmoke, IndependentHashesDiffer) {
    DOSBoxContext ctxA(ContextConfig::minimal());
    DOSBoxContext ctxB(ContextConfig::minimal());
    ctxA.initialize();
    ctxB.initialize();

    // Both start with same config → same hash
    auto hashA0 = get_state_hash(&ctxA, HashMode::Fast);
    auto hashB0 = get_state_hash(&ctxB, HashMode::Fast);
    ASSERT_TRUE(hashA0.has_value());
    ASSERT_TRUE(hashB0.has_value());
    EXPECT_EQ(hashA0.value(), hashB0.value());

    // Step A forward, leave B alone
    ctxA.step(100);

    auto hashA1 = get_state_hash(&ctxA, HashMode::Fast);
    auto hashB1 = get_state_hash(&ctxB, HashMode::Fast);
    ASSERT_TRUE(hashA1.has_value());
    ASSERT_TRUE(hashB1.has_value());

    // Hashes should now differ
    EXPECT_NE(hashA1.value(), hashB1.value());

    // B's hash should be unchanged
    EXPECT_EQ(hashB0.value(), hashB1.value());

    ctxA.shutdown();
    ctxB.shutdown();
}

/**
 * SMOKE-06: Hash Stability (Same State = Same Hash)
 * Verify computing hash twice on same state produces identical results.
 */
TEST(MultiInstanceSmoke, HashStability) {
    DOSBoxContext ctx(ContextConfig::minimal());
    ctx.initialize();
    ctx.step(50);

    auto hash1 = get_state_hash(&ctx, HashMode::Fast);
    auto hash2 = get_state_hash(&ctx, HashMode::Fast);
    ASSERT_TRUE(hash1.has_value());
    ASSERT_TRUE(hash2.has_value());
    EXPECT_EQ(hash1.value(), hash2.value());

    ctx.shutdown();
}

/**
 * SMOKE-07: Cross-Subsystem State Modification
 * Modify keyboard, PIC, and VGA in one context while leaving the
 * other untouched. Verify complete isolation.
 */
TEST(MultiInstanceSmoke, CrossSubsystemIsolation) {
    DOSBoxContext ctxA(ContextConfig::minimal());
    DOSBoxContext ctxB(ContextConfig::minimal());
    ctxA.initialize();
    ctxB.initialize();

    // Snapshot B's hash before touching A
    auto hashB_before = get_state_hash(&ctxB, HashMode::Fast);
    ASSERT_TRUE(hashB_before.has_value());

    // Heavily modify A across all 3 migrated subsystems
    ctxA.keyboard.buffer[0] = 0x1E;
    ctxA.keyboard.buffer_used = 1;
    ctxA.keyboard.ps2mouse.l = true;
    ctxA.keyboard.ps2mouse.acx = 100.0f;
    ctxA.pic.controllers[0].imr = 0x00;
    ctxA.pic.controllers[0].isr = 0x03;
    ctxA.pic.ticks = 999;
    ctxA.vga.width = 1920;
    ctxA.vga.height = 1080;
    ctxA.vga.frame_counter = 60;

    // B's hash should be completely unaffected
    auto hashB_after = get_state_hash(&ctxB, HashMode::Fast);
    ASSERT_TRUE(hashB_after.has_value());
    EXPECT_EQ(hashB_before.value(), hashB_after.value());

    // A's hash should be different from B
    auto hashA = get_state_hash(&ctxA, HashMode::Fast);
    ASSERT_TRUE(hashA.has_value());
    EXPECT_NE(hashA.value(), hashB_after.value());

    ctxA.shutdown();
    ctxB.shutdown();
}

/**
 * SMOKE-08: Clean Destruction
 * Create and destroy multiple contexts, verify no crashes.
 * (ASan will catch leaks if run under sanitizers)
 */
TEST(MultiInstanceSmoke, CleanDestruction) {
    for (int i = 0; i < 5; ++i) {
        DOSBoxContext ctxA(ContextConfig::minimal());
        DOSBoxContext ctxB(ContextConfig::minimal());
        ctxA.initialize();
        ctxB.initialize();

        // Modify state
        ctxA.keyboard.ps2mouse.type = 3;
        ctxB.pic.controllers[0].imr = 0x00;

        ctxA.shutdown();
        ctxB.shutdown();
    }
    // No crash = success. ASan will detect leaks.
}
