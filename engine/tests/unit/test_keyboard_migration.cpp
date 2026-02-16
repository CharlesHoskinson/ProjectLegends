/**
 * @file test_keyboard_migration.cpp
 * @brief Unit tests for keyboard state in DOSBoxContext.
 *
 * Tests for keyboard buffer, LED state, modifier tracking,
 * PS/2 mouse state, and auxiliary port flags.
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ===============================================================================
// Unit Tests
// ===============================================================================

/**
 * TEST-P08-U01: Keyboard Buffer Default (empty)
 * Verify new context has empty keyboard buffer.
 */
TEST(KeyboardMigration, KeyboardBufferDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.keyboard.buffer_used, 0u);
    EXPECT_EQ(ctx.keyboard.buffer_pos, 0u);
    EXPECT_EQ(ctx.keyboard.pending_key, 0);
}

/**
 * TEST-P08-U02: Keyboard Buffer Add/Remove
 * Verify buffer can store and track usage.
 */
TEST(KeyboardMigration, KeyboardBufferUsage) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Simulate adding to buffer
    ctx.keyboard.buffer[0] = 0x1E;  // 'A' scan code
    ctx.keyboard.buffer[1] = 0x9E;  // 'A' release
    ctx.keyboard.buffer_used = 2;

    EXPECT_EQ(ctx.keyboard.buffer[0], 0x1Eu);
    EXPECT_EQ(ctx.keyboard.buffer[1], 0x9Eu);
    EXPECT_EQ(ctx.keyboard.buffer_used, 2u);
}

/**
 * TEST-P08-U03: LED State Modification
 * Verify LED state can be modified.
 */
TEST(KeyboardMigration, LedStateModification) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Default LED state
    EXPECT_EQ(ctx.keyboard.led_state, 0u);

    // Set LED state (Num Lock = bit 1, Caps Lock = bit 2, Scroll Lock = bit 0)
    ctx.keyboard.led_state = 0x07;  // All LEDs on

    EXPECT_EQ(ctx.keyboard.led_state, 0x07u);
}

/**
 * TEST-P08-U04: Modifier Key Tracking
 * Verify modifier key states are accessible.
 */
TEST(KeyboardMigration, ModifierKeyTracking) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Default: no modifiers pressed
    EXPECT_FALSE(ctx.keyboard.leftalt_pressed);
    EXPECT_FALSE(ctx.keyboard.rightalt_pressed);
    EXPECT_FALSE(ctx.keyboard.leftctrl_pressed);
    EXPECT_FALSE(ctx.keyboard.rightctrl_pressed);
    EXPECT_FALSE(ctx.keyboard.leftshift_pressed);
    EXPECT_FALSE(ctx.keyboard.rightshift_pressed);

    // Press left alt and right shift
    ctx.keyboard.leftalt_pressed = true;
    ctx.keyboard.rightshift_pressed = true;

    EXPECT_TRUE(ctx.keyboard.leftalt_pressed);
    EXPECT_TRUE(ctx.keyboard.rightshift_pressed);
    EXPECT_FALSE(ctx.keyboard.rightalt_pressed);
}

/**
 * TEST-P08-U05: Keyboard State Reset
 * Verify reset clears appropriate fields.
 */
TEST(KeyboardMigration, KeyboardReset) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Set some values
    ctx.keyboard.buffer_used = 5;
    ctx.keyboard.led_state = 0x07;
    ctx.keyboard.leftalt_pressed = true;
    ctx.keyboard.scanning = true;

    // Reset
    ctx.keyboard.reset();

    // Check reset values
    EXPECT_EQ(ctx.keyboard.buffer_used, 0u);
    EXPECT_EQ(ctx.keyboard.led_state, 0u);
    EXPECT_FALSE(ctx.keyboard.leftalt_pressed);
    EXPECT_FALSE(ctx.keyboard.scanning);
    EXPECT_EQ(ctx.keyboard.scanset, 2u);  // Default scanset
}

// ===============================================================================
// Integration Tests
// ===============================================================================

/**
 * TEST-P08-I01: Keyboard Isolation Between Instances
 * Verify keyboard state is isolated per instance.
 */
TEST(KeyboardMigration, KeyboardIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    // Modify ctx1
    ctx1.keyboard.buffer[0] = 0x1E;
    ctx1.keyboard.buffer_used = 1;
    ctx1.keyboard.leftalt_pressed = true;

    // Modify ctx2 differently
    ctx2.keyboard.buffer[0] = 0x2E;
    ctx2.keyboard.buffer_used = 1;
    ctx2.keyboard.rightctrl_pressed = true;

    // Verify isolation
    EXPECT_EQ(ctx1.keyboard.buffer[0], 0x1Eu);
    EXPECT_TRUE(ctx1.keyboard.leftalt_pressed);
    EXPECT_FALSE(ctx1.keyboard.rightctrl_pressed);

    EXPECT_EQ(ctx2.keyboard.buffer[0], 0x2Eu);
    EXPECT_FALSE(ctx2.keyboard.leftalt_pressed);
    EXPECT_TRUE(ctx2.keyboard.rightctrl_pressed);
}

/**
 * TEST-P08-I02: 8042 Controller Buffer State
 * Verify 8042 controller buffer is accessible.
 */
TEST(KeyboardMigration, Controller8042Buffer) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Default: empty 8042 buffer
    EXPECT_EQ(ctx.keyboard.buf8042_len, 0u);
    EXPECT_EQ(ctx.keyboard.buf8042_pos, 0u);

    // Add response to 8042 buffer
    ctx.keyboard.buf8042[0] = 0xFA;  // ACK
    ctx.keyboard.buf8042_len = 1;

    EXPECT_EQ(ctx.keyboard.buf8042[0], 0xFAu);
    EXPECT_EQ(ctx.keyboard.buf8042_len, 1u);
}

/**
 * TEST-P08-I03: Repeat State
 * Verify key repeat state is accessible.
 */
TEST(KeyboardMigration, RepeatState) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Set repeat parameters
    ctx.keyboard.repeat.key = 0x1E;
    ctx.keyboard.repeat.rate = 30;
    ctx.keyboard.repeat.pause = 500;

    EXPECT_EQ(ctx.keyboard.repeat.key, 0x1Eu);
    EXPECT_EQ(ctx.keyboard.repeat.rate, 30u);
    EXPECT_EQ(ctx.keyboard.repeat.pause, 500u);
}

// ===============================================================================
// PS/2 Mouse State Tests (Sprint 2 Completion)
// ===============================================================================

/**
 * TEST-PS2-U01: PS/2 Mouse Default State
 * Verify new context has default PS/2 mouse values.
 */
TEST(KeyboardMigration, Ps2MouseDefaults) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.keyboard.ps2mouse.type, 0u);
    EXPECT_EQ(ctx.keyboard.ps2mouse.mode, 2u);
    EXPECT_EQ(ctx.keyboard.ps2mouse.reset_mode, 2u);
    EXPECT_EQ(ctx.keyboard.ps2mouse.samplerate, 80u);
    EXPECT_EQ(ctx.keyboard.ps2mouse.resolution, 1u);
    EXPECT_FLOAT_EQ(ctx.keyboard.ps2mouse.acx, 0.0f);
    EXPECT_FLOAT_EQ(ctx.keyboard.ps2mouse.acy, 0.0f);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.reporting);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.scale21);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.intellimouse_mode);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.intellimouse_btn45);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.int33_taken);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.l);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.m);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.r);
}

/**
 * TEST-PS2-U02: PS/2 Mouse State Modification
 * Verify PS/2 mouse state can be modified and read back.
 */
TEST(KeyboardMigration, Ps2MouseModification) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.keyboard.ps2mouse.type = 3;  // IntelliMouse
    ctx.keyboard.ps2mouse.samplerate = 200;
    ctx.keyboard.ps2mouse.acx = 10.5f;
    ctx.keyboard.ps2mouse.acy = -3.2f;
    ctx.keyboard.ps2mouse.reporting = true;
    ctx.keyboard.ps2mouse.l = true;
    ctx.keyboard.ps2mouse.intellimouse_mode = true;

    EXPECT_EQ(ctx.keyboard.ps2mouse.type, 3u);
    EXPECT_EQ(ctx.keyboard.ps2mouse.samplerate, 200u);
    EXPECT_FLOAT_EQ(ctx.keyboard.ps2mouse.acx, 10.5f);
    EXPECT_FLOAT_EQ(ctx.keyboard.ps2mouse.acy, -3.2f);
    EXPECT_TRUE(ctx.keyboard.ps2mouse.reporting);
    EXPECT_TRUE(ctx.keyboard.ps2mouse.l);
    EXPECT_TRUE(ctx.keyboard.ps2mouse.intellimouse_mode);
}

/**
 * TEST-PS2-U03: PS/2 Mouse Reset
 * Verify ps2mouse.reset() restores defaults.
 */
TEST(KeyboardMigration, Ps2MouseReset) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Modify state
    ctx.keyboard.ps2mouse.type = 4;
    ctx.keyboard.ps2mouse.acx = 99.0f;
    ctx.keyboard.ps2mouse.l = true;
    ctx.keyboard.ps2mouse.r = true;
    ctx.keyboard.ps2mouse.intellimouse_btn45 = true;

    // Reset
    ctx.keyboard.ps2mouse.reset();

    EXPECT_EQ(ctx.keyboard.ps2mouse.type, 0u);
    EXPECT_FLOAT_EQ(ctx.keyboard.ps2mouse.acx, 0.0f);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.l);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.r);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.intellimouse_btn45);
}

/**
 * TEST-PS2-U04: Keyboard Reset Includes PS/2 Mouse
 * Verify KeyboardState::reset() also resets ps2mouse.
 */
TEST(KeyboardMigration, KeyboardResetIncludesPs2Mouse) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.keyboard.ps2mouse.type = 3;
    ctx.keyboard.ps2mouse.l = true;
    ctx.keyboard.enable_aux = true;
    ctx.keyboard.aux_command = 0xAA;

    ctx.keyboard.reset();

    EXPECT_EQ(ctx.keyboard.ps2mouse.type, 0u);
    EXPECT_FALSE(ctx.keyboard.ps2mouse.l);
    EXPECT_FALSE(ctx.keyboard.enable_aux);
    EXPECT_EQ(ctx.keyboard.aux_command, 0u);
}

/**
 * TEST-BUF96-U01: Buffer Size Is 96
 * Verify BUFFER_SIZE matches global KEYBUFSIZE (32*3=96).
 */
TEST(KeyboardMigration, BufferSizeIs96) {
    EXPECT_EQ(KeyboardState::BUFFER_SIZE, 96u);

    DOSBoxContext ctx(ContextConfig::minimal());

    // Write to last buffer position
    ctx.keyboard.buffer[95] = 0xFF;
    EXPECT_EQ(ctx.keyboard.buffer[95], 0xFFu);
}

/**
 * TEST-HASH-U01: PS/2 Mouse State Changes Hash
 * Verify modifying ps2mouse state produces different hash.
 */
TEST(KeyboardMigration, Ps2MouseChangesHash) {
    DOSBoxContext ctx(ContextConfig::minimal());
    ctx.initialize();

    auto hash1 = get_state_hash(&ctx, HashMode::Fast);
    ASSERT_TRUE(hash1.has_value());

    ctx.keyboard.ps2mouse.l = true;
    ctx.keyboard.ps2mouse.acx = 5.0f;

    auto hash2 = get_state_hash(&ctx, HashMode::Fast);
    ASSERT_TRUE(hash2.has_value());

    EXPECT_NE(hash1.value(), hash2.value());

    ctx.shutdown();
}

/**
 * TEST-PS2-I01: PS/2 Mouse Isolation Between Instances
 * Verify PS/2 mouse state is isolated per instance.
 */
TEST(KeyboardMigration, Ps2MouseIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    ctx1.keyboard.ps2mouse.l = true;
    ctx1.keyboard.ps2mouse.acx = 42.0f;
    ctx1.keyboard.ps2mouse.intellimouse_mode = true;

    ctx2.keyboard.ps2mouse.r = true;
    ctx2.keyboard.ps2mouse.acy = -10.0f;

    // Verify isolation
    EXPECT_TRUE(ctx1.keyboard.ps2mouse.l);
    EXPECT_FALSE(ctx1.keyboard.ps2mouse.r);
    EXPECT_FLOAT_EQ(ctx1.keyboard.ps2mouse.acx, 42.0f);
    EXPECT_TRUE(ctx1.keyboard.ps2mouse.intellimouse_mode);

    EXPECT_FALSE(ctx2.keyboard.ps2mouse.l);
    EXPECT_TRUE(ctx2.keyboard.ps2mouse.r);
    EXPECT_FLOAT_EQ(ctx2.keyboard.ps2mouse.acy, -10.0f);
    EXPECT_FALSE(ctx2.keyboard.ps2mouse.intellimouse_mode);
}

/**
 * TEST-AUX-U01: Auxiliary Port Flags Default
 * Verify auxiliary port flags default state.
 */
TEST(KeyboardMigration, AuxPortFlagsDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_FALSE(ctx.keyboard.enable_aux);
    EXPECT_FALSE(ctx.keyboard.reset_state);
    EXPECT_EQ(ctx.keyboard.aux_command, 0u);
}
