/**
 * @file test_keyboard_migration.cpp
 * @brief Unit tests for keyboard state in DOSBoxContext.
 *
 * Tests for keyboard buffer, LED state, modifier tracking.
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"

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
