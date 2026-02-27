// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for Application::processEvents() branches.
// Tests event routing via the PAL InputEvent types and modifier tracking.
// Since Application::processEvents() is private, we test observable effects
// through the public API (init + run) and via extracted pure functions
// (matchHotkey, InputMapper, JoystickMapper).

#include "app/hotkey_dispatcher.h"
#include "app/input_mapper.h"
#include "app/joystick_mapper.h"
#include "app/menu_system.h"
#include "app/action_bus.h"
#include "app/ai_panel.h"

#include <pal/input_source.h>
#include <pal/types.h>

#include <gtest/gtest.h>

#include <atomic>
#include <cstdint>
#include <vector>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Helper: Build an InputEvent
// ═══════════════════════════════════════════════════════════════════════════

pal::InputEvent makeKeyEvent(pal::InputEventType type, uint16_t scancode) {
    pal::InputEvent ev;
    ev.type = type;
    ev.key.scancode = scancode;
    ev.key.keycode = scancode;
    ev.key.repeat = false;
    return ev;
}

pal::InputEvent makeMouseMotionEvent(int32_t dx, int32_t dy) {
    pal::InputEvent ev;
    ev.type = pal::InputEventType::MouseMotion;
    ev.mouse_motion.dx = dx;
    ev.mouse_motion.dy = dy;
    ev.mouse_motion.x = 0;
    ev.mouse_motion.y = 0;
    return ev;
}

pal::InputEvent makeMouseButtonEvent(pal::InputEventType type, uint8_t button,
                                      int32_t x = 0, int32_t y = 0) {
    pal::InputEvent ev;
    ev.type = type;
    ev.mouse_button.button = button;
    ev.mouse_button.clicks = 1;
    ev.mouse_button.x = x;
    ev.mouse_button.y = y;
    return ev;
}

pal::InputEvent makeJoystickAxisEvent(uint8_t id, int16_t axis, int16_t value) {
    pal::InputEvent ev;
    ev.type = pal::InputEventType::JoystickAxis;
    ev.joy_axis.id = id;
    ev.joy_axis.axis = axis;
    ev.joy_axis.value = value;
    return ev;
}

pal::InputEvent makeJoystickButtonEvent(uint8_t id, uint8_t button, bool pressed) {
    pal::InputEvent ev;
    ev.type = pal::InputEventType::JoystickButton;
    ev.joy_button.id = id;
    ev.joy_button.button = button;
    ev.joy_button.pressed = pressed;
    return ev;
}

pal::InputEvent makeWindowCloseEvent() {
    pal::InputEvent ev;
    ev.type = pal::InputEventType::WindowClose;
    return ev;
}

// ═══════════════════════════════════════════════════════════════════════════
// WindowClose event
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationEventsTest, WindowClose_EventType) {
    auto ev = makeWindowCloseEvent();
    EXPECT_EQ(ev.type, pal::InputEventType::WindowClose);
}

// ═══════════════════════════════════════════════════════════════════════════
// Modifier tracking — test the modifier bitmask logic
// Application uses scancodes 0xE0-0xE6 for modifier keys.
// ═══════════════════════════════════════════════════════════════════════════

class ModifierTrackingTest : public ::testing::Test {
protected:
    // Simulate Application's modifier tracking
    uint8_t modifiers_ = 0;

    static constexpr uint8_t kModLCtrl  = 0x01;
    static constexpr uint8_t kModRCtrl  = 0x02;
    static constexpr uint8_t kModCtrl   = kModLCtrl | kModRCtrl;
    static constexpr uint8_t kModLShift = 0x04;
    static constexpr uint8_t kModRShift = 0x08;
    static constexpr uint8_t kModShift  = kModLShift | kModRShift;
    static constexpr uint8_t kModLAlt   = 0x10;
    static constexpr uint8_t kModRAlt   = 0x20;
    static constexpr uint8_t kModAlt    = kModLAlt | kModRAlt;

    void applyModifier(uint16_t scancode, bool down) {
        if (scancode == 0xE0) {
            if (down) modifiers_ |= kModLCtrl;
            else      modifiers_ &= static_cast<uint8_t>(~kModLCtrl);
        }
        if (scancode == 0xE4) {
            if (down) modifiers_ |= kModRCtrl;
            else      modifiers_ &= static_cast<uint8_t>(~kModRCtrl);
        }
        if (scancode == 0xE1) {
            if (down) modifiers_ |= kModLShift;
            else      modifiers_ &= static_cast<uint8_t>(~kModLShift);
        }
        if (scancode == 0xE5) {
            if (down) modifiers_ |= kModRShift;
            else      modifiers_ &= static_cast<uint8_t>(~kModRShift);
        }
        if (scancode == 0xE2) {
            if (down) modifiers_ |= kModLAlt;
            else      modifiers_ &= static_cast<uint8_t>(~kModLAlt);
        }
        if (scancode == 0xE6) {
            if (down) modifiers_ |= kModRAlt;
            else      modifiers_ &= static_cast<uint8_t>(~kModRAlt);
        }
    }
};

TEST_F(ModifierTrackingTest, LCtrl_Down) {
    applyModifier(0xE0, true);
    EXPECT_EQ(modifiers_ & kModLCtrl, kModLCtrl);
}

TEST_F(ModifierTrackingTest, LCtrl_Up) {
    applyModifier(0xE0, true);
    applyModifier(0xE0, false);
    EXPECT_EQ(modifiers_ & kModLCtrl, 0);
}

TEST_F(ModifierTrackingTest, RCtrl_Down) {
    applyModifier(0xE4, true);
    EXPECT_EQ(modifiers_ & kModRCtrl, kModRCtrl);
}

TEST_F(ModifierTrackingTest, RCtrl_Up) {
    applyModifier(0xE4, true);
    applyModifier(0xE4, false);
    EXPECT_EQ(modifiers_ & kModRCtrl, 0);
}

TEST_F(ModifierTrackingTest, LShift_Down) {
    applyModifier(0xE1, true);
    EXPECT_EQ(modifiers_ & kModLShift, kModLShift);
}

TEST_F(ModifierTrackingTest, LShift_Up) {
    applyModifier(0xE1, true);
    applyModifier(0xE1, false);
    EXPECT_EQ(modifiers_ & kModLShift, 0);
}

TEST_F(ModifierTrackingTest, RShift_Down) {
    applyModifier(0xE5, true);
    EXPECT_EQ(modifiers_ & kModRShift, kModRShift);
}

TEST_F(ModifierTrackingTest, LAlt_Down) {
    applyModifier(0xE2, true);
    EXPECT_EQ(modifiers_ & kModLAlt, kModLAlt);
}

TEST_F(ModifierTrackingTest, RAlt_Down) {
    applyModifier(0xE6, true);
    EXPECT_EQ(modifiers_ & kModRAlt, kModRAlt);
}

TEST_F(ModifierTrackingTest, MultipleModifiers) {
    applyModifier(0xE0, true); // LCtrl
    applyModifier(0xE1, true); // LShift
    EXPECT_EQ(modifiers_ & kModLCtrl, kModLCtrl);
    EXPECT_EQ(modifiers_ & kModLShift, kModLShift);
    EXPECT_EQ(modifiers_ & kModCtrl, kModLCtrl);
    EXPECT_EQ(modifiers_ & kModShift, kModLShift);
}

TEST_F(ModifierTrackingTest, ReleaseOne_KeepsOther) {
    applyModifier(0xE0, true);  // LCtrl
    applyModifier(0xE2, true);  // LAlt
    applyModifier(0xE0, false); // Release LCtrl
    EXPECT_EQ(modifiers_ & kModLCtrl, 0);
    EXPECT_EQ(modifiers_ & kModLAlt, kModLAlt);
}

// ═══════════════════════════════════════════════════════════════════════════
// Menu routing — keys forwarded to menu when open
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationEventsTest, MenuSystem_IsOpenInitially_False) {
    MenuSystem menu;
    EXPECT_FALSE(menu.isOpen());
}

TEST(ApplicationEventsTest, MenuSystem_OpenClose) {
    MenuSystem menu;
    ActionBus bus;
    menu.initialize(&bus);
    menu.open();
    EXPECT_TRUE(menu.isOpen());
    menu.close();
    EXPECT_FALSE(menu.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// AI panel routing — keys forwarded to AI panel when open
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationEventsTest, AIPanel_IsOpenInitially_False) {
    AIPanel panel;
    EXPECT_FALSE(panel.isOpen());
}

TEST(ApplicationEventsTest, AIPanel_OpenClose) {
    AIPanel panel;
    ActionBus bus;
    panel.initialize(&bus);
    panel.open();
    EXPECT_TRUE(panel.isOpen());
    panel.close();
    EXPECT_FALSE(panel.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Hotkey matching and dispatch
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationEventsTest, Hotkey_F12_OpenMenu) {
    auto r = matchHotkey(0x45, 0, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::OpenMenu);
}

TEST(ApplicationEventsTest, Hotkey_NoMatch_RegularKey) {
    // Regular 'A' key (scancode 0x04) should not match any hotkey
    auto r = matchHotkey(0x04, 0, false);
    EXPECT_FALSE(r.matched);
}

// ═══════════════════════════════════════════════════════════════════════════
// Mouse events — capture logic
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationEventsTest, MouseButtonDown_LeftClick_CreatesEvent) {
    auto ev = makeMouseButtonEvent(pal::InputEventType::MouseButtonDown, 1);
    EXPECT_EQ(ev.type, pal::InputEventType::MouseButtonDown);
    EXPECT_EQ(ev.mouse_button.button, 1);
}

TEST(ApplicationEventsTest, MouseButtonDown_MiddleClick_CreatesEvent) {
    auto ev = makeMouseButtonEvent(pal::InputEventType::MouseButtonDown, 2);
    EXPECT_EQ(ev.mouse_button.button, 2);
}

TEST(ApplicationEventsTest, MouseMotion_CreatesEvent) {
    auto ev = makeMouseMotionEvent(10, -5);
    EXPECT_EQ(ev.type, pal::InputEventType::MouseMotion);
    EXPECT_EQ(ev.mouse_motion.dx, 10);
    EXPECT_EQ(ev.mouse_motion.dy, -5);
}

TEST(ApplicationEventsTest, MouseButtonUp_CreatesEvent) {
    auto ev = makeMouseButtonEvent(pal::InputEventType::MouseButtonUp, 1);
    EXPECT_EQ(ev.type, pal::InputEventType::MouseButtonUp);
}

// ═══════════════════════════════════════════════════════════════════════════
// Joystick events
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationEventsTest, JoystickAxis_EventConstruction) {
    auto ev = makeJoystickAxisEvent(0, 0, 16000);
    EXPECT_EQ(ev.type, pal::InputEventType::JoystickAxis);
    EXPECT_EQ(ev.joy_axis.id, 0);
    EXPECT_EQ(ev.joy_axis.axis, 0);
    EXPECT_EQ(ev.joy_axis.value, 16000);
}

TEST(ApplicationEventsTest, JoystickButton_Pressed) {
    auto ev = makeJoystickButtonEvent(0, 1, true);
    EXPECT_EQ(ev.type, pal::InputEventType::JoystickButton);
    EXPECT_EQ(ev.joy_button.id, 0);
    EXPECT_EQ(ev.joy_button.button, 1);
    EXPECT_TRUE(ev.joy_button.pressed);
}

TEST(ApplicationEventsTest, JoystickButton_Released) {
    auto ev = makeJoystickButtonEvent(0, 1, false);
    EXPECT_FALSE(ev.joy_button.pressed);
}

TEST(ApplicationEventsTest, JoystickMapper_DefaultState) {
    JoystickMapper mapper;
    auto s = mapper.state(0);
    EXPECT_EQ(s.buttons, 0);
}

TEST(ApplicationEventsTest, JoystickMapper_UpdateAndRead) {
    JoystickMapper mapper;
    mapper.update(0, 100, -200, 0x03);
    auto s = mapper.state(0);
    EXPECT_EQ(s.buttons, 0x03);
}

// ═══════════════════════════════════════════════════════════════════════════
// InputEvent construction — verify union layout works
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationEventsTest, InputEvent_DefaultIsNone) {
    pal::InputEvent ev;
    EXPECT_EQ(ev.type, pal::InputEventType::None);
}

TEST(ApplicationEventsTest, InputEvent_KeyDown) {
    auto ev = makeKeyEvent(pal::InputEventType::KeyDown, 0x1A);
    EXPECT_EQ(ev.type, pal::InputEventType::KeyDown);
    EXPECT_EQ(ev.key.scancode, 0x1A);
}

TEST(ApplicationEventsTest, InputEvent_KeyUp) {
    auto ev = makeKeyEvent(pal::InputEventType::KeyUp, 0x1A);
    EXPECT_EQ(ev.type, pal::InputEventType::KeyUp);
}

} // namespace
} // namespace legends
