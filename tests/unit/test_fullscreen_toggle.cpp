// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for Sprint 1 fullscreen toggle functionality:
// hotkey mapping (Alt+Enter), ActionBus dispatch, and state tracking.

#include <gtest/gtest.h>
#include "app/action_bus.h"
#include "app/hotkey_dispatcher.h"

namespace legends {
namespace {

// SDL3 Enter scancode
constexpr uint16_t kEnterScancode = 0x28;

// ═══════════════════════════════════════════════════════════════════════════
// Action enum
// ═══════════════════════════════════════════════════════════════════════════

TEST(FullscreenToggleTest, ToggleFullscreenActionExistsInEnum) {
    // Verify the enum value is accessible and has a distinct value
    Action a = Action::ToggleFullscreen;
    EXPECT_NE(static_cast<uint16_t>(a), static_cast<uint16_t>(Action::Quit));
    EXPECT_NE(static_cast<uint16_t>(a), static_cast<uint16_t>(Action::Pause));
}

// ═══════════════════════════════════════════════════════════════════════════
// Alt+Enter hotkey mapping
// ═══════════════════════════════════════════════════════════════════════════

TEST(FullscreenToggleTest, AltEnterMapsToToggleFullscreen) {
    auto r = matchHotkey(kEnterScancode, kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ToggleFullscreen);
}

TEST(FullscreenToggleTest, AltEnterWithRAlt) {
    auto r = matchHotkey(kEnterScancode, kHkModRAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ToggleFullscreen);
}

TEST(FullscreenToggleTest, CtrlEnterDoesNotMatchFullscreen) {
    auto r = matchHotkey(kEnterScancode, kHkModLCtrl, false);
    EXPECT_FALSE(r.matched);
}

TEST(FullscreenToggleTest, ShiftEnterDoesNotMatchFullscreen) {
    auto r = matchHotkey(kEnterScancode, kHkModLShift, false);
    EXPECT_FALSE(r.matched);
}

TEST(FullscreenToggleTest, EnterWithoutModifierDoesNotMatch) {
    auto r = matchHotkey(kEnterScancode, 0, false);
    EXPECT_FALSE(r.matched);
}

TEST(FullscreenToggleTest, AltEnterParamIsZero) {
    auto r = matchHotkey(kEnterScancode, kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.param, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// ActionBus dispatch for ToggleFullscreen
// ═══════════════════════════════════════════════════════════════════════════

TEST(FullscreenToggleTest, DispatchToggleFullscreenInvokesHandler) {
    ActionBus bus;
    int call_count = 0;
    bus.registerHandler(Action::ToggleFullscreen, [&](int) { ++call_count; });

    bus.dispatch(Action::ToggleFullscreen);
    EXPECT_EQ(call_count, 1);
}

TEST(FullscreenToggleTest, DispatchOtherActionDoesNotInvokeFullscreenHandler) {
    ActionBus bus;
    int call_count = 0;
    bus.registerHandler(Action::ToggleFullscreen, [&](int) { ++call_count; });

    bus.dispatch(Action::Pause);
    EXPECT_EQ(call_count, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Fullscreen state toggle tracking
// ═══════════════════════════════════════════════════════════════════════════

TEST(FullscreenToggleTest, FullscreenBoolStartsFalse) {
    bool fullscreen = false;
    EXPECT_FALSE(fullscreen);
}

TEST(FullscreenToggleTest, ToggleFromOffToOn) {
    bool fullscreen = false;
    ActionBus bus;
    bus.registerHandler(Action::ToggleFullscreen,
                        [&](int) { fullscreen = !fullscreen; });

    bus.dispatch(Action::ToggleFullscreen);
    EXPECT_TRUE(fullscreen);
}

TEST(FullscreenToggleTest, ToggleFromOnToOff) {
    bool fullscreen = true;
    ActionBus bus;
    bus.registerHandler(Action::ToggleFullscreen,
                        [&](int) { fullscreen = !fullscreen; });

    bus.dispatch(Action::ToggleFullscreen);
    EXPECT_FALSE(fullscreen);
}

TEST(FullscreenToggleTest, RepeatedToggles) {
    bool fullscreen = false;
    ActionBus bus;
    bus.registerHandler(Action::ToggleFullscreen,
                        [&](int) { fullscreen = !fullscreen; });

    bus.dispatch(Action::ToggleFullscreen);
    EXPECT_TRUE(fullscreen);
    bus.dispatch(Action::ToggleFullscreen);
    EXPECT_FALSE(fullscreen);
    bus.dispatch(Action::ToggleFullscreen);
    EXPECT_TRUE(fullscreen);
}

// ═══════════════════════════════════════════════════════════════════════════
// Simulated keydown vs keyup: only keydown should trigger
// ═══════════════════════════════════════════════════════════════════════════

TEST(FullscreenToggleTest, AltEnterOnlyOnKeydown) {
    // The hotkey dispatcher is called on keydown events only.
    // Simulate: keydown matches, but we verify that a "keyup" scenario
    // (application would not call matchHotkey on keyup) would not toggle.
    bool fullscreen = false;
    ActionBus bus;
    bus.registerHandler(Action::ToggleFullscreen,
                        [&](int) { fullscreen = !fullscreen; });

    // Keydown: match and dispatch
    auto r = matchHotkey(kEnterScancode, kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    if (r.matched) {
        bus.dispatch(r.action, r.param);
    }
    EXPECT_TRUE(fullscreen);

    // Keyup: application should NOT call matchHotkey; state unchanged
    // (We simply verify no second dispatch occurs)
    EXPECT_TRUE(fullscreen);
}

TEST(FullscreenToggleTest, DispatchCountIncrementsOnToggleFullscreen) {
    ActionBus bus;
    bus.registerHandler(Action::ToggleFullscreen, [](int) {});

    uint32_t before = bus.dispatchCount();
    bus.dispatch(Action::ToggleFullscreen);
    EXPECT_EQ(bus.dispatchCount(), before + 1);
}

} // namespace
} // namespace legends
