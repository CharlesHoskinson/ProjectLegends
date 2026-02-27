// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for the extracted hotkey dispatcher — pure-function matching.

#include <gtest/gtest.h>
#include "app/hotkey_dispatcher.h"

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// F12 — OpenMenu
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, F12_OpenMenu) {
    auto r = matchHotkey(0x45, 0, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::OpenMenu);
}

TEST(HotkeyDispatcherTest, F12_OpenMenu_WithModifiers) {
    // F12 matches regardless of modifiers
    auto r = matchHotkey(0x45, kHkModLCtrl, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::OpenMenu);
}

// ═══════════════════════════════════════════════════════════════════════════
// Alt+Pause — TogglePause
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, AltPause_TogglePause) {
    auto r = matchHotkey(0x48, kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::TogglePause);
}

TEST(HotkeyDispatcherTest, AltPause_RAlt) {
    auto r = matchHotkey(0x48, kHkModRAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::TogglePause);
}

TEST(HotkeyDispatcherTest, PauseWithoutAlt_NoMatch) {
    auto r = matchHotkey(0x48, 0, false);
    EXPECT_FALSE(r.matched);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+Alt+Delete — Reset
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlAltDelete_Reset) {
    auto r = matchHotkey(0x4C, kHkModLCtrl | kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::Reset);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+F5 — Screenshot
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlF5_Screenshot) {
    auto r = matchHotkey(0x3E, kHkModLCtrl, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::Screenshot);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+F1 — OpenMapper
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlF1_OpenMapper) {
    auto r = matchHotkey(0x3A, kHkModLCtrl, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::OpenMapper);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+Shift+V — ClipboardPaste
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlShiftV_ClipboardPaste) {
    auto r = matchHotkey(0x19, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ClipboardPaste);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+Shift+F1..F9 — SaveState with correct slot param
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlShiftF1_SaveState_Slot1) {
    auto r = matchHotkey(0x3A, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 1);
}

TEST(HotkeyDispatcherTest, CtrlShiftF5_IsVideoCapture_NotSaveState) {
    // F5 (0x3E) is within the F1-F9 range but is reserved for ToggleVideoCapture
    auto r = matchHotkey(0x3E, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ToggleVideoCapture);
    EXPECT_NE(r.action, Action::SaveState);
}

TEST(HotkeyDispatcherTest, CtrlShiftF9_SaveState_Slot9) {
    auto r = matchHotkey(0x42, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 9);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+Alt+F1..F9 — LoadState with correct slot param
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlAltF1_LoadState_Slot1) {
    auto r = matchHotkey(0x3A, kHkModLCtrl | kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::LoadState);
    EXPECT_EQ(r.param, 1);
}

TEST(HotkeyDispatcherTest, CtrlAltF5_LoadState_Slot5) {
    auto r = matchHotkey(0x3E, kHkModLCtrl | kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::LoadState);
    EXPECT_EQ(r.param, 5);
}

TEST(HotkeyDispatcherTest, CtrlAltF9_LoadState_Slot9) {
    auto r = matchHotkey(0x42, kHkModLCtrl | kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::LoadState);
    EXPECT_EQ(r.param, 9);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+F10 — ReleaseMouseCapture (conditional on mouse_captured)
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlF10_ReleaseMouseCapture_WhenCaptured) {
    auto r = matchHotkey(0x43, kHkModLCtrl, true);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ReleaseMouseCapture);
}

TEST(HotkeyDispatcherTest, CtrlF10_NoMatch_WhenNotCaptured) {
    auto r = matchHotkey(0x43, kHkModLCtrl, false);
    EXPECT_FALSE(r.matched);
}

// ═══════════════════════════════════════════════════════════════════════════
// Volume: Ctrl+Up, Ctrl+Down, Ctrl+M
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlUp_VolumeUp) {
    auto r = matchHotkey(0x52, kHkModLCtrl, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::VolumeUp);
}

TEST(HotkeyDispatcherTest, CtrlDown_VolumeDown) {
    auto r = matchHotkey(0x51, kHkModLCtrl, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::VolumeDown);
}

TEST(HotkeyDispatcherTest, CtrlM_ToggleMute) {
    auto r = matchHotkey(0x10, kHkModLCtrl, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ToggleMute);
}

// ═══════════════════════════════════════════════════════════════════════════
// Alt+Enter — ToggleFullscreen
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, AltEnter_ToggleFullscreen) {
    auto r = matchHotkey(0x28, kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ToggleFullscreen);
}

// ═══════════════════════════════════════════════════════════════════════════
// No match cases
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, UnrecognizedScancode_NoMatch) {
    auto r = matchHotkey(0xFE, 0, false);
    EXPECT_FALSE(r.matched);
}

TEST(HotkeyDispatcherTest, ModifierOnlyKeyPress_NoMatch) {
    // Left Ctrl key itself (0xE0)
    auto r = matchHotkey(0xE0, kHkModLCtrl, false);
    EXPECT_FALSE(r.matched);
}

TEST(HotkeyDispatcherTest, LetterKeyWithoutModifiers_NoMatch) {
    auto r = matchHotkey(0x04, 0, false); // 'A'
    EXPECT_FALSE(r.matched);
}

// ═══════════════════════════════════════════════════════════════════════════
// Priority checks: Ctrl+Shift+F1 is SaveState, not OpenMapper
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlShiftF1_IsSaveState_NotOpenMapper) {
    auto r = matchHotkey(0x3A, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_NE(r.action, Action::OpenMapper);
}

TEST(HotkeyDispatcherTest, CtrlAltF1_IsLoadState_NotOpenMapper) {
    auto r = matchHotkey(0x3A, kHkModLCtrl | kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::LoadState);
    EXPECT_NE(r.action, Action::OpenMapper);
}

// ═══════════════════════════════════════════════════════════════════════════
// Modifier variants: LCtrl vs RCtrl, LShift vs RShift, LAlt vs RAlt
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, RCtrl_VolumeUp) {
    auto r = matchHotkey(0x52, kHkModRCtrl, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::VolumeUp);
}

TEST(HotkeyDispatcherTest, RShift_CtrlRShiftF1_SaveState) {
    auto r = matchHotkey(0x3A, kHkModLCtrl | kHkModRShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
}

TEST(HotkeyDispatcherTest, RAlt_CtrlRAltF1_LoadState) {
    auto r = matchHotkey(0x3A, kHkModLCtrl | kHkModRAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::LoadState);
}

TEST(HotkeyDispatcherTest, RAlt_Pause_TogglePause) {
    auto r = matchHotkey(0x48, kHkModRAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::TogglePause);
}

// ═══════════════════════════════════════════════════════════════════════════
// Additional SaveState/LoadState slot parameter checks
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlShiftF2_SaveState_Slot2) {
    auto r = matchHotkey(0x3B, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 2);
}

TEST(HotkeyDispatcherTest, CtrlShiftF3_SaveState_Slot3) {
    auto r = matchHotkey(0x3C, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 3);
}

TEST(HotkeyDispatcherTest, CtrlAltF2_LoadState_Slot2) {
    auto r = matchHotkey(0x3B, kHkModLCtrl | kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::LoadState);
    EXPECT_EQ(r.param, 2);
}

TEST(HotkeyDispatcherTest, CtrlAltF3_LoadState_Slot3) {
    auto r = matchHotkey(0x3C, kHkModLCtrl | kHkModLAlt, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::LoadState);
    EXPECT_EQ(r.param, 3);
}

TEST(HotkeyDispatcherTest, CtrlShiftF4_SaveState_Slot4) {
    auto r = matchHotkey(0x3D, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 4);
}

TEST(HotkeyDispatcherTest, CtrlShiftF6_SaveState_Slot6) {
    auto r = matchHotkey(0x3F, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 6);
}

TEST(HotkeyDispatcherTest, CtrlShiftF7_SaveState_Slot7) {
    auto r = matchHotkey(0x40, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 7);
}

TEST(HotkeyDispatcherTest, CtrlShiftF8_SaveState_Slot8) {
    auto r = matchHotkey(0x41, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::SaveState);
    EXPECT_EQ(r.param, 8);
}

// ═══════════════════════════════════════════════════════════════════════════
// Ctrl+Shift+F5 — ToggleVideoCapture (priority over Ctrl+F5)
// ═══════════════════════════════════════════════════════════════════════════

TEST(HotkeyDispatcherTest, CtrlShiftF5_ToggleVideoCapture) {
    auto r = matchHotkey(0x3E, kHkModLCtrl | kHkModLShift, false);
    EXPECT_TRUE(r.matched);
    EXPECT_EQ(r.action, Action::ToggleVideoCapture);
}

TEST(HotkeyDispatcherTest, CtrlShiftF5_TakesPriorityOverCtrlF5) {
    // Ctrl+Shift+F5 = ToggleVideoCapture, NOT Screenshot
    auto video = matchHotkey(0x3E, kHkModLCtrl | kHkModLShift, false);
    EXPECT_EQ(video.action, Action::ToggleVideoCapture);

    // Ctrl+F5 (without shift) = Screenshot
    auto screenshot = matchHotkey(0x3E, kHkModLCtrl, false);
    EXPECT_EQ(screenshot.action, Action::Screenshot);
}

} // namespace
} // namespace legends
