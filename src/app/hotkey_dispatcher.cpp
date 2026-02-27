// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// HotkeyDispatcher — extracted hotkey matching logic.

#include "app/hotkey_dispatcher.h"

namespace legends {

HotkeyResult matchHotkey(uint16_t scancode, uint8_t modifiers, bool mouse_captured) {
    bool ctrl  = (modifiers & kHkModCtrl) != 0;
    bool shift = (modifiers & kHkModShift) != 0;
    bool alt   = (modifiers & kHkModAlt) != 0;

    // F12 — toggle overlay menu (no modifiers required)
    if (scancode == 0x45) {
        return {Action::OpenMenu, 0, true};
    }

    // Alt+Pause — toggle pause (SDL Pause = 0x48)
    if (alt && !ctrl && scancode == 0x48) {
        return {Action::TogglePause, 0, true};
    }

    // Ctrl+Alt+Delete — reset (SDL Delete = 0x4C)
    if (ctrl && alt && scancode == 0x4C) {
        return {Action::Reset, 0, true};
    }

    // Ctrl+Shift+F5 — toggle video capture (SDL F5 = 0x3E)
    // Must be checked BEFORE the Ctrl+Shift+F1..F9 range to avoid being shadowed
    if (ctrl && shift && !alt && scancode == 0x3E) {
        return {Action::ToggleVideoCapture, 0, true};
    }

    // Ctrl+Shift+F1..F9 — save state (slots 1-9)
    // Must be checked BEFORE Ctrl+F1 (OpenMapper) to ensure priority
    if (ctrl && shift && !alt &&
        scancode >= 0x3A && scancode <= 0x42) {
        int slot = static_cast<int>(scancode - 0x3A + 1);
        return {Action::SaveState, slot, true};
    }

    // Ctrl+Alt+F1..F9 — load state (slots 1-9)
    // Must be checked BEFORE Ctrl+F1 (OpenMapper) to ensure priority
    if (ctrl && alt && !shift &&
        scancode >= 0x3A && scancode <= 0x42) {
        int slot = static_cast<int>(scancode - 0x3A + 1);
        return {Action::LoadState, slot, true};
    }

    // Ctrl+F5 — screenshot (SDL F5 = 0x3E)
    if (ctrl && !shift && !alt && scancode == 0x3E) {
        return {Action::Screenshot, 0, true};
    }

    // Ctrl+F1 — open mapper (SDL F1 = 0x3A)
    if (ctrl && !shift && !alt && scancode == 0x3A) {
        return {Action::OpenMapper, 0, true};
    }

    // Ctrl+Shift+V — clipboard paste (SDL V = 0x19)
    if (ctrl && shift && !alt && scancode == 0x19) {
        return {Action::ClipboardPaste, 0, true};
    }

    // Ctrl+F10 — release mouse capture (only when captured)
    if (ctrl && !shift && !alt && scancode == 0x43 && mouse_captured) {
        return {Action::ReleaseMouseCapture, 0, true};
    }

    // Alt+Enter — toggle fullscreen (SDL Enter = 0x28)
    if (alt && !ctrl && !shift && scancode == 0x28) {
        return {Action::ToggleFullscreen, 0, true};
    }

    // Ctrl+Shift+S — toggle shaders (SDL S = 0x16)
    if (ctrl && shift && !alt && scancode == 0x16) {
        return {Action::ToggleShaders, 0, true};
    }

    // Ctrl+F12 — toggle AI panel (SDL F12 = 0x45... but F12 is already OpenMenu)
    // Use Ctrl+Shift+A instead (SDL A = 0x04)
    if (ctrl && shift && !alt && scancode == 0x04) {
        return {Action::ToggleAIPanel, 0, true};
    }

    // Volume: Ctrl+Up / Ctrl+Down / Ctrl+M
    if (ctrl && !shift && !alt) {
        if (scancode == 0x52) { // Up arrow
            return {Action::VolumeUp, 0, true};
        }
        if (scancode == 0x51) { // Down arrow
            return {Action::VolumeDown, 0, true};
        }
        if (scancode == 0x10) { // M key
            return {Action::ToggleMute, 0, true};
        }
    }

    return {Action::Quit, 0, false}; // no match
}

} // namespace legends
