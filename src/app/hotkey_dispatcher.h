// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// HotkeyDispatcher — pure-function hotkey matching extracted from Application.
// Testable without window/context/engine dependencies.

#pragma once

#include "app/action_bus.h"
#include <cstdint>

namespace legends {

struct HotkeyResult {
    Action action;
    int param;
    bool matched;
};

// Modifier bitmask constants (mirrored from Application for standalone use)
constexpr uint8_t kHkModLCtrl  = 0x01;
constexpr uint8_t kHkModRCtrl  = 0x02;
constexpr uint8_t kHkModCtrl   = kHkModLCtrl | kHkModRCtrl;
constexpr uint8_t kHkModLShift = 0x04;
constexpr uint8_t kHkModRShift = 0x08;
constexpr uint8_t kHkModShift  = kHkModLShift | kHkModRShift;
constexpr uint8_t kHkModLAlt   = 0x10;
constexpr uint8_t kHkModRAlt   = 0x20;
constexpr uint8_t kHkModAlt    = kHkModLAlt | kHkModRAlt;

/// Match a scancode + modifier state against the hotkey table.
/// Returns {action, param, true} if a hotkey matched, or {*, *, false} otherwise.
[[nodiscard]] HotkeyResult matchHotkey(uint16_t scancode, uint8_t modifiers, bool mouse_captured);

} // namespace legends
