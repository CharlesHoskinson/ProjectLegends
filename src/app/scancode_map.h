// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// SDL3 (USB HID) scancode to AT Set 1 scancode mapping.
// Extracted from Application for unit testability.

#pragma once

#include <cstdint>

namespace legends {

/// AT Set 1 scancode with extended-key flag.
struct ATScancode {
    uint8_t code;       // AT Set 1 make code
    bool    extended;   // true -> E0-prefixed (use legends_key_event_ext)
};

/// Translate SDL3 (USB HID) scancode to AT Set 1 scancode.
/// Returns {0, false} if no mapping exists.
ATScancode sdlScancodeToAT(uint16_t sdl_scancode);

} // namespace legends
