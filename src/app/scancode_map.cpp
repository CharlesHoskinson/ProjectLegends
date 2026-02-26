// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// SDL3 (USB HID) scancode to AT Set 1 scancode mapping.

#include "app/scancode_map.h"

namespace legends {

// SDL3 uses SDL_Scancode which is USB HID Usage ID.
// DOSBox-X expects AT keyboard Set 1 scancodes.
//
// See: https://wiki.osdev.org/PS/2_Keyboard#Scan_Code_Set_1

ATScancode sdlScancodeToAT(uint16_t sc) {
    // SDL_SCANCODE values (USB HID)
    // Common mapping -- covers letters, numbers, modifiers, function keys, etc.
    static const uint8_t table[] = {
        // 0x00 - 0x03: reserved / error
        0, 0, 0, 0,
        // 0x04 - 0x1D: A-Z
        0x1E, 0x30, 0x2E, 0x20, 0x12, 0x21, 0x22, 0x23,  // A B C D E F G H
        0x17, 0x24, 0x25, 0x26, 0x32, 0x31, 0x18, 0x19,  // I J K L M N O P
        0x10, 0x13, 0x1F, 0x14, 0x16, 0x2F, 0x11, 0x2D,  // Q R S T U V W X
        0x15, 0x2C,                                         // Y Z
        // 0x1E - 0x27: 1-9, 0
        0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09,  // 1 2 3 4 5 6 7 8
        0x0A, 0x0B,                                         // 9 0
        // 0x28 - 0x2C: Enter, Escape, Backspace, Tab, Space
        0x1C, 0x01, 0x0E, 0x0F, 0x39,
        // 0x2D - 0x31: - = [ ] backslash
        0x0C, 0x0D, 0x1A, 0x1B, 0x2B,
        // 0x32: non-US hash (use backslash)
        0x2B,
        // 0x33 - 0x36: ; ' ` , . /
        0x27, 0x28, 0x29, 0x33, 0x34, 0x35,
        // 0x39: Caps Lock
        0x3A,
        // 0x3A - 0x45: F1-F12
        0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41, 0x42,  // F1-F8
        0x43, 0x44, 0x57, 0x58,                             // F9-F12
    };

    // Direct table lookup for 0x00..0x45
    if (sc < sizeof(table)) {
        return {table[sc], false};
    }

    // Extended and non-extended keys mapped individually
    switch (sc) {
        case 0x46: return {0x00, false}; // PrintScreen (complex E0 sequence, skip)
        case 0x47: return {0x46, false}; // Scroll Lock
        case 0x48: return {0x00, false}; // Pause (complex, skip)
        // -- E0-prefixed extended keys --
        case 0x49: return {0x52, true};  // Insert       (E0 52)
        case 0x4A: return {0x47, true};  // Home         (E0 47)
        case 0x4B: return {0x49, true};  // Page Up      (E0 49)
        case 0x4C: return {0x53, true};  // Delete       (E0 53)
        case 0x4D: return {0x4F, true};  // End          (E0 4F)
        case 0x4E: return {0x51, true};  // Page Down    (E0 51)
        case 0x4F: return {0x4D, true};  // Right Arrow  (E0 4D)
        case 0x50: return {0x4B, true};  // Left Arrow   (E0 4B)
        case 0x51: return {0x50, true};  // Down Arrow   (E0 50)
        case 0x52: return {0x48, true};  // Up Arrow     (E0 48)
        case 0x53: return {0x45, false}; // Num Lock
        // Numpad
        case 0x54: return {0x35, true};  // KP /         (E0 35)
        case 0x55: return {0x37, false}; // KP *
        case 0x56: return {0x4A, false}; // KP -
        case 0x57: return {0x4E, false}; // KP +
        case 0x58: return {0x1C, true};  // KP Enter     (E0 1C)
        case 0x59: return {0x4F, false}; // KP 1
        case 0x5A: return {0x50, false}; // KP 2
        case 0x5B: return {0x51, false}; // KP 3
        case 0x5C: return {0x4B, false}; // KP 4
        case 0x5D: return {0x4C, false}; // KP 5
        case 0x5E: return {0x4D, false}; // KP 6
        case 0x5F: return {0x47, false}; // KP 7
        case 0x60: return {0x48, false}; // KP 8
        case 0x61: return {0x49, false}; // KP 9
        case 0x62: return {0x52, false}; // KP 0
        case 0x63: return {0x53, false}; // KP .
        // Modifiers
        case 0xE0: return {0x1D, false}; // Left Ctrl
        case 0xE1: return {0x2A, false}; // Left Shift
        case 0xE2: return {0x38, false}; // Left Alt
        case 0xE3: return {0x00, false}; // Left GUI (no AT equivalent)
        case 0xE4: return {0x1D, true};  // Right Ctrl   (E0 1D)
        case 0xE5: return {0x36, false}; // Right Shift
        case 0xE6: return {0x38, true};  // Right Alt    (E0 38)
        case 0xE7: return {0x00, false}; // Right GUI
        default:   return {0, false};
    }
}

} // namespace legends
