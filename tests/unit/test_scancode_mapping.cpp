// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for SDL3 -> AT Set 1 scancode mapping.

#include <gtest/gtest.h>
#include "app/scancode_map.h"

#include <string>
#include <tuple>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Parameterized test covering ~55 table entries
// ═══════════════════════════════════════════════════════════════════════════

struct ScancodeTestCase {
    uint16_t sdl;          // SDL3 / USB HID scancode
    uint8_t  expected_at;  // Expected AT Set 1 code
    bool     extended;     // Expected extended flag
    const char* name;      // Description
};

class ScancodeMapTest : public ::testing::TestWithParam<ScancodeTestCase> {};

TEST_P(ScancodeMapTest, MapsCorrectly) {
    auto [sdl, expected_at, extended, name] = GetParam();
    auto result = sdlScancodeToAT(sdl);
    EXPECT_EQ(result.code, expected_at) << "SDL 0x" << std::hex << sdl << " (" << name << ")";
    EXPECT_EQ(result.extended, extended) << "SDL 0x" << std::hex << sdl << " (" << name << ")";
}

// clang-format off
INSTANTIATE_TEST_SUITE_P(Letters, ScancodeMapTest, ::testing::Values(
    ScancodeTestCase{0x04, 0x1E, false, "A"},
    ScancodeTestCase{0x05, 0x30, false, "B"},
    ScancodeTestCase{0x06, 0x2E, false, "C"},
    ScancodeTestCase{0x07, 0x20, false, "D"},
    ScancodeTestCase{0x08, 0x12, false, "E"},
    ScancodeTestCase{0x09, 0x21, false, "F"},
    ScancodeTestCase{0x0A, 0x22, false, "G"},
    ScancodeTestCase{0x0B, 0x23, false, "H"},
    ScancodeTestCase{0x0C, 0x17, false, "I"},
    ScancodeTestCase{0x0D, 0x24, false, "J"},
    ScancodeTestCase{0x0E, 0x25, false, "K"},
    ScancodeTestCase{0x0F, 0x26, false, "L"},
    ScancodeTestCase{0x10, 0x32, false, "M"},
    ScancodeTestCase{0x11, 0x31, false, "N"},
    ScancodeTestCase{0x12, 0x18, false, "O"},
    ScancodeTestCase{0x13, 0x19, false, "P"},
    ScancodeTestCase{0x14, 0x10, false, "Q"},
    ScancodeTestCase{0x15, 0x13, false, "R"},
    ScancodeTestCase{0x16, 0x1F, false, "S"},
    ScancodeTestCase{0x17, 0x14, false, "T"},
    ScancodeTestCase{0x18, 0x16, false, "U"},
    ScancodeTestCase{0x19, 0x2F, false, "V"},
    ScancodeTestCase{0x1A, 0x11, false, "W"},
    ScancodeTestCase{0x1B, 0x2D, false, "X"},
    ScancodeTestCase{0x1C, 0x15, false, "Y"},
    ScancodeTestCase{0x1D, 0x2C, false, "Z"}
));

INSTANTIATE_TEST_SUITE_P(Numbers, ScancodeMapTest, ::testing::Values(
    ScancodeTestCase{0x1E, 0x02, false, "1"},
    ScancodeTestCase{0x1F, 0x03, false, "2"},
    ScancodeTestCase{0x20, 0x04, false, "3"},
    ScancodeTestCase{0x21, 0x05, false, "4"},
    ScancodeTestCase{0x22, 0x06, false, "5"},
    ScancodeTestCase{0x23, 0x07, false, "6"},
    ScancodeTestCase{0x24, 0x08, false, "7"},
    ScancodeTestCase{0x25, 0x09, false, "8"},
    ScancodeTestCase{0x26, 0x0A, false, "9"},
    ScancodeTestCase{0x27, 0x0B, false, "0"}
));

INSTANTIATE_TEST_SUITE_P(Symbols, ScancodeMapTest, ::testing::Values(
    ScancodeTestCase{0x28, 0x1C, false, "Enter"},
    ScancodeTestCase{0x29, 0x01, false, "Escape"},
    ScancodeTestCase{0x2A, 0x0E, false, "Backspace"},
    ScancodeTestCase{0x2B, 0x0F, false, "Tab"},
    ScancodeTestCase{0x2C, 0x39, false, "Space"},
    ScancodeTestCase{0x2D, 0x0C, false, "Minus"},
    ScancodeTestCase{0x2E, 0x0D, false, "Equals"},
    ScancodeTestCase{0x2F, 0x1A, false, "LeftBracket"},
    ScancodeTestCase{0x30, 0x1B, false, "RightBracket"},
    ScancodeTestCase{0x31, 0x2B, false, "Backslash"}
));

INSTANTIATE_TEST_SUITE_P(FunctionKeys, ScancodeMapTest, ::testing::Values(
    ScancodeTestCase{0x3A, 0x3B, false, "F1"},
    ScancodeTestCase{0x3B, 0x3C, false, "F2"},
    ScancodeTestCase{0x3C, 0x3D, false, "F3"},
    ScancodeTestCase{0x3D, 0x3E, false, "F4"},
    ScancodeTestCase{0x3E, 0x3F, false, "F5"},
    ScancodeTestCase{0x3F, 0x40, false, "F6"},
    ScancodeTestCase{0x40, 0x41, false, "F7"},
    ScancodeTestCase{0x41, 0x42, false, "F8"},
    ScancodeTestCase{0x42, 0x43, false, "F9"},
    ScancodeTestCase{0x43, 0x44, false, "F10"},
    ScancodeTestCase{0x44, 0x57, false, "F11"},
    ScancodeTestCase{0x45, 0x58, false, "F12"}
));

INSTANTIATE_TEST_SUITE_P(NavKeys, ScancodeMapTest, ::testing::Values(
    ScancodeTestCase{0x49, 0x52, true, "Insert"},
    ScancodeTestCase{0x4A, 0x47, true, "Home"},
    ScancodeTestCase{0x4B, 0x49, true, "PageUp"},
    ScancodeTestCase{0x4C, 0x53, true, "Delete"},
    ScancodeTestCase{0x4D, 0x4F, true, "End"},
    ScancodeTestCase{0x4E, 0x51, true, "PageDown"},
    ScancodeTestCase{0x4F, 0x4D, true, "Right"},
    ScancodeTestCase{0x50, 0x4B, true, "Left"},
    ScancodeTestCase{0x51, 0x50, true, "Down"},
    ScancodeTestCase{0x52, 0x48, true, "Up"}
));

INSTANTIATE_TEST_SUITE_P(Numpad, ScancodeMapTest, ::testing::Values(
    ScancodeTestCase{0x54, 0x35, true,  "KP_Divide"},
    ScancodeTestCase{0x55, 0x37, false, "KP_Multiply"},
    ScancodeTestCase{0x56, 0x4A, false, "KP_Minus"},
    ScancodeTestCase{0x57, 0x4E, false, "KP_Plus"},
    ScancodeTestCase{0x58, 0x1C, true,  "KP_Enter"},
    ScancodeTestCase{0x59, 0x4F, false, "KP_1"},
    ScancodeTestCase{0x62, 0x52, false, "KP_0"},
    ScancodeTestCase{0x63, 0x53, false, "KP_Dot"}
));

INSTANTIATE_TEST_SUITE_P(Modifiers, ScancodeMapTest, ::testing::Values(
    ScancodeTestCase{0xE0, 0x1D, false, "LCtrl"},
    ScancodeTestCase{0xE1, 0x2A, false, "LShift"},
    ScancodeTestCase{0xE2, 0x38, false, "LAlt"},
    ScancodeTestCase{0xE4, 0x1D, true,  "RCtrl"},
    ScancodeTestCase{0xE5, 0x36, false, "RShift"},
    ScancodeTestCase{0xE6, 0x38, true,  "RAlt"}
));
// clang-format on

// ═══════════════════════════════════════════════════════════════════════════
// Unmapped keys
// ═══════════════════════════════════════════════════════════════════════════

TEST(ScancodeMapStandalone, UnmappedReturnsZero) {
    auto at = sdlScancodeToAT(0xFF);
    EXPECT_EQ(at.code, 0);
    EXPECT_FALSE(at.extended);
}

TEST(ScancodeMapStandalone, ReservedCodesReturnZero) {
    for (uint16_t sc = 0x00; sc <= 0x03; ++sc) {
        auto at = sdlScancodeToAT(sc);
        EXPECT_EQ(at.code, 0) << "SDL 0x" << std::hex << sc;
    }
}

TEST(ScancodeMapStandalone, PauseReturnsZero) {
    auto at = sdlScancodeToAT(0x48); // Pause
    EXPECT_EQ(at.code, 0);
}

TEST(ScancodeMapStandalone, PrintScreenReturnsZero) {
    auto at = sdlScancodeToAT(0x46); // PrintScreen
    EXPECT_EQ(at.code, 0);
}

TEST(ScancodeMapStandalone, GUIKeysReturnZero) {
    auto lGUI = sdlScancodeToAT(0xE3);
    auto rGUI = sdlScancodeToAT(0xE7);
    EXPECT_EQ(lGUI.code, 0);
    EXPECT_EQ(rGUI.code, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Extended flag verification
// ═══════════════════════════════════════════════════════════════════════════

TEST(ScancodeMapStandalone, AllNavKeysAreExtended) {
    // Insert, Home, PageUp, Delete, End, PageDown, Right, Left, Down, Up
    for (uint16_t sc = 0x49; sc <= 0x52; ++sc) {
        auto at = sdlScancodeToAT(sc);
        EXPECT_TRUE(at.extended) << "Nav key SDL 0x" << std::hex << sc << " should be extended";
    }
}

TEST(ScancodeMapStandalone, RCtrlIsExtended) {
    auto at = sdlScancodeToAT(0xE4);
    EXPECT_TRUE(at.extended);
}

TEST(ScancodeMapStandalone, RAltIsExtended) {
    auto at = sdlScancodeToAT(0xE6);
    EXPECT_TRUE(at.extended);
}

TEST(ScancodeMapStandalone, LCtrlNotExtended) {
    auto at = sdlScancodeToAT(0xE0);
    EXPECT_FALSE(at.extended);
}

TEST(ScancodeMapStandalone, KPDivideExtended) {
    auto at = sdlScancodeToAT(0x54);
    EXPECT_TRUE(at.extended);
}

TEST(ScancodeMapStandalone, KPEnterExtended) {
    auto at = sdlScancodeToAT(0x58);
    EXPECT_TRUE(at.extended);
}

TEST(ScancodeMapStandalone, KPMultiplyNotExtended) {
    auto at = sdlScancodeToAT(0x55);
    EXPECT_FALSE(at.extended);
}

} // namespace
} // namespace legends
