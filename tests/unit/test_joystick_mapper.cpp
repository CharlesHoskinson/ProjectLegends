// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for JoystickMapper — PAL-to-DOS axis/button mapping with deadzone.

#include <gtest/gtest.h>
#include "app/joystick_mapper.h"

#include <cstdint>
#include <limits>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Deadzone configuration
// ═══════════════════════════════════════════════════════════════════════════

TEST(JoystickMapperTest, DefaultDeadzoneIs8000) {
    JoystickMapper mapper;
    EXPECT_EQ(mapper.deadzone(), 8000);
}

TEST(JoystickMapperTest, SetGetDeadzone) {
    JoystickMapper mapper;
    mapper.setDeadzone(5000);
    EXPECT_EQ(mapper.deadzone(), 5000);
}

TEST(JoystickMapperTest, DeadzoneNegativeClampedToZero) {
    JoystickMapper mapper;
    mapper.setDeadzone(-100);
    EXPECT_EQ(mapper.deadzone(), 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// mapAxis — center, min, max
// ═══════════════════════════════════════════════════════════════════════════

TEST(JoystickMapperTest, MapAxisCenter) {
    JoystickMapper mapper;
    // PAL center (0) should map to DOS center (128)
    EXPECT_EQ(mapper.mapAxis(0), 128);
}

TEST(JoystickMapperTest, MapAxisMax) {
    JoystickMapper mapper;
    // PAL max (32767) should map to DOS max (255)
    EXPECT_EQ(mapper.mapAxis(32767), 255);
}

TEST(JoystickMapperTest, MapAxisMin) {
    JoystickMapper mapper;
    // PAL min (-32768) should map to DOS min (0)
    EXPECT_EQ(mapper.mapAxis(std::numeric_limits<int16_t>::min()), 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// mapAxis — deadzone behavior
// ═══════════════════════════════════════════════════════════════════════════

TEST(JoystickMapperTest, MapAxisWithinDeadzoneReturnsCenter) {
    JoystickMapper mapper;
    mapper.setDeadzone(8000);
    // Values within deadzone should return center (128)
    EXPECT_EQ(mapper.mapAxis(100), 128);
    EXPECT_EQ(mapper.mapAxis(-100), 128);
    EXPECT_EQ(mapper.mapAxis(7999), 128);
    EXPECT_EQ(mapper.mapAxis(-7999), 128);
}

TEST(JoystickMapperTest, MapAxisJustOutsidePositiveDeadzone) {
    JoystickMapper mapper;
    mapper.setDeadzone(8000);
    // Just outside deadzone should NOT be 128
    uint8_t val = mapper.mapAxis(8001);
    EXPECT_GT(val, 128);
}

TEST(JoystickMapperTest, MapAxisJustOutsideNegativeDeadzone) {
    JoystickMapper mapper;
    mapper.setDeadzone(8000);
    // Just outside negative deadzone should be < 128
    uint8_t val = mapper.mapAxis(-8001);
    EXPECT_LT(val, 128);
}

TEST(JoystickMapperTest, MapAxisAtDeadzoneBoundary) {
    JoystickMapper mapper;
    mapper.setDeadzone(8000);
    // At exactly the deadzone boundary, should be center
    EXPECT_EQ(mapper.mapAxis(8000), 128);
    EXPECT_EQ(mapper.mapAxis(-8000), 128);
}

TEST(JoystickMapperTest, DeadzoneZeroMeansNoDeadzone) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    // With zero deadzone, small values should NOT be center
    // 0 itself is center
    EXPECT_EQ(mapper.mapAxis(0), 128);
    // Small positive value should be > 128
    uint8_t pos = mapper.mapAxis(1000);
    EXPECT_GT(pos, 128);
    // Small negative value should be < 128
    uint8_t neg = mapper.mapAxis(-1000);
    EXPECT_LT(neg, 128);
}

TEST(JoystickMapperTest, DeadzoneMaxMeansAlwaysCenter) {
    JoystickMapper mapper;
    mapper.setDeadzone(32767);
    // Maximum deadzone means everything maps to center
    EXPECT_EQ(mapper.mapAxis(0), 128);
    EXPECT_EQ(mapper.mapAxis(32767), 128);
    EXPECT_EQ(mapper.mapAxis(-32768), 128);
    EXPECT_EQ(mapper.mapAxis(16000), 128);
    EXPECT_EQ(mapper.mapAxis(-16000), 128);
}

// ═══════════════════════════════════════════════════════════════════════════
// mapAxis — INT16 edge cases
// ═══════════════════════════════════════════════════════════════════════════

TEST(JoystickMapperTest, INT16_MIN_EdgeCase) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    // INT16_MIN (-32768) should map to 0
    EXPECT_EQ(mapper.mapAxis(std::numeric_limits<int16_t>::min()), 0);
}

TEST(JoystickMapperTest, INT16_MAX_EdgeCase) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    // INT16_MAX (32767) should map to 255
    EXPECT_EQ(mapper.mapAxis(std::numeric_limits<int16_t>::max()), 255);
}

// ═══════════════════════════════════════════════════════════════════════════
// mapButton
// ═══════════════════════════════════════════════════════════════════════════

TEST(JoystickMapperTest, MapButtonBit0Pressed) {
    JoystickMapper mapper;
    EXPECT_EQ(mapper.mapButton(0x01, true), 0x01);
}

TEST(JoystickMapperTest, MapButtonBit1Pressed) {
    JoystickMapper mapper;
    EXPECT_EQ(mapper.mapButton(0x02, true), 0x02);
}

TEST(JoystickMapperTest, MapButtonBothPressed) {
    JoystickMapper mapper;
    EXPECT_EQ(mapper.mapButton(0x03, true), 0x03);
}

TEST(JoystickMapperTest, MapButtonNonePressed) {
    JoystickMapper mapper;
    // Even with bits set, pressed=false should return 0
    EXPECT_EQ(mapper.mapButton(0x03, false), 0x00);
}

TEST(JoystickMapperTest, MapButtonZeroBitmask) {
    JoystickMapper mapper;
    EXPECT_EQ(mapper.mapButton(0x00, true), 0x00);
}

// ═══════════════════════════════════════════════════════════════════════════
// processEvent
// ═══════════════════════════════════════════════════════════════════════════

TEST(JoystickMapperTest, ProcessEventCombinesAxisAndButtons) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    auto state = mapper.processEvent(32767, -32768, 0x03);
    EXPECT_EQ(state.axis_x, 255);
    EXPECT_EQ(state.axis_y, 0);
    EXPECT_EQ(state.buttons, 0x03);
}

TEST(JoystickMapperTest, ProcessEventWithDeadzone) {
    JoystickMapper mapper;
    mapper.setDeadzone(8000);
    // Axes within deadzone should be center
    auto state = mapper.processEvent(100, -50, 0x01);
    EXPECT_EQ(state.axis_x, 128);
    EXPECT_EQ(state.axis_y, 128);
    EXPECT_EQ(state.buttons, 0x01);
}

// ═══════════════════════════════════════════════════════════════════════════
// update / state
// ═══════════════════════════════════════════════════════════════════════════

TEST(JoystickMapperTest, StateDefaultsToCenter) {
    JoystickMapper mapper;
    auto& s0 = mapper.state(0);
    EXPECT_EQ(s0.axis_x, 128);
    EXPECT_EQ(s0.axis_y, 128);
    EXPECT_EQ(s0.buttons, 0);

    auto& s1 = mapper.state(1);
    EXPECT_EQ(s1.axis_x, 128);
    EXPECT_EQ(s1.axis_y, 128);
    EXPECT_EQ(s1.buttons, 0);
}

TEST(JoystickMapperTest, UpdateStoresState) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    mapper.update(0, 32767, -32768, 0x01);

    auto& s = mapper.state(0);
    EXPECT_EQ(s.axis_x, 255);
    EXPECT_EQ(s.axis_y, 0);
    EXPECT_EQ(s.buttons, 0x01);
}

TEST(JoystickMapperTest, StateRetrievalForJoystick0And1) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    mapper.update(0, 32767, 0, 0x01);
    mapper.update(1, -32768, 0, 0x02);

    auto& s0 = mapper.state(0);
    EXPECT_EQ(s0.axis_x, 255);
    EXPECT_EQ(s0.buttons, 0x01);

    auto& s1 = mapper.state(1);
    EXPECT_EQ(s1.axis_x, 0);
    EXPECT_EQ(s1.buttons, 0x02);
}

TEST(JoystickMapperTest, MultipleUpdatesOverride) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    mapper.update(0, 32767, 32767, 0x03);
    mapper.update(0, 0, 0, 0x00);

    auto& s = mapper.state(0);
    EXPECT_EQ(s.axis_x, 128);
    EXPECT_EQ(s.axis_y, 128);
    EXPECT_EQ(s.buttons, 0x00);
}

TEST(JoystickMapperTest, JoystickIdClampedTo0Or1) {
    JoystickMapper mapper;
    mapper.setDeadzone(0);
    // ID > 1 should be clamped to 1
    mapper.update(5, 32767, 32767, 0x03);

    auto& s1 = mapper.state(1);
    EXPECT_EQ(s1.axis_x, 255);
    EXPECT_EQ(s1.axis_y, 255);
    EXPECT_EQ(s1.buttons, 0x03);

    // state() also clamps
    auto& s_clamped = mapper.state(200);
    EXPECT_EQ(s_clamped.axis_x, 255);
}

} // namespace
} // namespace legends
