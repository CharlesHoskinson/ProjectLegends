// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// JoystickMapper — maps PAL joystick axis/button events to DOS-era values.
// Supports two joysticks with configurable deadzone and linear axis mapping.

#pragma once

#include <cstdint>
#include <array>

namespace legends {

/// State of a single joystick in DOS-era format.
struct JoystickState {
    uint8_t axis_x = 128;   ///< X axis position, 0..255 (128 = center)
    uint8_t axis_y = 128;   ///< Y axis position, 0..255 (128 = center)
    uint8_t buttons = 0;    ///< Button bitmask (bit 0 = btn1, bit 1 = btn2)
};

class JoystickMapper {
public:
    /// Set the axis deadzone threshold (clamped to [0, 32767]).
    /// @param deadzone  Values within +/- this range map to center (128).
    void setDeadzone(int16_t deadzone);

    /// @return Current deadzone threshold.
    int16_t deadzone() const;

    /// Map a PAL axis value (-32768..32767) to DOS range (0..255) with deadzone.
    /// Values within the deadzone map to center (128). Outside the deadzone,
    /// the remaining range is linearly mapped using int32_t intermediates.
    /// @param pal_value  Raw PAL axis value
    /// @return DOS-range axis value (0..255)
    uint8_t mapAxis(int16_t pal_value) const;

    /// Map a PAL button bitmask to a DOS button bitmask.
    /// Returns the accumulated DOS button bits when @p pressed is true,
    /// or 0x00 when @p pressed is false (all buttons released).
    /// Bit 0 of @p pal_button maps to DOS button 1 (0x01),
    /// bit 1 maps to DOS button 2 (0x02).
    /// @param pal_button  PAL-layer button bitmask
    /// @param pressed     true if buttons are held, false if released
    /// @return DOS-style button bitmask (0x00 when released)
    uint8_t mapButton(uint8_t pal_button, bool pressed) const;

    /// Process a complete joystick event and return the resulting DOS state.
    /// @param axis_x       PAL X axis value (-32768..32767)
    /// @param axis_y       PAL Y axis value (-32768..32767)
    /// @param pal_buttons  PAL button bitmask
    /// @return Translated JoystickState in DOS format.
    JoystickState processEvent(int16_t axis_x, int16_t axis_y,
                               uint8_t pal_buttons) const;

    /// Get the current stored state for a joystick.
    /// @param joystick_id  Joystick index (clamped to 0-1).
    /// @return Reference to the stored JoystickState.
    const JoystickState& state(uint8_t joystick_id) const;

    /// Update the stored state for a joystick from a PAL event.
    /// @param joystick_id  Joystick index (clamped to 0-1).
    /// @param axis_x       PAL X axis value
    /// @param axis_y       PAL Y axis value
    /// @param pal_buttons  PAL button bitmask
    void update(uint8_t joystick_id, int16_t axis_x, int16_t axis_y,
                uint8_t pal_buttons);

private:
    int16_t deadzone_ = 8000;
    std::array<JoystickState, 2> states_{};
};

} // namespace legends
