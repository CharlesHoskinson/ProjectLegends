// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// JoystickMapper — PAL-to-DOS joystick axis and button mapping.

#include "app/joystick_mapper.h"

#include <algorithm>
#include <cmath>

namespace legends {

void JoystickMapper::setDeadzone(int16_t deadzone) {
    // Clamp to valid range [0, 32767]
    if (deadzone < 0) deadzone = 0;
    deadzone_ = deadzone;
}

int16_t JoystickMapper::deadzone() const {
    return deadzone_;
}

uint8_t JoystickMapper::mapAxis(int16_t pal_value) const {
    // All arithmetic uses int32_t to avoid overflow when multiplying
    // 16-bit axis values by 127/126-step mapping factors.

    // If deadzone covers the entire range, always return center
    if (deadzone_ >= 32767) {
        return 128;
    }

    // Values within deadzone map to center
    if (pal_value > -deadzone_ && pal_value < deadzone_) {
        return 128;
    }

    // At deadzone boundary, also map to center (deadzone is inclusive)
    if (deadzone_ > 0 && (pal_value == deadzone_ || pal_value == -deadzone_)) {
        return 128;
    }

    // If deadzone is zero, do a simple linear map of the full range
    if (deadzone_ == 0) {
        // Map -32768..32767 to 0..255
        // Center (0) must map to exactly 128
        if (pal_value == 0) return 128;
        if (pal_value > 0) {
            // Map 1..32767 to 129..255 (126 steps)
            int32_t result = 129 + ((static_cast<int32_t>(pal_value) - 1) * 126) / 32766;
            return static_cast<uint8_t>(std::clamp(result, int32_t{129}, int32_t{255}));
        } else {
            // Map -32768..-1 to 0..127 (127 steps)
            // -1 → 127, -32768 → 0
            int32_t abs_val = static_cast<int32_t>(-pal_value); // 1..32768
            int32_t result = 127 - ((abs_val - 1) * 127) / 32767;
            return static_cast<uint8_t>(std::clamp(result, int32_t{0}, int32_t{127}));
        }
    }

    // Outside deadzone: linearly remap the remaining range to the DOS half.
    // The deadzone carves out the center, so only (32767 - deadzone_) values
    // remain per side, mapped into 127 DOS steps (0..127 or 129..255).
    if (pal_value > 0) {
        int32_t range_in = 32767 - deadzone_;
        int32_t offset = static_cast<int32_t>(pal_value) - deadzone_;
        // Map offset in [1, range_in] to [129, 255]
        int32_t result = 129 + ((offset - 1) * 126) / (range_in - 1);
        return static_cast<uint8_t>(std::clamp(result, int32_t{129}, int32_t{255}));
    } else {
        // pal_value < -deadzone_
        // Map -(deadzone_+1)..-32768 to 127..0
        int32_t range_in = 32768 - deadzone_;
        int32_t offset = static_cast<int32_t>(-pal_value) - deadzone_;
        // offset in [1, range_in], map to [127, 0]
        int32_t result = 127 - ((offset - 1) * 127) / (range_in - 1);
        return static_cast<uint8_t>(std::clamp(result, int32_t{0}, int32_t{127}));
    }
}

uint8_t JoystickMapper::mapButton(uint8_t pal_button, bool pressed) const {
    if (!pressed) return 0x00;

    uint8_t result = 0;
    // bit 0 of pal_button → DOS button 1 (0x01)
    if (pal_button & 0x01) result |= 0x01;
    // bit 1 of pal_button → DOS button 2 (0x02)
    if (pal_button & 0x02) result |= 0x02;
    return result;
}

JoystickState JoystickMapper::processEvent(int16_t axis_x, int16_t axis_y,
                                           uint8_t pal_buttons) const {
    JoystickState state;
    state.axis_x = mapAxis(axis_x);
    state.axis_y = mapAxis(axis_y);
    state.buttons = mapButton(pal_buttons, true);
    return state;
}

const JoystickState& JoystickMapper::state(uint8_t joystick_id) const {
    // Clamp to valid range
    uint8_t id = (joystick_id > 1) ? 1 : joystick_id;
    return states_[id];
}

void JoystickMapper::update(uint8_t joystick_id, int16_t axis_x,
                            int16_t axis_y, uint8_t pal_buttons) {
    // Clamp to valid range
    uint8_t id = (joystick_id > 1) ? 1 : joystick_id;
    states_[id] = processEvent(axis_x, axis_y, pal_buttons);
}

} // namespace legends
