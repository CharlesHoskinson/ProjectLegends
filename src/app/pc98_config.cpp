// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// NEC PC-98 configuration implementation.

#include "app/pc98_config.h"
#include "app/config_parser.h"

namespace legends {

void PC98Config::loadFrom(const ConfigParser& config) {
    if (!config.hasSection("pc98")) {
        return;
    }

    enabled = config.getBool("pc98", "pc98", enabled);
    gdc_clock = config.get("pc98", "gdc_clock", gdc_clock);
    sound_board = config.get("pc98", "sound_board", sound_board);
    bus_mouse = config.getBool("pc98", "bus_mouse", bus_mouse);
}

bool PC98Config::isValid() const {
    return isValidGDCClock(gdc_clock) && isValidSoundBoard(sound_board);
}

bool PC98Config::isValidGDCClock(const std::string& clock) {
    return clock == "default" || clock == "5mhz";
}

bool PC98Config::isValidSoundBoard(const std::string& board) {
    return board == "auto" || board == "26k" || board == "86";
}

} // namespace legends
