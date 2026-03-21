// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// NEC PC-98 configuration from [pc98] config section.

#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace legends {

class ConfigParser;

/// NEC PC-98 machine configuration loaded from the [pc98] config section.
struct PC98Config {
    bool enabled = false;                   ///< Whether PC-98 mode is active.

    std::string gdc_clock = "default";      ///< GDC clock: "default" (2.5 MHz) or "5mhz".

    std::string sound_board = "auto";       ///< Sound board: "auto", "26k" (PC-9801-26K), or "86" (PC-9801-86).

    bool bus_mouse = true;                  ///< Enable bus mouse support.

    /// Machine type constant passed to legends_config_t.
    static constexpr uint8_t kMachineType = 5;

    /// Load settings from the [pc98] section of a ConfigParser.
    /// @param config  Parsed configuration source.
    void loadFrom(const ConfigParser& config);

    /// Validate GDC clock and sound board settings.
    /// @return true if the configuration is usable.
    bool isValid() const;

    /// Check whether a GDC clock string is valid ("default" or "5mhz").
    /// @param clock  The clock string to validate.
    /// @return true if recognised.
    static bool isValidGDCClock(std::string_view clock);

    /// Check whether a sound board string is valid ("auto", "26k", or "86").
    /// @param board  The sound board string to validate.
    /// @return true if recognised.
    static bool isValidSoundBoard(std::string_view board);
};

} // namespace legends
