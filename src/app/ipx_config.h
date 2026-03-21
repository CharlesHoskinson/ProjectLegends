// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// IPX networking configuration from [ipx] config section.

#pragma once

#include <cstdint>
#include <string>

namespace legends {

class ConfigParser;

/// IPX networking configuration loaded from the [ipx] config section.
struct IPXConfig {
    bool enabled = false;       ///< Whether IPX networking is active.
    std::string server;         ///< IPX server hostname or IP address.
    uint16_t port = 213;        ///< Server port (default: 213, the DOSBox IPX port).

    /// Load settings from the [ipx] section of a ConfigParser.
    /// @param config  Parsed configuration source.
    void loadFrom(const ConfigParser& config);

    /// Validate that required fields (server address) are present when enabled.
    /// @return true if the configuration is usable.
    [[nodiscard]] bool isValid() const;
};

} // namespace legends
