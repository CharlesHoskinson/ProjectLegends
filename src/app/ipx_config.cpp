// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// IPX networking configuration implementation.

#include "app/ipx_config.h"
#include "app/config_parser.h"

#include <legends/gsl.hpp>

namespace legends {

void IPXConfig::loadFrom(const ConfigParser& config) {
    if (!config.hasSection("ipx")) {
        return;
    }

    enabled = config.getBool("ipx", "ipx", enabled);
    server = config.get("ipx", "server", server);
    port = gsl::narrow<uint16_t>(config.getInt("ipx", "port",
                                  static_cast<int>(port)));
}

bool IPXConfig::isValid() const {
    if (enabled && server.empty()) {
        return false;
    }
    return true;
}

} // namespace legends
