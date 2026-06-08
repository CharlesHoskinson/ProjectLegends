// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// 3dfx Glide emulation configuration implementation.

#include "app/glide_config.h"
#include "app/config_parser.h"

#include <legends/gsl.hpp>

namespace legends {

void GlideConfig::loadFrom(const ConfigParser& config) {
    if (!config.hasSection("glide")) {
        return;
    }

    enabled = config.getBool("glide", "glide", enabled);
    width = gsl::narrow<uint16_t>(config.getInt("glide", "width",
                                   static_cast<int>(width)));
    height = gsl::narrow<uint16_t>(config.getInt("glide", "height",
                                    static_cast<int>(height)));
    lfb_access = config.getBool("glide", "lfb", lfb_access);
    splash_screen = config.get("glide", "splash", splash_screen);
}

bool GlideConfig::isValid() const {
    if (enabled && (width == 0 || height == 0)) {
        return false;
    }
    return true;
}

} // namespace legends
