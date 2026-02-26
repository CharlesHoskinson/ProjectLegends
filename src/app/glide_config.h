// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// 3dfx Glide emulation configuration from [glide] config section.

#pragma once

#include <cstdint>
#include <string>

namespace legends {

class ConfigParser;

/// 3dfx Glide emulation configuration loaded from the [glide] config section.
struct GlideConfig {
    bool enabled = false;           ///< Whether Glide passthrough is active.
    uint16_t width = 640;           ///< Glide render width in pixels.
    uint16_t height = 480;          ///< Glide render height in pixels.
    bool lfb_access = true;         ///< Allow Linear Frame Buffer access.
    std::string splash_screen;      ///< Splash screen mode: "true", "false", or "auto".

    /// Load settings from the [glide] section of a ConfigParser.
    /// @param config  Parsed configuration source.
    void loadFrom(const ConfigParser& config);

    /// Validate resolution and settings.
    /// @return true if the configuration is usable.
    bool isValid() const;

    /// @return true if Glide emulation requires an OpenGL context.
    bool requiresOpenGL() const { return enabled; }
};

} // namespace legends
