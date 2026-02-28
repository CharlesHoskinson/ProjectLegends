// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Platform-specific directory resolution.
// REQ-CONFIG-002: Default config search paths

#pragma once

#include <string>

namespace legends {

/// Get the platform-specific configuration directory.
/// Windows:  %APPDATA%\ProjectLegends
/// Linux:    $XDG_CONFIG_HOME/projectlegends (fallback ~/.config/projectlegends)
/// macOS:    ~/Library/Preferences/ProjectLegends
std::string getConfigDir();

/// Get the platform-specific data directory.
/// Windows:  %APPDATA%\ProjectLegends
/// Linux:    $XDG_DATA_HOME/projectlegends (fallback ~/.local/share/projectlegends)
/// macOS:    ~/Library/Application Support/ProjectLegends
std::string getDataDir();

/// Get the platform-specific cache directory.
/// Windows:  %LOCALAPPDATA%\ProjectLegends
/// Linux:    $XDG_CACHE_HOME/projectlegends (fallback ~/.cache/projectlegends)
/// macOS:    ~/Library/Caches/ProjectLegends
std::string getCacheDir();

/// Get the platform-specific log directory.
/// Windows:  %LOCALAPPDATA%\ProjectLegends\logs
/// Linux:    $XDG_CACHE_HOME/projectlegends/logs (fallback ~/.cache/projectlegends/logs)
/// macOS:    ~/Library/Caches/ProjectLegends/logs
std::string getLogDir();

} // namespace legends
