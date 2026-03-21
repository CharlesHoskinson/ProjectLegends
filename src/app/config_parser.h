// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Minimal INI parser for DOSBox-X .conf format.
// REQ-CONFIG-001: Config file loading
// REQ-CONFIG-002: Default config search

#pragma once

#include <string>
#include <string_view>
#include <unordered_map>

namespace legends {

/// INI-style configuration file parser.
///
/// Supports:
/// - [section] headers
/// - key=value pairs (whitespace-trimmed)
/// - # and ; line comments
/// - Case-insensitive section/key names
class ConfigParser {
public:
    /// Load configuration from a file.
    /// @return true on success, false if file cannot be opened.
    bool loadFile(const std::string& path);

    /// Get a string value.
    std::string get(std::string_view section, std::string_view key,
                    const std::string& default_val = "") const;

    /// Get an integer value.
    int getInt(std::string_view section, std::string_view key,
               int default_val = 0) const;

    /// Get a boolean value (true/yes/1/on).
    bool getBool(std::string_view section, std::string_view key,
                 bool default_val = false) const;

    /// Check if a section exists.
    bool hasSection(std::string_view section) const;

    /// Check if a key exists within a section.
    bool hasKey(std::string_view section, std::string_view key) const;

    /// Get the path of the loaded file (empty if none loaded).
    const std::string& getLoadedPath() const { return loaded_path_; }

    /// Try to load from the default search locations.
    /// Search order:
    ///   1. ./dosbox-x.conf
    ///   2. ./dosbox.conf
    ///   3. <getConfigDir()>/default.conf
    /// @return true if any file was found and loaded.
    bool loadDefaults();

private:
    using SectionMap = std::unordered_map<std::string, std::string>;
    std::unordered_map<std::string, SectionMap> sections_;
    std::string loaded_path_;

    static std::string toLower(std::string_view s);
    static std::string trim(std::string_view s);
};

} // namespace legends
