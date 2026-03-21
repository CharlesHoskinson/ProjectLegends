// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Minimal INI parser for DOSBox-X .conf format.
// REQ-CONFIG-001: Config file loading
// REQ-CONFIG-002: Default config search

#pragma once

#include <string>
#include <unordered_map>

namespace legends {

/// Field length limits for INI parsing (REQ-SEC-014).
/// Lines with section names, keys, or values exceeding these limits are skipped.
inline constexpr size_t kMaxSectionNameLen = 256;
inline constexpr size_t kMaxKeyLen         = 256;
inline constexpr size_t kMaxValueLen       = 4096;

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
    [[nodiscard]] bool loadFile(const std::string& path);

    /// Get a string value.
    [[nodiscard]] std::string get(const std::string& section, const std::string& key,
                    const std::string& default_val = "") const;

    /// Get an integer value.
    [[nodiscard]] int getInt(const std::string& section, const std::string& key,
               int default_val = 0) const;

    /// Get a boolean value (true/yes/1/on).
    [[nodiscard]] bool getBool(const std::string& section, const std::string& key,
                 bool default_val = false) const;

    /// Check if a section exists.
    [[nodiscard]] bool hasSection(const std::string& section) const;

    /// Check if a key exists within a section.
    [[nodiscard]] bool hasKey(const std::string& section, const std::string& key) const;

    /// Get the path of the loaded file (empty if none loaded).
    [[nodiscard]] const std::string& getLoadedPath() const { return loaded_path_; }

    /// Try to load from the default search locations.
    /// Search order:
    ///   1. ./dosbox-x.conf
    ///   2. ./dosbox.conf
    ///   3. <getConfigDir()>/default.conf
    /// @return true if any file was found and loaded.
    [[nodiscard]] bool loadDefaults();

private:
    using SectionMap = std::unordered_map<std::string, std::string>;
    std::unordered_map<std::string, SectionMap> sections_;
    std::string loaded_path_;

    [[nodiscard]] static std::string toLower(const std::string& s);
    [[nodiscard]] static std::string trim(const std::string& s);
};

} // namespace legends
