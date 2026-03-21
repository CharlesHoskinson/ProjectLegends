// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Config parser implementation.

#include "app/config_parser.h"
#include "app/platform_dirs.h"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string_view>

namespace legends {

bool ConfigParser::loadFile(const std::string& path) {
    std::ifstream file(path);
    if (!file.is_open()) {
        return false;
    }

    // REQ-SEC-013: Warn if loading config from CWD (may be unintentional).
    std::error_code ec;
    auto canonical = std::filesystem::weakly_canonical(path, ec);
    auto cwd = std::filesystem::current_path(ec);
    if (!ec && canonical.has_parent_path() && canonical.parent_path() == cwd) {
        std::fprintf(stderr,
            "Warning: Loading config from current directory (%s) "
            "— this may be unintentional\n",
            canonical.string().c_str());
    }

    sections_.clear();
    loaded_path_ = path;

    std::string current_section;
    std::string line;
    bool first_line = true;

    while (std::getline(file, line)) {
        // Strip UTF-8 BOM (EF BB BF) from first line
        if (first_line) {
            first_line = false;
            if (line.size() >= 3 &&
                static_cast<unsigned char>(line[0]) == 0xEF &&
                static_cast<unsigned char>(line[1]) == 0xBB &&
                static_cast<unsigned char>(line[2]) == 0xBF) {
                line = line.substr(3);
            }
        }

        line = trim(line);

        // Skip empty lines and comments
        if (line.empty() || line[0] == '#' || line[0] == ';') {
            continue;
        }

        // Section header
        if (line.front() == '[' && line.back() == ']') {
            std::string name = toLower(trim(line.substr(1, line.size() - 2)));
            // REQ-SEC-014: Skip section names exceeding the length limit.
            if (name.size() > kMaxSectionNameLen) {
                continue;
            }
            current_section = std::move(name);
            continue;
        }

        // Key=value pair
        auto eq_pos = line.find('=');
        if (eq_pos != std::string::npos) {
            std::string key = toLower(trim(line.substr(0, eq_pos)));
            std::string value = trim(line.substr(eq_pos + 1));
            // REQ-SEC-014: Skip entries with oversized keys or values.
            if (key.size() > kMaxKeyLen || value.size() > kMaxValueLen) {
                continue;
            }
            if (!key.empty()) {
                sections_[current_section][key] = value;
            }
        }
    }

    return true;
}

std::string ConfigParser::get(std::string_view section, std::string_view key,
                              const std::string& default_val) const {
    auto sec_it = sections_.find(toLower(section));
    if (sec_it == sections_.end()) return default_val;

    auto key_it = sec_it->second.find(toLower(key));
    if (key_it == sec_it->second.end()) return default_val;

    return key_it->second;
}

int ConfigParser::getInt(std::string_view section, std::string_view key,
                         int default_val) const {
    std::string val = get(section, key, "");
    if (val.empty()) return default_val;

    int result = 0;
    auto [ptr, ec] = std::from_chars(val.data(), val.data() + val.size(), result);
    if (ec != std::errc{}) return default_val;
    return result;
}

bool ConfigParser::getBool(std::string_view section, std::string_view key,
                           bool default_val) const {
    std::string val = toLower(get(section, key, ""));
    if (val.empty()) return default_val;

    if (val == "true" || val == "yes" || val == "1" || val == "on") return true;
    if (val == "false" || val == "no" || val == "0" || val == "off") return false;
    return default_val;
}

bool ConfigParser::hasSection(std::string_view section) const {
    return sections_.find(toLower(section)) != sections_.end();
}

bool ConfigParser::hasKey(std::string_view section, std::string_view key) const {
    auto sec_it = sections_.find(toLower(section));
    if (sec_it == sections_.end()) return false;
    return sec_it->second.find(toLower(key)) != sec_it->second.end();
}

bool ConfigParser::loadDefaults() {
    // Search order per REQ-CONFIG-002
    if (loadFile("dosbox-x.conf")) return true;
    if (loadFile("dosbox.conf"))   return true;

    std::string config_dir = getConfigDir();
    if (!config_dir.empty()) {
        if (loadFile(config_dir + "/default.conf")) return true;
    }

    return false;
}

std::string ConfigParser::toLower(std::string_view s) {
    std::string result(s);
    std::transform(result.begin(), result.end(), result.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return result;
}

std::string ConfigParser::trim(std::string_view s) {
    auto start = s.find_first_not_of(" \t\r\n");
    if (start == std::string_view::npos) return {};
    auto end = s.find_last_not_of(" \t\r\n");
    return std::string(s.substr(start, end - start + 1));
}

} // namespace legends
