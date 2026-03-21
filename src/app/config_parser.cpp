// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Config parser implementation.

#include "app/config_parser.h"
#include "app/platform_dirs.h"

#include <gsl-lite/gsl-lite.hpp>

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <sstream>

namespace legends {

bool ConfigParser::loadFile(const std::string& path) {
    gsl_Expects(!path.empty());
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
            current_section = toLower(trim(line.substr(1, line.size() - 2)));
            continue;
        }

        // Key=value pair
        auto eq_pos = line.find('=');
        if (eq_pos != std::string::npos) {
            std::string key = toLower(trim(line.substr(0, eq_pos)));
            std::string value = trim(line.substr(eq_pos + 1));
            if (!key.empty()) {
                sections_[current_section][key] = value;
            }
        }
    }

    return true;
}

std::string ConfigParser::get(const std::string& section, const std::string& key,
                              const std::string& default_val) const {
    auto sec_it = sections_.find(toLower(section));
    if (sec_it == sections_.end()) return default_val;

    auto key_it = sec_it->second.find(toLower(key));
    if (key_it == sec_it->second.end()) return default_val;

    return key_it->second;
}

int ConfigParser::getInt(const std::string& section, const std::string& key,
                         int default_val) const {
    std::string val = get(section, key, "");
    if (val.empty()) return default_val;

    try {
        return std::stoi(val);
    } catch (...) {
        return default_val;
    }
}

bool ConfigParser::getBool(const std::string& section, const std::string& key,
                           bool default_val) const {
    std::string val = toLower(get(section, key, ""));
    if (val.empty()) return default_val;

    if (val == "true" || val == "yes" || val == "1" || val == "on") return true;
    if (val == "false" || val == "no" || val == "0" || val == "off") return false;
    return default_val;
}

bool ConfigParser::hasSection(const std::string& section) const {
    return sections_.find(toLower(section)) != sections_.end();
}

bool ConfigParser::hasKey(const std::string& section, const std::string& key) const {
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

std::string ConfigParser::toLower(const std::string& s) {
    std::string result = s;
    std::transform(result.begin(), result.end(), result.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return result;
}

std::string ConfigParser::trim(const std::string& s) {
    auto start = s.find_first_not_of(" \t\r\n");
    if (start == std::string::npos) return {};
    auto end = s.find_last_not_of(" \t\r\n");
    return s.substr(start, end - start + 1);
}

} // namespace legends
