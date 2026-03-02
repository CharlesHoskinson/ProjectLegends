// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// InputMapper implementation — load/save mapper.txt, translate with remaps.

#include "app/input_mapper.h"

#include <cstdio>
#include <fstream>
#include <sstream>

namespace legends {

bool InputMapper::loadFromFile(const std::string& path) {
    std::ifstream file(path);
    if (!file.is_open()) return false;

    remaps_.clear();
    std::string line;
    while (std::getline(file, line)) {
        // Skip empty lines and comments
        if (line.empty() || line[0] == '#') continue;

        std::istringstream iss(line);
        std::string from_str, to_str;
        if (!(iss >> from_str >> to_str)) continue;

        // Parse hex values (with or without 0x prefix)
        unsigned long from_val = 0, to_val = 0;
        try {
            std::size_t from_pos = 0, to_pos = 0;
            from_val = std::stoul(from_str, &from_pos, 16);
            to_val = std::stoul(to_str, &to_pos, 16);
            // Reject if not all characters were consumed
            if (from_pos != from_str.size() || to_pos != to_str.size()) continue;
        } catch (...) {
            continue; // Skip malformed lines
        }

        if (from_val <= 0xFFFF && to_val <= 0xFFFF) {
            remaps_[static_cast<uint16_t>(from_val)] = static_cast<uint16_t>(to_val);
        }
    }

    return true;
}

bool InputMapper::saveToFile(const std::string& path) const {
    std::ofstream file(path);
    if (!file.is_open()) return false;

    file << "# Project Legends key mapper\n";
    file << "# Format: SDL_FROM SDL_TO (hex)\n";

    for (const auto& [from, to] : remaps_) {
        char buf[32];
        std::snprintf(buf, sizeof(buf), "0x%04X 0x%04X", from, to);
        file << buf << "\n";
    }

    return file.good();
}

ATScancode InputMapper::translate(uint16_t sdl_scancode) const {
    // Check for custom remap first
    auto it = remaps_.find(sdl_scancode);
    if (it != remaps_.end()) {
        return sdlScancodeToAT(it->second);
    }
    return sdlScancodeToAT(sdl_scancode);
}

void InputMapper::remap(uint16_t sdl_from, uint16_t sdl_to) {
    remaps_[sdl_from] = sdl_to;
}

void InputMapper::clearRemap(uint16_t sdl_from) {
    remaps_.erase(sdl_from);
}

void InputMapper::clearAll() {
    remaps_.clear();
}

size_t InputMapper::customCount() const {
    return remaps_.size();
}

} // namespace legends
