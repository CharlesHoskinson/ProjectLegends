// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// InputMapper — customizable SDL3-to-AT scancode remapping with persistence.

#pragma once

#include "app/scancode_map.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>

namespace legends {

class InputMapper {
public:
    /// Load custom remappings from file. Returns true if file was read.
    /// Missing file is not an error (returns false, no remaps loaded).
<<<<<<< HEAD
    [[nodiscard]] bool loadFromFile(const std::string& path);

    /// Save current remappings to file. Returns true on success.
    [[nodiscard]] bool saveToFile(const std::string& path) const;
=======
    bool loadFromFile(std::string_view path);

    /// Save current remappings to file. Returns true on success.
    bool saveToFile(std::string_view path) const;
>>>>>>> worktree-agent-a4ab30fc

    /// Translate an SDL3 scancode to AT Set 1, applying any custom remap first.
    [[nodiscard]] ATScancode translate(uint16_t sdl_scancode) const;

    /// Add a custom remap: sdl_from key will behave as sdl_to key.
    void remap(uint16_t sdl_from, uint16_t sdl_to);

    /// Remove a custom remap for the given key.
    void clearRemap(uint16_t sdl_from);

    /// Remove all custom remaps.
    void clearAll();

    /// Number of custom remaps currently active.
    [[nodiscard]] size_t customCount() const;

private:
    std::unordered_map<uint16_t, uint16_t> remaps_;
};

} // namespace legends
