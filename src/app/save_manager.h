// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// SaveManager — multi-slot save state management with atomic writes and
// optional thumbnail PNG.

#pragma once

#include <legends/legends_embed.h>
#include <cstdint>
#include <string>

namespace legends {

class SaveManager {
public:
    static constexpr int kMaxSlots = 9;

    /// Get the saves directory: <getDataDir()>/saves
    static std::string getSaveDir();

    /// Get the file path for a save slot (1-based).
    static std::string slotPath(int slot);

    /// Get the file path for a save slot thumbnail (1-based).
    static std::string thumbnailPath(int slot);

    /// Save engine state to the given slot with optional RGB24 thumbnail.
    /// Returns true on success.
    bool saveToSlot(legends_handle engine, int slot,
                    const uint8_t* rgb_thumb, uint16_t w, uint16_t h);

    /// Load engine state from the given slot.
    /// Returns true on success.
    bool loadFromSlot(legends_handle engine, int slot);

    /// Check if a slot has a saved state file.
    bool isSlotOccupied(int slot) const;

    /// Last error message (empty on success).
    const std::string& lastError() const { return last_error_; }

private:
    std::string last_error_;

    /// Write data to path atomically (write .tmp then rename).
    static bool atomicWrite(const std::string& path, const void* data, size_t size);
};

} // namespace legends
