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

/// REQ-SEC-010: Save state header for validation.
/// REQ-SEC-011: CRC-32 integrity check on save state payload.
#pragma pack(push, 1)
struct SaveStateHeader {
    uint8_t  magic[4];       // "LGND"
    uint16_t version;        // Header format version (currently 1)
    uint32_t crc32;          // CRC-32 of the payload (state blob)
    uint64_t payload_size;   // Size of the state blob in bytes
};
#pragma pack(pop)

static_assert(sizeof(SaveStateHeader) == 18, "SaveStateHeader must be packed");

class RuntimeHost;

class SaveManager {
public:
    static constexpr int kMaxSlots = 9;
    static constexpr int kAutosaveSlot = 0;  // REQ-UX-010: slot 0 reserved for crash autosave
    static constexpr size_t kMaxSaveSize = 256 * 1024 * 1024; // 256 MB limit
    static constexpr uint16_t kHeaderVersion = 1;

    /// Get the saves directory: <getDataDir()>/saves
    [[nodiscard]] static std::string getSaveDir();

    /// Get the file path for a save slot. Slot 0 is reserved for crash autosave;
    /// slots 1 through kMaxSlots are user-visible saves.
    [[nodiscard]] static std::string slotPath(int slot);

    /// Get the file path for a save slot thumbnail.
    [[nodiscard]] static std::string thumbnailPath(int slot);

    /// Save engine state to the given slot with optional RGB24 thumbnail.
    /// Returns true on success.
    [[nodiscard]] bool saveToSlot(legends_handle engine, int slot,
                    const uint8_t* rgb_thumb, uint16_t w, uint16_t h);

    [[nodiscard]] bool saveToSlot(RuntimeHost& runtime, int slot,
                    const uint8_t* rgb_thumb, uint16_t w, uint16_t h);

    /// Load engine state from the given slot.
    /// Returns true on success.
    [[nodiscard]] bool loadFromSlot(legends_handle engine, int slot);

    [[nodiscard]] bool loadFromSlot(RuntimeHost& runtime, int slot);

    /// Check if a slot has a saved state file.
    [[nodiscard]] bool isSlotOccupied(int slot) const;

    /// Last error message (empty on success).
    [[nodiscard]] const std::string& lastError() const { return last_error_; }

    /// Compute CRC-32 of a data buffer (uses zlib crc32).
    [[nodiscard]] static uint32_t computeCRC32(const void* data, size_t size);

    /// REQ-UX-010: Check if a crash autosave exists.
    [[nodiscard]] bool hasAutosave() const { return isSlotOccupied(kAutosaveSlot); }

    /// REQ-UX-010: Load the crash autosave and delete the file.
    [[nodiscard]] bool recoverAutosave(legends_handle engine);

    [[nodiscard]] bool recoverAutosave(RuntimeHost& runtime);

private:
    std::string last_error_;

    /// Write data to path atomically (write .tmp then rename).
    [[nodiscard]] static bool atomicWrite(const std::string& path, const void* data, size_t size);
};

} // namespace legends
