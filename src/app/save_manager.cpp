// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// SaveManager implementation — save/load state blobs, atomic writes, thumbnails.
// REQ-SEC-010: Save state header validation (magic + version + size)
// REQ-SEC-011: CRC-32 integrity verification on load

#include "app/save_manager.h"
#include "app/capture.h"
#include "app/platform_dirs.h"

#include <cstdio>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <vector>

namespace legends {

// CRC-32 lookup table generated at compile time from polynomial 0xEDB88320
// (reflected form of the standard CRC-32).
namespace {

constexpr uint32_t crc32_entry(uint32_t index) {
    uint32_t crc = index;
    for (int bit = 0; bit < 8; ++bit) {
        if (crc & 1)
            crc = (crc >> 1) ^ 0xEDB88320u;
        else
            crc >>= 1;
    }
    return crc;
}

struct CRC32Table {
    uint32_t entries[256];
    constexpr CRC32Table() : entries{} {
        for (uint32_t i = 0; i < 256; ++i)
            entries[i] = crc32_entry(i);
    }
    constexpr uint32_t operator[](size_t i) const { return entries[i]; }
};

static constexpr CRC32Table kCRC32Table{};

// Static asserts to verify key entries match the standard CRC-32 polynomial.
static_assert(kCRC32Table[0]   == 0x00000000, "CRC-32 table[0] mismatch");
static_assert(kCRC32Table[1]   == 0x77073096, "CRC-32 table[1] mismatch");
static_assert(kCRC32Table[128] == 0xEDB88320, "CRC-32 table[128] mismatch");
static_assert(kCRC32Table[255] == 0x2D02EF8D, "CRC-32 table[255] mismatch");

} // namespace

std::string SaveManager::getSaveDir() {
    return getDataDir() + "/saves";
}

std::string SaveManager::slotPath(int slot) {
    char buf[64];
    std::snprintf(buf, sizeof(buf), "/slot_%d.sav", slot);
    return getSaveDir() + buf;
}

std::string SaveManager::thumbnailPath(int slot) {
    char buf[64];
    std::snprintf(buf, sizeof(buf), "/slot_%d.png", slot);
    return getSaveDir() + buf;
}

uint32_t SaveManager::computeCRC32(const void* data, size_t size) {
    auto* bytes = static_cast<const uint8_t*>(data);
    uint32_t crc = 0xFFFFFFFF;
    for (size_t i = 0; i < size; ++i) {
        crc = kCRC32Table[(crc ^ bytes[i]) & 0xFF] ^ (crc >> 8);
    }
    return crc ^ 0xFFFFFFFF;
}

bool SaveManager::saveToSlot(legends_handle engine, int slot,
                             const uint8_t* rgb_thumb, uint16_t w, uint16_t h) {
    if (!engine || slot < 0 || slot > kMaxSlots) {
        last_error_ = "Invalid engine handle or slot number";
        return false;
    }

    // Create saves directory
    std::string dir = getSaveDir();
    std::error_code ec;
    std::filesystem::create_directories(dir, ec);
    if (ec) {
        last_error_ = "Cannot create save directory: " + ec.message();
        return false;
    }

    // Two-call pattern: query state size, then read
    size_t state_size = 0;
    auto err = legends_save_state(engine, nullptr, 0, &state_size);
    if (err != LEGENDS_OK && err != LEGENDS_ERR_BUFFER_TOO_SMALL) {
        last_error_ = "legends_save_state query failed: " + std::to_string(err);
        return false;
    }
    if (state_size == 0) {
        last_error_ = "State size is zero";
        return false;
    }

    std::vector<uint8_t> state_buf(state_size);
    err = legends_save_state(engine, state_buf.data(), state_buf.size(), &state_size);
    if (err != LEGENDS_OK) {
        last_error_ = "legends_save_state failed: " + std::to_string(err);
        return false;
    }

    // Build header (REQ-SEC-010, REQ-SEC-011)
    SaveStateHeader header{};
    header.magic[0] = 'L'; header.magic[1] = 'G';
    header.magic[2] = 'N'; header.magic[3] = 'D';
    header.version = kHeaderVersion;
    header.payload_size = state_size;
    header.crc32 = computeCRC32(state_buf.data(), state_size);

    // Combine header + payload for atomic write
    std::vector<uint8_t> file_data(sizeof(header) + state_size);
    std::memcpy(file_data.data(), &header, sizeof(header));
    std::memcpy(file_data.data() + sizeof(header), state_buf.data(), state_size);

    // Atomic write the state blob
    std::string path = slotPath(slot);
    if (!atomicWrite(path, file_data.data(), file_data.size())) {
        last_error_ = "Failed to write save file: " + path;
        return false;
    }

    // Write thumbnail PNG (non-fatal if it fails)
    if (rgb_thumb && w > 0 && h > 0) {
        writeScreenshotPNG(thumbnailPath(slot), rgb_thumb, w, h);
    }

    last_error_.clear();
    return true;
}

bool SaveManager::loadFromSlot(legends_handle engine, int slot) {
    if (!engine || slot < 0 || slot > kMaxSlots) {
        last_error_ = "Invalid engine handle or slot number";
        return false;
    }

    std::string path = slotPath(slot);
    if (!std::filesystem::exists(path)) {
        last_error_ = "Slot " + std::to_string(slot) + " is empty";
        return false;
    }

    // Read the save file
    std::ifstream file(path, std::ios::binary | std::ios::ate);
    if (!file.is_open()) {
        last_error_ = "Cannot open save file: " + path;
        return false;
    }

    auto file_size = file.tellg();
    if (file_size == std::streampos(-1) || file_size == std::streampos(0)) {
        last_error_ = "Save file is empty: " + path;
        return false;
    }

    // REQ-SEC-010: Reject files exceeding size limit before allocating
    auto total_size = static_cast<size_t>(file_size);
    if (total_size > kMaxSaveSize + sizeof(SaveStateHeader)) {
        last_error_ = "Save file exceeds maximum size limit";
        return false;
    }

    // Must be at least large enough for a header
    if (total_size < sizeof(SaveStateHeader)) {
        last_error_ = "Save file too small to contain valid header";
        return false;
    }

    std::vector<uint8_t> buf(total_size);
    file.seekg(0);
    file.read(reinterpret_cast<char*>(buf.data()), static_cast<std::streamsize>(total_size));
    if (!file) {
        last_error_ = "Failed to read save file: " + path;
        return false;
    }

    // REQ-SEC-010: Validate header
    SaveStateHeader header{};
    std::memcpy(&header, buf.data(), sizeof(header));

    if (header.magic[0] != 'L' || header.magic[1] != 'G' ||
        header.magic[2] != 'N' || header.magic[3] != 'D') {
        last_error_ = "Invalid save file: bad magic bytes";
        return false;
    }

    if (header.version != kHeaderVersion) {
        last_error_ = "Unsupported save file version: " + std::to_string(header.version);
        return false;
    }

    if (header.payload_size > kMaxSaveSize) {
        last_error_ = "Save state payload exceeds maximum size limit";
        return false;
    }

    size_t expected_total = sizeof(SaveStateHeader) + header.payload_size;
    if (total_size < expected_total) {
        last_error_ = "Save file truncated: header claims " +
                       std::to_string(header.payload_size) + " bytes but file too small";
        return false;
    }

    // REQ-SEC-011: Verify CRC-32
    const uint8_t* payload = buf.data() + sizeof(SaveStateHeader);
    uint32_t actual_crc = computeCRC32(payload, header.payload_size);
    if (actual_crc != header.crc32) {
        last_error_ = "Save file integrity check failed: CRC-32 mismatch";
        return false;
    }

    auto err = legends_load_state(engine, payload, header.payload_size);
    if (err != LEGENDS_OK) {
        last_error_ = "legends_load_state failed: " + std::to_string(err);
        return false;
    }

    last_error_.clear();
    return true;
}

bool SaveManager::isSlotOccupied(int slot) const {
    if (slot < 0 || slot > kMaxSlots) return false;
    return std::filesystem::exists(slotPath(slot));
}

bool SaveManager::recoverAutosave(legends_handle engine) {
    if (!loadFromSlot(engine, kAutosaveSlot)) {
        return false;
    }
    // Delete the autosave file after successful recovery
    std::string path = slotPath(kAutosaveSlot);
    std::error_code ec;
    std::filesystem::remove(path, ec);
    return true;
}

bool SaveManager::atomicWrite(const std::string& path, const void* data, size_t size) {
    std::string tmp_path = path + ".tmp";

    // Write to temporary file
    std::ofstream file(tmp_path, std::ios::binary);
    if (!file.is_open()) return false;
    file.write(static_cast<const char*>(data), static_cast<std::streamsize>(size));
    file.close();
    if (!file) return false;

    // Atomic rename over target
    std::error_code ec;
    std::filesystem::rename(tmp_path, path, ec);
    return !ec;
}

} // namespace legends
