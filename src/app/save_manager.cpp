// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// SaveManager implementation — save/load state blobs, atomic writes, thumbnails.

#include "app/save_manager.h"
#include "app/capture.h"
#include "app/platform_dirs.h"

#include <cstdio>
#include <filesystem>
#include <fstream>
#include <vector>

namespace legends {

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

bool SaveManager::saveToSlot(legends_handle engine, int slot,
                             const uint8_t* rgb_thumb, uint16_t w, uint16_t h) {
    if (!engine || slot < 1 || slot > kMaxSlots) {
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

    // Atomic write the state blob
    std::string path = slotPath(slot);
    if (!atomicWrite(path, state_buf.data(), state_size)) {
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
    if (!engine || slot < 1 || slot > kMaxSlots) {
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

    std::vector<uint8_t> buf(static_cast<size_t>(file_size));
    file.seekg(0);
    file.read(reinterpret_cast<char*>(buf.data()), file_size);
    if (!file) {
        last_error_ = "Failed to read save file: " + path;
        return false;
    }

    auto err = legends_load_state(engine, buf.data(), buf.size());
    if (err != LEGENDS_OK) {
        last_error_ = "legends_load_state failed: " + std::to_string(err);
        return false;
    }

    last_error_.clear();
    return true;
}

bool SaveManager::isSlotOccupied(int slot) const {
    if (slot < 1 || slot > kMaxSlots) return false;
    return std::filesystem::exists(slotPath(slot));
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
