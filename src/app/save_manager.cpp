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

// Standalone CRC-32 lookup table (avoids zlib dependency for the app layer).
// Polynomial: 0xEDB88320 (reflected form of the standard CRC-32).
namespace {
constexpr uint32_t kCRC32Table[] = {
    0x00000000, 0x77073096, 0xEE0E612C, 0x990951BA, 0x076DC419, 0x706AF48F,
    0xE963A535, 0x9E6495A3, 0x0EDB8832, 0x79DCB8A4, 0xE0D5E91B, 0x97D2D988,
    0x09B64C2B, 0x7EB17CBB, 0xE7B82D09, 0x90BF1D9F, 0x1DB71064, 0x6AB020F2,
    0xF3B97148, 0x84BE41DE, 0x1ADAD47D, 0x6DDDE4EB, 0xF4D4B551, 0x83D385C7,
    0x136C9856, 0x646BA8C0, 0xFD62F97A, 0x8A65C9EC, 0x14015C4F, 0x63066CD9,
    0xFA0F3D63, 0x8D080DF5, 0x3B6E20C8, 0x4C69105E, 0xD56041E4, 0xA2677172,
    0x3C03E4D1, 0x4B04D447, 0xD20D85FD, 0xA50AB56B, 0x35B5A8FA, 0x42B2986C,
    0xDBBBB9D6, 0xACBCB9C0, 0x32D86CE3, 0x45DF5C75, 0xDCD60DCF, 0xABD13D59,
    0x26D930AC, 0x51DE003A, 0xC8D75180, 0xBFD06116, 0x21B4F0B5, 0x56B3C423,
    0xCFBA9599, 0xB8BDA50F, 0x2802B89E, 0x5F058808, 0xC60CD9B2, 0xB10BE924,
    0x2F6F7C87, 0x58684C11, 0xC1611DAB, 0xB6662D3D, 0x76DC4190, 0x01DB7106,
    0x98D220BC, 0xEFD5102A, 0x71B18589, 0x06B6B51F, 0x9FBFE4A5, 0xE8B8D433,
    0x7807C9A2, 0x0F00F934, 0x9609A88E, 0xE10E9818, 0x7F6A0D6B, 0x086D3D2D,
    0x91646C97, 0xE6635C01, 0x6B6B51F4, 0x1C6C6162, 0x856530D8, 0xF262004E,
    0x6C0695ED, 0x1B01A57B, 0x8208F4C1, 0xF50FC457, 0x65B0D9C6, 0x12B7E950,
    0x8BBEB8EA, 0xFCB9887C, 0x62DD1DDF, 0x15DA2D49, 0x8CD37CF3, 0xFBD44C65,
    0x4DB26158, 0x3AB551CE, 0xA3BC0074, 0xD4BB30E2, 0x4ADFA541, 0x3DD895D7,
    0xA4D1C46D, 0xD3D6F4FB, 0x4369E96A, 0x346ED9FC, 0xAD678846, 0xDA60B8D0,
    0x44042D73, 0x33031DE5, 0xAA0A4C5F, 0xDD0D7822, 0x3B6E20C8, 0x4C69105E,
    0xD56041E4, 0xA2677172, 0x3C03E4D1, 0x4B04D447, 0xD20D85FD, 0xA50AB56B,
    0x35B5A8FA, 0x42B2986C, 0xDBBBB9D6, 0xACBCB9C0, 0x32D86CE3, 0x45DF5C75,
    0xDCD60DCF, 0xABD13D59, 0x26D930AC, 0x51DE003A, 0xC8D75180, 0xBFD06116,
    0x21B4F0B5, 0x56B3C423, 0xCFBA9599, 0xB8BDA50F, 0x2802B89E, 0x5F058808,
    0xC60CD9B2, 0xB10BE924, 0x2F6F7C87, 0x58684C11, 0xC1611DAB, 0xB6662D3D,
    0x76DC4190, 0x01DB7106, 0x98D220BC, 0xEFD5102A, 0x71B18589, 0x06B6B51F,
    0x9FBFE4A5, 0xE8B8D433, 0x7807C9A2, 0x0F00F934, 0x9609A88E, 0xE10E9818,
    0x7F6A0D6B, 0x086D3D2D, 0x91646C97, 0xE6635C01, 0x6B6B51F4, 0x1C6C6162,
    0x856530D8, 0xF262004E, 0x6C0695ED, 0x1B01A57B, 0x8208F4C1, 0xF50FC457,
    0x65B0D9C6, 0x12B7E950, 0x8BBEB8EA, 0xFCB9887C, 0x62DD1DDF, 0x15DA2D49,
    0x8CD37CF3, 0xFBD44C65, 0x4DB26158, 0x3AB551CE, 0xA3BC0074, 0xD4BB30E2,
    0x4ADFA541, 0x3DD895D7, 0xA4D1C46D, 0xD3D6F4FB, 0x4369E96A, 0x346ED9FC,
    0xAD678846, 0xDA60B8D0, 0x44042D73, 0x33031DE5, 0xAA0A4C5F, 0xDD0D7822,
    0x9B64C2B0, 0xEC63F226, 0x756AA39C, 0x026D930A, 0x9C0906A9, 0xEB0E363F,
    0x72076785, 0x05005713, 0x95BF4A82, 0xE2B87A14, 0x7BB12BAE, 0x0CB61B38,
    0x92D28E9B, 0xE5D5BE0D, 0x7CDCEFB7, 0x0BDBDF21, 0x86D3D2D4, 0xF1D4E242,
    0x68DDB3F6, 0x1FDA836E, 0x81BE16CD, 0xF6B9265B, 0x6FB077E1, 0x18B74777,
    0x88085AE6, 0xFF0F6B70, 0x66063BCA, 0x11010B5C, 0x8F659EFF, 0xF862AE69,
    0x616BFFD3, 0x166CCF45, 0xA00AE278, 0xD70DD2EE, 0x4E048354, 0x3903B3C2,
    0xA7672661, 0xD06016F7, 0x4969474D, 0x3E6E77DB, 0xAED16A4A, 0xD9D65ADC,
    0x40DF0B66, 0x37D83BF0, 0xA9BCAE53, 0xDEBB9EC5, 0x47B2CF7F, 0x30B5FFE9,
    0xBDBDF21C, 0xCABAC28A, 0x53B39330, 0x24B4A3A6, 0xBAD03605, 0xCDD706FF,
    0x54DE5729, 0x23D967BF, 0xB3667A2E, 0xC4614AB8, 0x5D681B02, 0x2A6F2B94,
    0xB40BBE37, 0xC30C8EA1, 0x5A05DF1B, 0x2D02EF8D,
};
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
