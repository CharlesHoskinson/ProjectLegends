// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ImageValidator — pre-mount validation for disk image files.
// REQ-SEC-016: Defense-in-depth against malformed disk images.

#include "app/image_validator.h"

#include <algorithm>
#include <cstring>
#include <filesystem>
#include <fstream>

namespace legends {

ImageValidationResult ImageValidator::validate(const std::string& path) {
    std::error_code ec;
    auto file_size = std::filesystem::file_size(path, ec);
    if (ec) return {false, "Cannot read file size: " + ec.message()};
    if (file_size == 0) return {false, "Image file is empty"};

    // Detect type by extension
    std::filesystem::path p(path);
    std::string ext = p.extension().string();
    std::transform(ext.begin(), ext.end(), ext.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });

    if (ext == ".iso" || ext == ".cue") {
        return validateISO(path, static_cast<size_t>(file_size));
    }
    return validateFAT(path, static_cast<size_t>(file_size));
}

ImageValidationResult ImageValidator::validateFAT(const std::string& path, size_t file_size) {
    if (file_size > kMaxFATImageSize) {
        return {false, "FAT image exceeds 2 GB size limit"};
    }

    // Must be large enough for a boot sector
    if (file_size < 512) {
        return {false, "Image too small for FAT boot sector"};
    }

    // Read the boot sector (first 512 bytes)
    std::ifstream file(path, std::ios::binary);
    if (!file.is_open()) return {false, "Cannot open image file"};

    uint8_t boot[512];
    file.read(reinterpret_cast<char*>(boot), 512);
    if (!file) {
        return {false, "Failed to read boot sector"};
    }

    // BPB validation: Jump instruction at byte 0
    // Valid values: 0xEB (short jump), 0xE9 (near jump), 0x00 (some raw images)
    if (boot[0] != 0xEB && boot[0] != 0xE9 && boot[0] != 0x00) {
        return {false, "Invalid boot sector: bad jump instruction"};
    }

    // BPB bytes 11-12: Bytes per sector (must be power of 2, 128-4096)
    uint16_t bytes_per_sector;
    std::memcpy(&bytes_per_sector, &boot[11], 2);
    if (bytes_per_sector == 0 || (bytes_per_sector & (bytes_per_sector - 1)) != 0 ||
        bytes_per_sector < 128 || bytes_per_sector > 4096) {
        return {false, "Invalid BPB: bad bytes per sector (" +
                        std::to_string(bytes_per_sector) + ")"};
    }

    // BPB byte 13: Sectors per cluster (must be power of 2, 1-128)
    uint8_t spc = boot[13];
    if (spc == 0 || (spc & (spc - 1)) != 0 || spc > 128) {
        return {false, "Invalid BPB: bad sectors per cluster"};
    }

    // BPB bytes 14-15: Reserved sector count (must be >= 1)
    uint16_t reserved;
    std::memcpy(&reserved, &boot[14], 2);
    if (reserved == 0) {
        return {false, "Invalid BPB: zero reserved sectors"};
    }

    // BPB byte 16: Number of FATs (typically 2, must be 1-4)
    uint8_t num_fats = boot[16];
    if (num_fats == 0 || num_fats > 4) {
        return {false, "Invalid BPB: bad FAT count (" + std::to_string(num_fats) + ")"};
    }

    // Boot sector signature at bytes 510-511
    if (boot[510] != 0x55 || boot[511] != 0xAA) {
        return {false, "Invalid boot sector: missing 0x55AA signature"};
    }

    // Cross-check: total sectors vs file size (sanity bound)
    uint16_t total_sectors_16;
    std::memcpy(&total_sectors_16, &boot[19], 2);
    uint32_t total_sectors_32 = 0;
    if (total_sectors_16 == 0) {
        std::memcpy(&total_sectors_32, &boot[32], 4);
    } else {
        total_sectors_32 = total_sectors_16;
    }

    if (total_sectors_32 > 0) {
        auto claimed_size = static_cast<uint64_t>(total_sectors_32) * bytes_per_sector;
        if (claimed_size > file_size * 2) {
            return {false, "BPB claims more sectors than file contains"};
        }
    }

    return {true, ""};
}

ImageValidationResult ImageValidator::validateISO(const std::string& /*path*/, size_t file_size) {
    if (file_size > kMaxISOImageSize) {
        return {false, "ISO image exceeds 4.7 GB size limit"};
    }

    // ISO 9660: system area (32 KB) + at least one volume descriptor (2 KB)
    if (file_size < 32768 + 2048) {
        return {false, "ISO image too small for valid ISO 9660"};
    }

    return {true, ""};
}

} // namespace legends
