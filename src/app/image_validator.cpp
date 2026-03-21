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
#include <string>
#include <string_view>

namespace legends {

ImageValidationResult ImageValidator::validate(std::string_view path) {
    std::string path_str(path);
    std::error_code ec;
    auto file_size = std::filesystem::file_size(path_str, ec);
    if (ec) return {false, "Cannot read file size: " + ec.message()};
    if (file_size == 0) return {false, "Image file is empty"};

    // Detect type by extension
    std::filesystem::path p(path_str);
    std::string ext = p.extension().string();
    std::transform(ext.begin(), ext.end(), ext.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });

    if (ext == ".iso" || ext == ".cue") {
        return validateISO(path, static_cast<size_t>(file_size));
    }
    return validateFAT(path, static_cast<size_t>(file_size));
}

ImageValidationResult ImageValidator::validateFAT(std::string_view path, size_t file_size) {
    if (file_size > kMaxFATImageSize) {
        return {false, "FAT image exceeds 2 GB size limit"};
    }

    // Must be large enough for a boot sector
    if (file_size < 512) {
        return {false, "Image too small for FAT boot sector"};
    }

    // Read the boot sector (first 512 bytes)
    std::ifstream file(std::string(path), std::ios::binary);
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

    // REQ-SEC-016: Validate FAT directory depth to prevent stack exhaustion
    // from deeply nested directory chains in malformed images.
    auto depth_result = validateFATDirectoryDepth(file, boot, bytes_per_sector,
                                                   num_fats, reserved, file_size);
    if (!depth_result.valid) {
        return depth_result;
    }

    return {true, ""};
}

ImageValidationResult ImageValidator::validateFATDirectoryDepth(
    std::ifstream& file, const uint8_t* boot,
    uint16_t bytes_per_sector, uint8_t num_fats,
    uint16_t reserved_sectors, size_t file_size) {

    // Compute the root directory offset for FAT12/FAT16.
    // BPB bytes 17-18: Root entry count
    uint16_t root_entry_count;
    std::memcpy(&root_entry_count, &boot[17], 2);

    // FAT size (16-bit): BPB bytes 22-23
    uint16_t fat_size_16;
    std::memcpy(&fat_size_16, &boot[22], 2);

    if (root_entry_count == 0 || fat_size_16 == 0) {
        // FAT32 or unrecognizable layout — skip depth check (valid so far)
        return {true, ""};
    }

    // Root directory starts after reserved sectors + all FATs
    uint64_t root_dir_offset = static_cast<uint64_t>(reserved_sectors) * bytes_per_sector
                             + static_cast<uint64_t>(num_fats) * fat_size_16 * bytes_per_sector;

    uint32_t root_dir_bytes = static_cast<uint32_t>(root_entry_count) * 32u;

    if (root_dir_offset + root_dir_bytes > file_size) {
        return {false, "FAT root directory extends beyond file"};
    }

    // Data region starts after root directory
    uint64_t data_region_offset = root_dir_offset + root_dir_bytes;
    uint8_t spc = boot[13];
    uint32_t cluster_bytes = static_cast<uint32_t>(spc) * bytes_per_sector;
    if (cluster_bytes == 0) {
        return {false, "Invalid cluster size"};
    }

    // Walk root directory entries to find subdirectories, then check depth
    // using iterative BFS with a depth counter capped at kMaxDirectoryDepth.
    struct DirEntry {
        uint64_t offset;
        uint32_t size;
        int depth;
    };

    std::vector<DirEntry> stack;
    stack.push_back({root_dir_offset, root_dir_bytes, 0});

    while (!stack.empty()) {
        auto current = stack.back();
        stack.pop_back();

        if (current.depth > kMaxDirectoryDepth) {
            return {false, "FAT directory depth exceeds limit (" +
                            std::to_string(kMaxDirectoryDepth) + ")"};
        }

        // Read directory entries (each is 32 bytes)
        uint32_t entry_count = current.size / 32;
        for (uint32_t i = 0; i < entry_count && i < 512; ++i) {
            uint64_t entry_offset = current.offset + static_cast<uint64_t>(i) * 32;
            if (entry_offset + 32 > file_size) break;

            uint8_t entry[32];
            file.seekg(static_cast<std::streamoff>(entry_offset));
            file.read(reinterpret_cast<char*>(entry), 32);
            if (!file) break;

            // End-of-directory marker
            if (entry[0] == 0x00) break;
            // Deleted entry
            if (entry[0] == 0xE5) continue;
            // Long filename entry (attr = 0x0F)
            if (entry[11] == 0x0F) continue;

            // Check if subdirectory (attr bit 4)
            if ((entry[11] & 0x10) == 0) continue;

            // Skip "." and ".." entries
            if (entry[0] == '.' && (entry[1] == ' ' || entry[1] == '.')) continue;

            // Get starting cluster (bytes 26-27 low word)
            uint16_t start_cluster;
            std::memcpy(&start_cluster, &entry[26], 2);

            if (start_cluster < 2) continue;

            // Calculate the offset of this subdirectory's data
            uint64_t subdir_offset = data_region_offset +
                static_cast<uint64_t>(start_cluster - 2) * cluster_bytes;

            if (subdir_offset + cluster_bytes > file_size) continue;

            stack.push_back({subdir_offset, cluster_bytes, current.depth + 1});
        }
    }

    return {true, ""};
}

ImageValidationResult ImageValidator::validateISO(std::string_view /*path*/, size_t file_size) {
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
