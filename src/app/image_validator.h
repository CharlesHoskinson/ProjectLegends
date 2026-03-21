// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ImageValidator — pre-mount validation for disk image files.
// REQ-SEC-016: Defense-in-depth checks before mounting .img/.iso/.ima files.

#pragma once

#include <cstdint>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>

namespace legends {

struct ImageValidationResult {
    bool valid = false;
    std::string error;
};

/// REQ-SEC-016: Pre-mount validation for disk image files.
class ImageValidator {
public:
    static constexpr size_t kMaxFATImageSize = 2ULL * 1024 * 1024 * 1024;
    static constexpr size_t kMaxISOImageSize = 4700ULL * 1024 * 1024;
    static constexpr int kMaxDirectoryDepth = 32;

    [[nodiscard]] static ImageValidationResult validate(std::string_view path);

private:
    [[nodiscard]] static ImageValidationResult validateFAT(std::string_view path, size_t file_size);
    [[nodiscard]] static ImageValidationResult validateISO(std::string_view path, size_t file_size);

    [[nodiscard]] static ImageValidationResult validateFATDirectoryDepth(
        std::ifstream& file, const uint8_t* boot,
        uint16_t bytes_per_sector, uint8_t num_fats,
        uint16_t reserved_sectors, size_t file_size);
};

} // namespace legends
