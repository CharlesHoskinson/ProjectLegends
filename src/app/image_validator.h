// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ImageValidator — pre-mount validation for disk image files.
// REQ-SEC-016: Defense-in-depth checks before mounting .img/.iso/.ima files.

#pragma once

#include <cstdint>
#include <string>

namespace legends {

struct ImageValidationResult {
    bool valid = false;
    std::string error;
};

/// REQ-SEC-016: Pre-mount validation for disk image files.
/// Checks file size limits and FAT BPB header sanity before the engine
/// attempts to parse the image, providing defense-in-depth against
/// malformed or adversarial disk images.
class ImageValidator {
public:
    static constexpr size_t kMaxFATImageSize = 2ULL * 1024 * 1024 * 1024;   // 2 GB
    static constexpr size_t kMaxISOImageSize = 4700ULL * 1024 * 1024;       // ~4.7 GB (DVD)
    static constexpr int kMaxDirectoryDepth = 32;

    /// Validate a disk image file before mounting.
    /// Returns {true, ""} on success or {false, reason} on failure.
    [[nodiscard]] static ImageValidationResult validate(const std::string& path);

private:
    [[nodiscard]] static ImageValidationResult validateFAT(const std::string& path, size_t file_size);
    [[nodiscard]] static ImageValidationResult validateISO(const std::string& path, size_t file_size);
};

} // namespace legends
