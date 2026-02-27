// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MountManager — host directory and disk image mounting implementation.
// REQ-MOUNT-001: Host directory mounting
// REQ-MOUNT-002: Block device image mounting

#include "app/mount_manager.h"

#include <algorithm>
#include <cctype>
#include <filesystem>
#include <string>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// Static Utilities
// ─────────────────────────────────────────────────────────────────────────────

int MountManager::parseDriveLetter(const std::string& letter) {
    if (letter.size() != 1) return -1;
    char c = letter[0];
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a';
    return -1;
}

bool MountManager::validateHostPath(const std::string& path) {
    if (path.empty()) return false;

    // Reject path traversal attempts
    if (path.find("..") != std::string::npos) return false;

    std::error_code ec;
    return std::filesystem::is_directory(path, ec) && !ec;
}

bool MountManager::validateImageExtension(const std::string& ext) {
    if (ext.empty()) return false;

    std::string lower = ext;
    std::transform(lower.begin(), lower.end(), lower.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });

    return lower == ".iso" || lower == ".img" || lower == ".ima" ||
           lower == ".cue" || lower == ".bin";
}

MountType MountManager::detectMountType(const std::string& path) {
    // Check if it's a directory first
    std::error_code ec;
    if (std::filesystem::is_directory(path, ec) && !ec) {
        return MountType::Directory;
    }

    // Detect by file extension
    std::filesystem::path p(path);
    std::string ext = p.extension().string();
    std::transform(ext.begin(), ext.end(), ext.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });

    if (ext == ".iso" || ext == ".cue") return MountType::ISO;
    return MountType::FATImage;  // .img, .ima, .bin, or unknown
}

std::optional<MountArg> MountManager::parseMountArg(const std::string& arg) {
    if (arg.empty()) return std::nullopt;

    // Expected format: "D:=/path/to/dir"
    auto sep = arg.find(":=");
    if (sep == std::string::npos || sep != 1) return std::nullopt;

    char letter = arg[0];
    if (!isValidLetter(letter)) return std::nullopt;

    std::string path = arg.substr(3);  // Skip "X:="
    if (path.empty()) return std::nullopt;

    return MountArg{normalizeLetter(letter), path};
}

// ─────────────────────────────────────────────────────────────────────────────
// Instance Methods
// ─────────────────────────────────────────────────────────────────────────────

bool MountManager::mountLocal(char letter, const std::string& path, uint32_t flags) {
    gsl_Expects(isValidLetter(letter));
    gsl_Expects(!path.empty());

    char norm = normalizeLetter(letter);
    size_t idx = letterToIndex(norm);

    if (mounts_[idx].has_value()) {
        last_error_ = std::string("Drive ") + norm + " is already mounted";
        return false;
    }

    if (!validateHostPath(path)) {
        last_error_ = "Invalid host path: " + path;
        return false;
    }

    mounts_[idx] = MountInfo{norm, path, MountType::Directory, flags};
    last_error_.clear();
    return true;
}

bool MountManager::mountImage(char letter, const std::string& path, MountType type,
                               uint32_t flags) {
    gsl_Expects(isValidLetter(letter));
    gsl_Expects(!path.empty());
    gsl_Expects(type == MountType::ISO || type == MountType::FATImage);

    char norm = normalizeLetter(letter);
    size_t idx = letterToIndex(norm);

    if (mounts_[idx].has_value()) {
        last_error_ = std::string("Drive ") + norm + " is already mounted";
        return false;
    }

    // Verify file exists
    std::error_code ec;
    if (!std::filesystem::exists(path, ec) || ec) {
        last_error_ = "Image file not found: " + path;
        return false;
    }

    mounts_[idx] = MountInfo{norm, path, type, flags};
    last_error_.clear();
    return true;
}

bool MountManager::unmount(char letter) {
    gsl_Expects(isValidLetter(letter));

    size_t idx = letterToIndex(letter);
    if (!mounts_[idx].has_value()) {
        last_error_ = std::string("Drive ") + normalizeLetter(letter) + " is not mounted";
        return false;
    }

    mounts_[idx].reset();
    last_error_.clear();
    return true;
}

bool MountManager::isMounted(char letter) const {
    gsl_Expects(isValidLetter(letter));
    return mounts_[letterToIndex(letter)].has_value();
}

std::optional<MountInfo> MountManager::getMountInfo(char letter) const {
    if (!isValidLetter(letter)) return std::nullopt;
    return mounts_[letterToIndex(letter)];
}

} // namespace legends
