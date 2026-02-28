// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MountManager — host directory and disk image mounting implementation.
// REQ-MOUNT-001: Host directory mounting
// REQ-MOUNT-002: Block device image mounting

#include "app/mount_manager.h"
#include "app/image_validator.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
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

    // REQ-SEC-023: Canonicalize the path to resolve "..", ".", and symlinks.
    // This replaces the naive path.find("..") string check with proper
    // filesystem resolution that handles symlink traversal attacks.
    std::error_code ec;
    auto canonical = std::filesystem::weakly_canonical(path, ec);
    if (ec) return false;

    return std::filesystem::is_directory(canonical, ec) && !ec;
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

// REQ-SEC-025: Check if a path refers to a sensitive system directory.
static bool isSensitivePath(const std::filesystem::path& p) {
    std::string s = p.string();

#ifdef _WIN32
    // Normalize to forward slashes for comparison
    std::replace(s.begin(), s.end(), '\\', '/');
    std::string lower = s;
    std::transform(lower.begin(), lower.end(), lower.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });

    if (lower.find("c:/windows") == 0) return true;
    if (lower.find("c:/program files") == 0) return true;
    if (lower.find("c:/programdata") == 0) return true;
#else
    if (s == "/" || s == "/etc" || s == "/usr" || s == "/bin" ||
        s == "/sbin" || s == "/lib" || s == "/var" || s == "/boot" ||
        s == "/proc" || s == "/sys" || s == "/dev") return true;
    if (s.find("/etc/") == 0 || s.find("/usr/") == 0) return true;
#endif

    // Home directory root (mounting ~ itself is risky)
    const char* home = std::getenv("HOME");
    if (!home) home = std::getenv("USERPROFILE");
    if (home && s == home) return true;

    return false;
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

    // REQ-SEC-023: Store the canonical path to prevent traversal via symlinks.
    std::error_code ec;
    auto resolved = std::filesystem::weakly_canonical(path, ec);
    std::string stored_path = ec ? path : resolved.string();

    // REQ-SEC-025: Warn when mounting sensitive system directories.
    if (isSensitivePath(resolved)) {
        std::fprintf(stderr,
            "Warning: Mounting sensitive directory '%s' as drive %c: "
            "— this may expose system files to the guest\n",
            stored_path.c_str(), norm);
    }

    mounts_[idx] = MountInfo{norm, stored_path, MountType::Directory, flags};
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

    // REQ-SEC-016: Validate image structure before mounting.
    auto result = ImageValidator::validate(path);
    if (!result.valid) {
        last_error_ = "Image validation failed: " + result.error;
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
