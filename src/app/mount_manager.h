// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MountManager — host directory and disk image mounting for DOS drive letters.
// REQ-MOUNT-001: Host directory mounting
// REQ-MOUNT-002: Block device image mounting (.iso, .img, .ima, .cue, .bin)

#pragma once

#include <legends/gsl.hpp>

#include <array>
#include <cstdint>
#include <optional>
#include <string>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// Mount Types
// ─────────────────────────────────────────────────────────────────────────────

/// @brief Type of mount source.
enum class MountType : uint8_t {
    Directory,  ///< Host filesystem directory
    FATImage,   ///< FAT12/16/32 disk image (.img, .ima, .bin)
    ISO,        ///< ISO 9660 / UDF image (.iso, .cue)
};

/// @brief Information about a mounted drive.
/// @requirement REQ-MOUNT-001, REQ-MOUNT-002
struct MountInfo {
    char letter;            ///< Drive letter ('A'-'Z')
    std::string host_path;  ///< Path on the host filesystem
    MountType type;         ///< Type of mount source
    uint32_t flags;         ///< Mount flags (LEGENDS_MOUNT_FLAG_*)
};

/// @brief Parsed CLI mount argument (e.g., "D:=/path/to/dir").
struct MountArg {
    char letter;            ///< Drive letter ('A'-'Z'), normalized to uppercase
    std::string host_path;  ///< Host path
};

// ─────────────────────────────────────────────────────────────────────────────
// MountManager
// ─────────────────────────────────────────────────────────────────────────────

/// @brief Manages DOS drive letter mounts (host directories and disk images).
///
/// Tracks which drive letters are mounted and their source paths. Provides
/// static utility methods for parsing and validation, and instance methods
/// for mount/unmount state management.
///
/// All public methods accepting drive letters enforce gsl_Expects(isValidLetter).
///
/// @requirement REQ-MOUNT-001, REQ-MOUNT-002
class MountManager {
public:
    // ── Static Utilities ────────────────────────────────────────────────────

    /// @brief Parse a single-character drive letter string to index (0-25).
    /// @param letter Single character string ("A"-"Z", case-insensitive)
    /// @return Drive index (0-25) or -1 if invalid
    static int parseDriveLetter(const std::string& letter);

    /// @brief Check if a host path is an existing directory (no traversal).
    /// @param path Host filesystem path
    /// @return true if path exists and is a directory with no ".." components
    static bool validateHostPath(const std::string& path);

    /// @brief Check if a file extension is a supported image format.
    /// @param ext File extension including dot (e.g., ".iso")
    /// @return true if extension is supported (.iso, .img, .ima, .cue, .bin)
    static bool validateImageExtension(const std::string& ext);

    /// @brief Detect mount type from a host path.
    ///
    /// If the path is an existing directory, returns Directory.
    /// Otherwise inspects the file extension.
    ///
    /// @param path Host path (directory or image file)
    /// @return Detected mount type
    static MountType detectMountType(const std::string& path);

    /// @brief Parse a CLI mount argument string (e.g., "D:=/path/to/dir").
    /// @param arg CLI argument string
    /// @return Parsed MountArg if valid, std::nullopt otherwise
    static std::optional<MountArg> parseMountArg(const std::string& arg);

    // ── Instance Methods ────────────────────────────────────────────────────

    /// @brief Mount a host directory to a drive letter.
    /// @param letter Drive letter ('A'-'Z')
    /// @param path Host directory path
    /// @param flags Optional mount flags (default 0)
    /// @return true on success, false if already mounted or path invalid
    /// @pre letter is 'A'-'Z' (gsl_Expects)
    /// @pre path is not empty (gsl_Expects)
    bool mountLocal(char letter, const std::string& path, uint32_t flags = 0);

    /// @brief Mount a disk image to a drive letter.
    /// @param letter Drive letter ('A'-'Z')
    /// @param path Host image file path
    /// @param type Image type (ISO or FATImage)
    /// @param flags Optional mount flags (default 0)
    /// @return true on success, false if already mounted or path invalid
    /// @pre letter is 'A'-'Z' (gsl_Expects)
    /// @pre path is not empty (gsl_Expects)
    bool mountImage(char letter, const std::string& path, MountType type,
                    uint32_t flags = 0);

    /// @brief Unmount a drive letter.
    /// @param letter Drive letter ('A'-'Z')
    /// @return true if drive was mounted and is now unmounted, false if not mounted
    /// @pre letter is 'A'-'Z' (gsl_Expects)
    bool unmount(char letter);

    /// @brief Check if a drive letter is currently mounted.
    /// @param letter Drive letter ('A'-'Z')
    /// @return true if mounted
    /// @pre letter is 'A'-'Z' (gsl_Expects)
    bool isMounted(char letter) const;

    /// @brief Get mount information for a drive letter.
    /// @param letter Drive letter ('A'-'Z')
    /// @return MountInfo if mounted, std::nullopt otherwise
    std::optional<MountInfo> getMountInfo(char letter) const;

    /// @brief Get the last error message (for UI display).
    /// @return Last error string, empty if no error
    const std::string& lastError() const { return last_error_; }

private:
    /// @brief Validate that a character is a valid drive letter ('A'-'Z').
    static bool isValidLetter(char c) {
        return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
    }

    /// @brief Normalize a drive letter to uppercase.
    static char normalizeLetter(char c) {
        return (c >= 'a' && c <= 'z') ? static_cast<char>(c - 'a' + 'A') : c;
    }

    /// @brief Convert drive letter to array index (0-25).
    static size_t letterToIndex(char c) {
        return static_cast<size_t>(normalizeLetter(c) - 'A');
    }

    std::array<std::optional<MountInfo>, 26> mounts_{};
    std::string last_error_;
};

} // namespace legends
