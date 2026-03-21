// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Abstract update checker: opt-in version comparison against remote manifest.
// REQ-OPS-017: Update checking with opt-in, rate limiting, version comparison.

#pragma once

#include <chrono>
#include <cstdint>
#include <string>

namespace legends {

/// Result of an update check.
struct UpdateCheckResult {
    bool        checked    = false;   // Whether a check was performed
    bool        available  = false;   // Whether an update is available
    std::string current_version;      // Current installed version
    std::string latest_version;       // Latest available version
    std::string download_url;         // URL to download the update
    std::string release_notes;        // Brief release notes
    std::string error;                // Error message if check failed
};

/// Abstract update checker with opt-in gating and rate limiting.
///
/// Platform-specific implementations fetch a JSON manifest from a known
/// URL and compare versions. Checks are opt-in only and rate-limited
/// to once per 24 hours.
class UpdateChecker {
public:
    UpdateChecker();
    virtual ~UpdateChecker();

    UpdateChecker(const UpdateChecker&) = delete;
    UpdateChecker& operator=(const UpdateChecker&) = delete;

    /// Enable update checking. Must be called before checkForUpdate().
    void setEnabled(bool enabled) { enabled_ = enabled; }

    /// Check if update checking is enabled.
    [[nodiscard]] bool isEnabled() const { return enabled_; }

    /// Set the minimum interval between checks (default: 24 hours).
    void setCheckInterval(std::chrono::seconds interval) { check_interval_ = interval; }

    /// Get the check interval.
    [[nodiscard]] std::chrono::seconds checkInterval() const { return check_interval_; }

    /// Perform an update check. Returns immediately if:
    /// - Update checking is disabled
    /// - A check was performed less than check_interval ago
    [[nodiscard]] UpdateCheckResult checkForUpdate();

    /// Force an update check regardless of rate limiting.
    [[nodiscard]] UpdateCheckResult forceCheck();

    /// Get the time of the last successful check.
    [[nodiscard]] std::chrono::steady_clock::time_point lastCheckTime() const { return last_check_time_; }

    /// Check if enough time has passed since the last check.
    [[nodiscard]] bool canCheckNow() const;

    /// Compare two version strings (e.g., "1.0.0" vs "1.1.0").
    /// Returns: -1 if a < b, 0 if a == b, 1 if a > b.
    [[nodiscard]] static int compareVersions(const std::string& a, const std::string& b);

    /// Get the current application version.
    [[nodiscard]] static std::string currentVersion();

protected:
    /// Platform-specific: fetch the update manifest JSON from the remote server.
    /// Implementations should return the raw JSON string or empty on error.
    [[nodiscard]] virtual std::string fetchManifest() = 0;

    /// Parse the manifest JSON and populate the result.
    [[nodiscard]] UpdateCheckResult parseManifest(const std::string& json);

private:
    bool        enabled_  = false;
    std::chrono::seconds check_interval_{86400}; // 24 hours
    std::chrono::steady_clock::time_point last_check_time_;
    bool        has_checked_ = false;
};

/// Factory: create the platform-specific update checker.
[[nodiscard]] std::unique_ptr<UpdateChecker> createPlatformUpdateChecker();

} // namespace legends
