// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors

#include "app/update_checker.h"

#include <algorithm>
#include <charconv>
#include <sstream>
#include <vector>

namespace legends {

UpdateChecker::UpdateChecker() = default;
UpdateChecker::~UpdateChecker() = default;

UpdateCheckResult UpdateChecker::checkForUpdate() {
    if (!enabled_) return {};
    if (has_checked_ && !canCheckNow()) return {};
    return forceCheck();
}

UpdateCheckResult UpdateChecker::forceCheck() {
    has_checked_ = true;
    last_check_time_ = std::chrono::steady_clock::now();

    std::string json = fetchManifest();
    if (json.empty()) {
        UpdateCheckResult r;
        r.checked = true;
        r.error = "Failed to fetch update manifest";
        return r;
    }
    return parseManifest(json);
}

bool UpdateChecker::canCheckNow() const {
    if (!has_checked_) return true;
    auto elapsed = std::chrono::steady_clock::now() - last_check_time_;
    return elapsed >= check_interval_;
}

int UpdateChecker::compareVersions(const std::string& a, const std::string& b) {
    auto parse = [](const std::string& s) {
        std::vector<int> parts;
        std::istringstream ss(s);
        std::string token;
        while (std::getline(ss, token, '.')) {
            int val = 0;
            auto [ptr, ec] = std::from_chars(token.data(), token.data() + token.size(), val);
            (void)ptr; (void)ec;
            parts.push_back(val);
        }
        return parts;
    };

    auto va = parse(a);
    auto vb = parse(b);
    size_t len = std::max(va.size(), vb.size());
    for (size_t i = 0; i < len; ++i) {
        int pa = (i < va.size()) ? va[i] : 0;
        int pb = (i < vb.size()) ? vb[i] : 0;
        if (pa < pb) return -1;
        if (pa > pb) return 1;
    }
    return 0;
}

std::string UpdateChecker::currentVersion() {
    return "0.1.0";
}

UpdateCheckResult UpdateChecker::parseManifest(const std::string& /*json*/) {
    // Minimal stub — real implementation would parse JSON
    UpdateCheckResult r;
    r.checked = true;
    r.current_version = currentVersion();
    return r;
}

} // namespace legends
