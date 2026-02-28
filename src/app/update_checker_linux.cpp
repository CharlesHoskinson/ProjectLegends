// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors

#include "app/update_checker.h"

#include <memory>
#include <string>

namespace legends {

namespace {

class LinuxUpdateChecker final : public UpdateChecker {
protected:
    std::string fetchManifest() override {
        // Linux backend is intentionally a stub for now.
        // Returning empty triggers a graceful "checked with error" result.
        return {};
    }
};

} // namespace

std::unique_ptr<UpdateChecker> createPlatformUpdateChecker() {
    return std::make_unique<LinuxUpdateChecker>();
}

} // namespace legends
