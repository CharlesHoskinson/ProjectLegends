// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Linux update checker: stub until HTTP backend is integrated.

#include "app/update_checker.h"

#include <memory>

#if !defined(_WIN32) && !defined(__APPLE__)

namespace legends {

class LinuxUpdateChecker : public UpdateChecker {
protected:
    std::string fetchManifest() override {
        // TODO: Implement using libcurl or raw sockets
        return {};
    }
};

std::unique_ptr<UpdateChecker> createPlatformUpdateChecker() {
    return std::make_unique<LinuxUpdateChecker>();
}

} // namespace legends

#endif
