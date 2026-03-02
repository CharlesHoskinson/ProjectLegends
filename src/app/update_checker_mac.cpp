// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// macOS update checker: stub until NSURLSession backend is integrated.

#include "app/update_checker.h"

#include <memory>

#if defined(__APPLE__)

namespace legends {

class MacUpdateChecker : public UpdateChecker {
protected:
    std::string fetchManifest() override {
        // TODO: Implement using NSURLSession via Objective-C++
        return {};
    }
};

std::unique_ptr<UpdateChecker> createPlatformUpdateChecker() {
    return std::make_unique<MacUpdateChecker>();
}

} // namespace legends

#endif
