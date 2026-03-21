// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors

#include "app/crash_reporter.h"

#include <string_view>

namespace legends {

void CrashReporter::install() {}
void CrashReporter::uninstall() {}
bool CrashReporter::enable(std::string_view /*crash_dir*/) { return true; }
void CrashReporter::disable() {}

CrashReporter& globalCrashReporter() {
    static CrashReporter instance;
    return instance;
}

} // namespace legends
