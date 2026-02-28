// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Crash reporter — captures and persists crash diagnostics.

#pragma once

#include <string>

namespace legends {

class CrashReporter {
public:
    CrashReporter()  = default;
    ~CrashReporter() = default;

    void install();
    void uninstall();
    bool enable(const std::string& crash_dir);
    void disable();
};

CrashReporter& globalCrashReporter();

} // namespace legends
