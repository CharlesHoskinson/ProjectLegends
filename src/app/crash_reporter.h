// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Crash reporter — captures and persists crash diagnostics.

#pragma once

#include <string>
#include <string_view>

namespace legends {

class CrashReporter {
public:
    CrashReporter()  = default;
    ~CrashReporter() = default;

    void install();
    void uninstall();
<<<<<<< HEAD
    [[nodiscard]] bool enable(const std::string& crash_dir);
=======
    bool enable(std::string_view crash_dir);
>>>>>>> worktree-agent-a4ab30fc
    void disable();
};

[[nodiscard]] CrashReporter& globalCrashReporter();

} // namespace legends
