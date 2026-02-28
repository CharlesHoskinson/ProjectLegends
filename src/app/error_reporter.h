// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Error reporter — collects and displays user-facing error summaries.

#pragma once

#include <string>

namespace legends {

enum class ErrorSeverity {
    Info,
    Warning,
    Error,
};

class ErrorReporter {
public:
    ErrorReporter()  = default;
    ~ErrorReporter() = default;

    void report(const std::string& message);
    void report(ErrorSeverity severity, const std::string& message);
    void clear();
};

} // namespace legends
