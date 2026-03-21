// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors

#include "app/error_reporter.h"

#include <string_view>

namespace legends {

void ErrorReporter::report(std::string_view /*message*/) {}
void ErrorReporter::report(ErrorSeverity /*severity*/, std::string_view /*message*/) {}
void ErrorReporter::clear() {}

} // namespace legends
