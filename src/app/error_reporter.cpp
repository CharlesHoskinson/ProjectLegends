// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors

#include "app/error_reporter.h"

namespace legends {

void ErrorReporter::report(const std::string& /*message*/) {}
void ErrorReporter::report(ErrorSeverity /*severity*/, const std::string& /*message*/) {}
void ErrorReporter::clear() {}

} // namespace legends
