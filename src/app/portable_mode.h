// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Portable mode detection and directory redirection.

#pragma once

#include <string>

namespace legends {

[[nodiscard]] std::string getExecutableDir();
[[nodiscard]] bool        isPortableMode();
[[nodiscard]] std::string getPortableBaseDir();

} // namespace legends
