// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Portable mode detection and directory redirection.

#pragma once

#include <string>

namespace legends {

std::string getExecutableDir();
bool        isPortableMode();
std::string getPortableBaseDir();

} // namespace legends
