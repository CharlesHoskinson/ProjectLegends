// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AI screen context capture — converts screen text to context string.

#pragma once

#include <legends/legends_embed.h>
#include <cstdint>
#include <string>

namespace legends {

/// Convert CP437 character to UTF-8 string.
[[nodiscard]] std::string cp437ToUtf8(uint8_t cp437_char);

/// Capture current screen text as UTF-8 context string.
/// Truncates to max_chars if needed.
[[nodiscard]] std::string captureScreenContext(legends_handle handle, uint32_t max_chars = 8000);

/// Format screen text into a structured context prompt.
[[nodiscard]] std::string formatScreenContext(const std::string& screen_text,
                                uint8_t cursor_x, uint8_t cursor_y,
                                uint8_t columns, uint8_t rows);

} // namespace legends
