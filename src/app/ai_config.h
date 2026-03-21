// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AI Assistant configuration from [ai] config section.

#pragma once

#include <cstdint>
#include <string>

namespace legends {

class ConfigParser;

/// Configuration for the AI assistant feature.
struct AIConfig {
    bool enabled = false;                   ///< Whether the AI assistant is active.
    std::string endpoint = "https://api.anthropic.com/v1/messages"; ///< API endpoint URL.
    std::string model = "claude-sonnet-4-20250514";       ///< Model identifier for API requests.
    std::string api_key_env = "ANTHROPIC_API_KEY"; ///< Environment variable holding the API key.
    uint32_t max_tokens = 4096;             ///< Maximum tokens in API response.
    uint32_t max_context_chars = 8000;      ///< Max characters of screen context to send.
    bool privacy_mode = false;              ///< When true, disables all API calls.

    /// Load from [ai] section of config.
    void loadFrom(const ConfigParser& config);

    /// Resolve API key from environment variable.
    [[nodiscard]] std::string resolveApiKey() const;

    /// Validate configuration.
    [[nodiscard]] bool isValid() const;
};

} // namespace legends
