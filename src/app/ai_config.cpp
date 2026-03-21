// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AI Assistant configuration — loading from INI [ai] section.

#include "app/ai_config.h"
#include "app/config_parser.h"

#include <cstdio>
#include <cstdlib>

namespace legends {

void AIConfig::loadFrom(const ConfigParser& config) {
    if (!config.hasSection("ai")) {
        return;
    }

    enabled = config.getBool("ai", "enabled", enabled);
    endpoint = config.get("ai", "endpoint", endpoint);
    model = config.get("ai", "model", model);

    // REQ-SEC-006: Detect raw API keys in config files.
    // The api_key field should contain an environment variable name, not a
    // raw secret. Refuse to load values that look like actual API keys.
    if (config.hasKey("ai", "api_key")) {
        std::string raw_value = config.get("ai", "api_key", "");
        if (raw_value.substr(0, 3) == "sk-") {
            std::fprintf(stderr,
                "Security warning: [ai] api_key contains a raw API key "
                "(starts with 'sk-'). Store keys in environment variables "
                "and use api_key_env instead. Raw key ignored.\n");
            raw_api_key_detected = true;
            // Do NOT store the raw key — leave api_key_env at its default
        }
    }

    api_key_env = config.get("ai", "api_key_env", api_key_env);
    max_tokens = static_cast<uint32_t>(
        config.getInt("ai", "max_tokens", static_cast<int>(max_tokens)));
    max_context_chars = static_cast<uint32_t>(
        config.getInt("ai", "max_context_chars", static_cast<int>(max_context_chars)));
    privacy_mode = config.getBool("ai", "privacy_mode", privacy_mode);
}

std::string AIConfig::resolveApiKey() const {
    const char* value = std::getenv(api_key_env.c_str());
    if (value == nullptr) {
        return {};
    }
    return std::string(value);
}

bool AIConfig::isValid() const {
    return enabled && !endpoint.empty() && !model.empty();
}

} // namespace legends
