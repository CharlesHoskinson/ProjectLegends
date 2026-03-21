// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AI Assistant configuration — loading from INI [ai] section.

#include "app/ai_config.h"
#include "app/config_parser.h"

#include <gsl-lite/gsl-lite.hpp>

#include <cstdlib>

namespace legends {

void AIConfig::loadFrom(const ConfigParser& config) {
    if (!config.hasSection("ai")) {
        return;
    }

    enabled = config.getBool("ai", "enabled", enabled);
    endpoint = config.get("ai", "endpoint", endpoint);
    model = config.get("ai", "model", model);
    api_key_env = config.get("ai", "api_key_env", api_key_env);
    max_tokens = gsl::narrow<uint32_t>(
        config.getInt("ai", "max_tokens", static_cast<int>(max_tokens)));
    max_context_chars = gsl::narrow<uint32_t>(
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
