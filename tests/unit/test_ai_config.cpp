// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for AIConfig.

#include <gtest/gtest.h>
#include "app/ai_config.h"

#include <cstdlib>
#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Default values
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIConfigTest, DefaultEnabledIsFalse) {
    AIConfig config;
    EXPECT_FALSE(config.enabled);
}

TEST(AIConfigTest, DefaultEndpointIsAnthropicApi) {
    AIConfig config;
    EXPECT_EQ(config.endpoint, "https://api.anthropic.com/v1/messages");
}

TEST(AIConfigTest, DefaultModelIsClaudeSonnet) {
    AIConfig config;
    EXPECT_EQ(config.model, "claude-sonnet-4-20250514");
}

TEST(AIConfigTest, DefaultApiKeyEnvIsAnthropicApiKey) {
    AIConfig config;
    EXPECT_EQ(config.api_key_env, "ANTHROPIC_API_KEY");
}

TEST(AIConfigTest, DefaultMaxTokensIs4096) {
    AIConfig config;
    EXPECT_EQ(config.max_tokens, 4096u);
}

TEST(AIConfigTest, DefaultMaxContextCharsIs8000) {
    AIConfig config;
    EXPECT_EQ(config.max_context_chars, 8000u);
}

TEST(AIConfigTest, DefaultPrivacyModeIsFalse) {
    AIConfig config;
    EXPECT_FALSE(config.privacy_mode);
}

TEST(AIConfigTest, AllStringDefaultsAreNonEmpty) {
    AIConfig config;
    EXPECT_FALSE(config.endpoint.empty());
    EXPECT_FALSE(config.model.empty());
    EXPECT_FALSE(config.api_key_env.empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// isValid
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIConfigTest, IsValidReturnsFalseWhenDisabled) {
    AIConfig config;
    // Default: enabled = false
    EXPECT_FALSE(config.isValid());
}

TEST(AIConfigTest, IsValidReturnsTrueWhenEnabledWithDefaults) {
    AIConfig config;
    config.enabled = true;
    EXPECT_TRUE(config.isValid());
}

TEST(AIConfigTest, IsValidReturnsFalseWithEmptyEndpoint) {
    AIConfig config;
    config.enabled = true;
    config.endpoint.clear();
    EXPECT_FALSE(config.isValid());
}

TEST(AIConfigTest, IsValidReturnsFalseWithEmptyModel) {
    AIConfig config;
    config.enabled = true;
    config.model.clear();
    EXPECT_FALSE(config.isValid());
}

// ═══════════════════════════════════════════════════════════════════════════
// resolveApiKey
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIConfigTest, ResolveApiKeyReturnsEmptyWhenEnvVarNotSet) {
    AIConfig config;
    config.api_key_env = "LEGENDS_TEST_NONEXISTENT_KEY_XYZ_12345";
    EXPECT_TRUE(config.resolveApiKey().empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// Struct direct manipulation
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIConfigTest, PrivacyModeCanBeSetTrue) {
    AIConfig config;
    config.privacy_mode = true;
    EXPECT_TRUE(config.privacy_mode);
}

TEST(AIConfigTest, ConfigCopyWorksCorrectly) {
    AIConfig original;
    original.enabled = true;
    original.endpoint = "https://example.com/api";
    original.model = "test-model";
    original.max_tokens = 1024;

    AIConfig copy = original;
    EXPECT_EQ(copy.enabled, original.enabled);
    EXPECT_EQ(copy.endpoint, original.endpoint);
    EXPECT_EQ(copy.model, original.model);
    EXPECT_EQ(copy.max_tokens, original.max_tokens);
}

TEST(AIConfigTest, MultipleConfigsDoNotInterfere) {
    AIConfig a;
    a.enabled = true;
    a.model = "model-a";

    AIConfig b;
    b.enabled = false;
    b.model = "model-b";

    EXPECT_TRUE(a.enabled);
    EXPECT_FALSE(b.enabled);
    EXPECT_EQ(a.model, "model-a");
    EXPECT_EQ(b.model, "model-b");
}

TEST(AIConfigTest, EdgeMaxTokensZero) {
    AIConfig config;
    config.enabled = true;
    config.max_tokens = 0;
    // Still valid — max_tokens=0 doesn't affect isValid
    EXPECT_TRUE(config.isValid());
}

TEST(AIConfigTest, EdgeMaxContextCharsZero) {
    AIConfig config;
    config.max_context_chars = 0;
    EXPECT_EQ(config.max_context_chars, 0u);
}

TEST(AIConfigTest, EndpointUrlFormatPreserved) {
    AIConfig config;
    config.endpoint = "https://custom.api.example.com/v2/chat";
    EXPECT_EQ(config.endpoint, "https://custom.api.example.com/v2/chat");
}

TEST(AIConfigTest, ModelNamePreserved) {
    AIConfig config;
    config.model = "my-custom-model-v3";
    EXPECT_EQ(config.model, "my-custom-model-v3");
}

TEST(AIConfigTest, ApiKeyEnvPreserved) {
    AIConfig config;
    config.api_key_env = "MY_CUSTOM_API_KEY";
    EXPECT_EQ(config.api_key_env, "MY_CUSTOM_API_KEY");
}

} // namespace
} // namespace legends
