// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for AIHttpClient — JSON build/parse and state management.

#include <gtest/gtest.h>
#include "app/ai_http_client.h"

#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// buildRequestJson — basic structure
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIHttpClientTest, BuildRequestJsonProducesValidLookingJson) {
    AIRequest req;
    req.model = "test-model";
    req.user_message = "Hello";
    req.max_tokens = 100;

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_FALSE(json.empty());
    EXPECT_EQ(json.front(), '{');
    EXPECT_EQ(json.back(), '}');
}

TEST(AIHttpClientTest, BuildRequestJsonIncludesModelField) {
    AIRequest req;
    req.model = "claude-test";
    req.user_message = "Hi";

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("\"model\":\"claude-test\""), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonIncludesMaxTokens) {
    AIRequest req;
    req.model = "m";
    req.user_message = "Hi";
    req.max_tokens = 2048;

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("\"max_tokens\":2048"), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonIncludesSystemPrompt) {
    AIRequest req;
    req.model = "m";
    req.user_message = "Hi";
    req.system_prompt = "You are helpful.";

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("\"system\":\"You are helpful.\""), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonIncludesUserMessage) {
    AIRequest req;
    req.model = "m";
    req.user_message = "What is DOS?";

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("\"content\":\"What is DOS?\""), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonWithEmptySystemPrompt) {
    AIRequest req;
    req.model = "m";
    req.user_message = "Hi";
    req.system_prompt = "";

    std::string json = AIHttpClient::buildRequestJson(req);
    // No "system" key when empty
    EXPECT_EQ(json.find("\"system\""), std::string::npos);
}

// ═══════════════════════════════════════════════════════════════════════════
// buildRequestJson — escaping
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIHttpClientTest, BuildRequestJsonEscapesQuotes) {
    AIRequest req;
    req.model = "m";
    req.user_message = "He said \"hello\"";

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("He said \\\"hello\\\""), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonEscapesBackslashes) {
    AIRequest req;
    req.model = "m";
    req.user_message = "path\\to\\file";

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("path\\\\to\\\\file"), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonEscapesNewlines) {
    AIRequest req;
    req.model = "m";
    req.user_message = "line1\nline2";

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("line1\\nline2"), std::string::npos);
    // Raw newline should not appear
    EXPECT_EQ(json.find('\n'), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonEscapesTabs) {
    AIRequest req;
    req.model = "m";
    req.user_message = "col1\tcol2";

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("col1\\tcol2"), std::string::npos);
    EXPECT_EQ(json.find('\t'), std::string::npos);
}

TEST(AIHttpClientTest, BuildRequestJsonWithUnicodeContent) {
    AIRequest req;
    req.model = "m";
    req.user_message = "Caf\xC3\xA9"; // "Café" in UTF-8

    std::string json = AIHttpClient::buildRequestJson(req);
    EXPECT_NE(json.find("Caf\xC3\xA9"), std::string::npos);
}

// ═══════════════════════════════════════════════════════════════════════════
// parseResponseJson
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIHttpClientTest, ParseResponseJsonExtractsTextContent) {
    std::string json = R"({"content":[{"type":"text","text":"Hello world"}]})";
    auto resp = AIHttpClient::parseResponseJson(json, 200);
    EXPECT_TRUE(resp.success);
    EXPECT_EQ(resp.body, "Hello world");
}

TEST(AIHttpClientTest, ParseResponseJsonHandlesErrorResponse) {
    std::string json = R"({"error":{"type":"invalid_request","message":"Bad request"}})";
    auto resp = AIHttpClient::parseResponseJson(json, 400);
    EXPECT_FALSE(resp.success);
    EXPECT_FALSE(resp.error.empty());
}

TEST(AIHttpClientTest, ParseResponseJsonHandlesEmptyBody) {
    auto resp = AIHttpClient::parseResponseJson("", 200);
    EXPECT_FALSE(resp.success);
    EXPECT_EQ(resp.error, "Empty response body");
}

TEST(AIHttpClientTest, ParseResponseJsonHandlesMalformedJson) {
    auto resp = AIHttpClient::parseResponseJson("not json at all", 200);
    EXPECT_FALSE(resp.success);
}

TEST(AIHttpClientTest, ParseResponseJsonPreservesHttpStatus) {
    auto resp = AIHttpClient::parseResponseJson("{}", 503);
    EXPECT_EQ(resp.http_status, 503);
}

TEST(AIHttpClientTest, ParseResponseJsonStatus200VsStatus400) {
    std::string json_with_text = R"({"content":[{"type":"text","text":"OK"}]})";

    auto resp200 = AIHttpClient::parseResponseJson(json_with_text, 200);
    EXPECT_TRUE(resp200.success);

    auto resp400 = AIHttpClient::parseResponseJson(json_with_text, 400);
    EXPECT_FALSE(resp400.success);
}

// ═══════════════════════════════════════════════════════════════════════════
// Default state
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIHttpClientTest, DefaultStateNotBusy) {
    AIHttpClient client;
    EXPECT_FALSE(client.isBusy());
}

TEST(AIHttpClientTest, DefaultStateNotRunning) {
    AIHttpClient client;
    EXPECT_FALSE(client.isRunning());
}

// ═══════════════════════════════════════════════════════════════════════════
// Request lifecycle
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIHttpClientTest, SubmitRequestSetsBusyFlag) {
    AIHttpClient client;
    AIRequest req;
    req.model = "m";
    req.user_message = "test";
    client.submitRequest(req, [](const AIResponse&) {});
    EXPECT_TRUE(client.isBusy());
}

TEST(AIHttpClientTest, CancelSetsCancelFlag) {
    AIHttpClient client;
    client.cancel();
    // Cancel does not crash even without a pending request
    EXPECT_FALSE(client.isBusy());
}

TEST(AIHttpClientTest, PollResponseReturnsFalseInitially) {
    AIHttpClient client;
    AIResponse resp;
    EXPECT_FALSE(client.pollResponse(resp));
}

TEST(AIHttpClientTest, StartSetsRunningFlag) {
    AIHttpClient client;
    client.start();
    EXPECT_TRUE(client.isRunning());
    client.stop();
}

TEST(AIHttpClientTest, StopClearsRunningFlag) {
    AIHttpClient client;
    client.start();
    client.stop();
    EXPECT_FALSE(client.isRunning());
}

// ═══════════════════════════════════════════════════════════════════════════
// Default struct values
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIHttpClientTest, AIRequestDefaultValues) {
    AIRequest req;
    EXPECT_TRUE(req.endpoint.empty());
    EXPECT_TRUE(req.api_key.empty());
    EXPECT_TRUE(req.model.empty());
    EXPECT_TRUE(req.system_prompt.empty());
    EXPECT_TRUE(req.user_message.empty());
    EXPECT_EQ(req.max_tokens, 4096u);
}

TEST(AIHttpClientTest, AIResponseDefaultValues) {
    AIResponse resp;
    EXPECT_FALSE(resp.success);
    EXPECT_EQ(resp.http_status, 0);
    EXPECT_TRUE(resp.body.empty());
    EXPECT_TRUE(resp.error.empty());
}

} // namespace
} // namespace legends
