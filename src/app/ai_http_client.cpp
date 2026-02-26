// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Async HTTP client for AI API calls — JSON building and parsing.

#include "app/ai_http_client.h"

#include <algorithm>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// JSON string escaping
// ─────────────────────────────────────────────────────────────────────────────

// Escape special characters for embedding in a JSON string literal.
// Handles RFC 8259 mandatory escapes (" \ and control chars 0x00-0x1F).
static std::string escapeJsonString(const std::string& input) {
    std::string result;
    result.reserve(input.size() + 16);
    for (char ch : input) {
        switch (ch) {
            case '"':  result += "\\\""; break;
            case '\\': result += "\\\\"; break;
            case '\n': result += "\\n";  break;
            case '\r': result += "\\r";  break;
            case '\t': result += "\\t";  break;
            case '\b': result += "\\b";  break;
            case '\f': result += "\\f";  break;
            default:
                if (static_cast<unsigned char>(ch) < 0x20) {
                    // Control characters: encode as \u00XX
                    const char* hex = "0123456789abcdef";
                    result += "\\u00";
                    result += hex[(static_cast<unsigned char>(ch) >> 4) & 0x0F];
                    result += hex[static_cast<unsigned char>(ch) & 0x0F];
                } else {
                    result += ch;
                }
                break;
        }
    }
    return result;
}

// ─────────────────────────────────────────────────────────────────────────────
// Build JSON request body for Anthropic Messages API
// ─────────────────────────────────────────────────────────────────────────────

std::string AIHttpClient::buildRequestJson(const AIRequest& request) {
    std::string json;
    json.reserve(512);

    json += "{\"model\":\"";
    json += escapeJsonString(request.model);
    json += "\",\"max_tokens\":";
    json += std::to_string(request.max_tokens);

    if (!request.system_prompt.empty()) {
        json += ",\"system\":\"";
        json += escapeJsonString(request.system_prompt);
        json += "\"";
    }

    json += ",\"messages\":[{\"role\":\"user\",\"content\":\"";
    json += escapeJsonString(request.user_message);
    json += "\"}]}";

    return json;
}

// ─────────────────────────────────────────────────────────────────────────────
// Parse JSON response from Anthropic Messages API
// ─────────────────────────────────────────────────────────────────────────────

static std::string extractJsonStringField(const std::string& json,
                                           const std::string& field_name) {
    // Look for "field_name":"value" pattern
    std::string search = "\"" + field_name + "\":\"";
    auto pos = json.find(search);
    if (pos == std::string::npos) {
        // Try with space after colon: "field_name": "value"
        search = "\"" + field_name + "\": \"";
        pos = json.find(search);
        if (pos == std::string::npos) {
            return {};
        }
    }

    pos += search.size();
    std::string result;
    bool escaped = false;

    for (size_t i = pos; i < json.size(); ++i) {
        char ch = json[i];
        if (escaped) {
            switch (ch) {
                case '"':  result += '"';  break;
                case '\\': result += '\\'; break;
                case 'n':  result += '\n'; break;
                case 'r':  result += '\r'; break;
                case 't':  result += '\t'; break;
                case 'b':  result += '\b'; break;
                case 'f':  result += '\f'; break;
                default:   result += ch;   break;
            }
            escaped = false;
        } else if (ch == '\\') {
            escaped = true;
        } else if (ch == '"') {
            break;
        } else {
            result += ch;
        }
    }
    return result;
}

AIResponse AIHttpClient::parseResponseJson(const std::string& json,
                                            int http_status) {
    AIResponse response;
    response.http_status = http_status;
    response.body = json;

    if (json.empty()) {
        response.success = false;
        response.error = "Empty response body";
        return response;
    }

    if (http_status >= 200 && http_status < 300) {
        // Try to extract text content from successful response
        std::string text = extractJsonStringField(json, "text");
        if (!text.empty()) {
            response.success = true;
            response.body = text;
        } else {
            response.success = false;
            response.error = "Could not extract text from response";
        }
    } else {
        // Error response — extract error message
        std::string error_msg = extractJsonStringField(json, "message");
        if (error_msg.empty()) {
            error_msg = extractJsonStringField(json, "error");
        }
        response.success = false;
        response.error = error_msg.empty()
            ? ("HTTP error " + std::to_string(http_status))
            : error_msg;
    }

    return response;
}

// ─────────────────────────────────────────────────────────────────────────────
// Constructor / Destructor
// ─────────────────────────────────────────────────────────────────────────────

AIHttpClient::AIHttpClient() = default;

AIHttpClient::~AIHttpClient() {
    stop();
}

// ─────────────────────────────────────────────────────────────────────────────
// Request submission
// ─────────────────────────────────────────────────────────────────────────────

// Queue a request under the mutex, then wake the worker via condvar.
// The worker thread (when connected) dequeues pending_request_ and
// delivers the result through completed_response_ + has_completed_.
void AIHttpClient::submitRequest(const AIRequest& request,
                                  ResponseCallback callback) {
    std::lock_guard<std::mutex> lock(mutex_);
    pending_request_ = request;
    pending_callback_ = std::move(callback);
    has_pending_ = true;
    busy_.store(true, std::memory_order_release);
    cancel_requested_.store(false, std::memory_order_release);
    cv_.notify_one();
}

// ─────────────────────────────────────────────────────────────────────────────
// Cancel
// ─────────────────────────────────────────────────────────────────────────────

void AIHttpClient::cancel() {
    cancel_requested_.store(true, std::memory_order_release);
}

// ─────────────────────────────────────────────────────────────────────────────
// Poll for completed response
// ─────────────────────────────────────────────────────────────────────────────

bool AIHttpClient::pollResponse(AIResponse& out) {
    std::lock_guard<std::mutex> lock(mutex_);
    if (!has_completed_) {
        return false;
    }
    out = completed_response_;
    has_completed_ = false;
    return true;
}

// ─────────────────────────────────────────────────────────────────────────────
// Start / Stop worker lifecycle
// ─────────────────────────────────────────────────────────────────────────────

void AIHttpClient::start() {
    running_.store(true, std::memory_order_release);
    // Actual thread creation deferred to application wiring (libcurl optional).
}

void AIHttpClient::stop() {
    running_.store(false, std::memory_order_release);
    cancel_requested_.store(true, std::memory_order_release);
    cv_.notify_all();
}

} // namespace legends
