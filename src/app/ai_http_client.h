// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Async HTTP client for AI API calls.

#pragma once

#include <atomic>
#include <cstdint>
#include <functional>
#include <mutex>
#include <string>
#include <vector>
#include <condition_variable>

namespace legends {

struct AIRequest {
    std::string endpoint;
    std::string api_key;
    std::string model;
    std::string system_prompt;
    std::string user_message;
    uint32_t max_tokens = 4096;
};

struct AIResponse {
    bool success = false;
    int http_status = 0;
    std::string body;
    std::string error;
};

class AIHttpClient {
public:
    using ResponseCallback = std::function<void(const AIResponse&)>;

    AIHttpClient();
    ~AIHttpClient();

    AIHttpClient(const AIHttpClient&) = delete;
    AIHttpClient& operator=(const AIHttpClient&) = delete;

    /// Submit async request. Callback invoked on worker thread.
    void submitRequest(const AIRequest& request, ResponseCallback callback);

    /// Check if a request is in progress.
    [[nodiscard]] bool isBusy() const { return busy_.load(std::memory_order_acquire); }

    /// Cancel pending request.
    void cancel();

    /// Poll for completed response. Returns true if response ready.
    [[nodiscard]] bool pollResponse(AIResponse& out);

    /// Start worker thread.
    void start();

    /// Stop worker thread.
    void stop();

    [[nodiscard]] bool isRunning() const { return running_.load(std::memory_order_acquire); }

    /// Build JSON request body for Anthropic Messages API.
    [[nodiscard]] static std::string buildRequestJson(const AIRequest& request);

    /// Parse JSON response from Anthropic Messages API.
    [[nodiscard]] static AIResponse parseResponseJson(const std::string& json, int http_status);

private:
    std::atomic<bool> running_{false};
    std::atomic<bool> busy_{false};
    std::atomic<bool> cancel_requested_{false};

    mutable std::mutex mutex_;
    std::condition_variable cv_;

    // Pending request
    AIRequest pending_request_;
    ResponseCallback pending_callback_;
    bool has_pending_ = false;

    // Completed response
    AIResponse completed_response_;
    bool has_completed_ = false;
};

} // namespace legends
