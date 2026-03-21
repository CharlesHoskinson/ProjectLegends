// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AI Assistant overlay panel.

#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace legends {

class ActionBus;

struct AIChatMessage {
    bool is_user;           // true = user, false = assistant
    std::string text;
};

class AIPanel {
public:
    void initialize(ActionBus* bus);

    void open();
    void close();
    [[nodiscard]] bool isOpen() const { return open_; }

    /// Handle keyboard input. Returns true if consumed.
    [[nodiscard]] bool handleKey(uint16_t scancode, bool down, uint8_t character = 0);

    /// Handle text character input.
    void handleTextInput(char ch);

    /// Add a response message from the AI.
    void addResponse(const std::string& text);

    /// Add a user message (shown in chat).
    void addUserMessage(const std::string& text);

    /// Set streaming text (partial response).
    void setStreamingText(const std::string& text);

    /// Clear all chat history.
    void clearHistory();

    /// Get current input text.
    [[nodiscard]] const std::string& inputText() const { return input_text_; }

    /// Get chat history.
    [[nodiscard]] const std::vector<AIChatMessage>& history() const { return history_; }

    /// Get number of messages.
    [[nodiscard]] size_t messageCount() const { return history_.size(); }

    /// Render the AI panel overlay into an RGB24 buffer.
    void render(uint8_t* rgb_buffer, uint16_t width, uint16_t height,
                uint32_t pitch = 0) const;

    /// Get panel width as fraction of screen (0.0-1.0).
    [[nodiscard]] float panelWidthFraction() const { return panel_width_fraction_; }

    /// Is the panel waiting for a response?
    [[nodiscard]] bool isWaiting() const { return waiting_; }

    void setWaiting(bool w) { waiting_ = w; }

private:
    void submitQuery();

    ActionBus* bus_ = nullptr;
    bool open_ = false;
    bool waiting_ = false;
    std::string input_text_;
    std::string streaming_text_;
    std::vector<AIChatMessage> history_;
    int scroll_offset_ = 0;
    float panel_width_fraction_ = 0.4f;

    static constexpr int kCharW = 8;
    static constexpr int kCharH = 16;
    static constexpr int kPadding = 8;
};

} // namespace legends
