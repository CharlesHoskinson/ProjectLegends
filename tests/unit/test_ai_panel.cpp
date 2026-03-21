// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for AIPanel overlay.

#include <gtest/gtest.h>
#include "app/ai_panel.h"
#include "app/action_bus.h"

#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Default state
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, DefaultStateNotOpen) {
    AIPanel panel;
    EXPECT_FALSE(panel.isOpen());
}

TEST(AIPanelTest, DefaultIsWaitingFalse) {
    AIPanel panel;
    EXPECT_FALSE(panel.isWaiting());
}

TEST(AIPanelTest, DefaultPanelWidthFraction) {
    AIPanel panel;
    EXPECT_FLOAT_EQ(panel.panelWidthFraction(), 0.4f);
}

TEST(AIPanelTest, DefaultInputTextEmpty) {
    AIPanel panel;
    EXPECT_TRUE(panel.inputText().empty());
}

TEST(AIPanelTest, DefaultMessageCountZero) {
    AIPanel panel;
    EXPECT_EQ(panel.messageCount(), 0u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Open / Close
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, OpenCloseCycle) {
    AIPanel panel;
    panel.open();
    EXPECT_TRUE(panel.isOpen());
    panel.close();
    EXPECT_FALSE(panel.isOpen());
}

TEST(AIPanelTest, OpenCloseToggle) {
    AIPanel panel;
    panel.open();
    EXPECT_TRUE(panel.isOpen());
    panel.close();
    EXPECT_FALSE(panel.isOpen());
    panel.open();
    EXPECT_TRUE(panel.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Text input
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, HandleTextInputAppendsCharacters) {
    AIPanel panel;
    panel.open();
    panel.handleTextInput('H');
    panel.handleTextInput('i');
    EXPECT_EQ(panel.inputText(), "Hi");
}

TEST(AIPanelTest, HandleTextInputWithSpecialChars) {
    AIPanel panel;
    panel.open();
    panel.handleTextInput('!');
    panel.handleTextInput('@');
    panel.handleTextInput('#');
    EXPECT_EQ(panel.inputText(), "!@#");
}

// ═══════════════════════════════════════════════════════════════════════════
// Key handling
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, HandleKeyBackspaceRemovesLastChar) {
    AIPanel panel;
    panel.open();
    panel.handleTextInput('A');
    panel.handleTextInput('B');
    panel.handleTextInput('C');
    // Backspace scancode = 0x2A
    panel.handleKey(0x2A, true);
    EXPECT_EQ(panel.inputText(), "AB");
}

TEST(AIPanelTest, HandleKeyEscapeClosesPanel) {
    AIPanel panel;
    panel.open();
    EXPECT_TRUE(panel.isOpen());
    // Escape scancode = 0x29
    panel.handleKey(0x29, true);
    EXPECT_FALSE(panel.isOpen());
}

TEST(AIPanelTest, HandleKeyEnterOnEmptyInputDoesNothing) {
    AIPanel panel;
    ActionBus bus;
    panel.initialize(&bus);
    panel.open();
    // Enter scancode = 0x28, input is empty
    panel.handleKey(0x28, true);
    EXPECT_EQ(panel.messageCount(), 0u);
}

TEST(AIPanelTest, HandleKeyWithPanelClosedReturnsFalse) {
    AIPanel panel;
    // Panel is closed by default
    bool consumed = panel.handleKey(0x28, true);
    EXPECT_FALSE(consumed);
}

TEST(AIPanelTest, HandleKeyUpDownDoesNotCrash) {
    AIPanel panel;
    panel.open();
    // Up = 0x52, Down = 0x51
    EXPECT_TRUE(panel.handleKey(0x52, true));
    EXPECT_TRUE(panel.handleKey(0x51, true));
}

// ═══════════════════════════════════════════════════════════════════════════
// Chat history
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, AddResponseAddsToHistory) {
    AIPanel panel;
    panel.addResponse("Hello from AI");
    EXPECT_EQ(panel.messageCount(), 1u);
}

TEST(AIPanelTest, AddUserMessageAddsToHistory) {
    AIPanel panel;
    panel.addUserMessage("Hello from user");
    EXPECT_EQ(panel.messageCount(), 1u);
}

TEST(AIPanelTest, UserMessageIsUserTrue) {
    AIPanel panel;
    panel.addUserMessage("question");
    EXPECT_TRUE(panel.history()[0].is_user);
}

TEST(AIPanelTest, ResponseMessageIsUserFalse) {
    AIPanel panel;
    panel.addResponse("answer");
    EXPECT_FALSE(panel.history()[0].is_user);
}

TEST(AIPanelTest, MessageCountTracksCorrectly) {
    AIPanel panel;
    panel.addUserMessage("q1");
    panel.addResponse("a1");
    panel.addUserMessage("q2");
    EXPECT_EQ(panel.messageCount(), 3u);
}

TEST(AIPanelTest, HistoryPreservesOrder) {
    AIPanel panel;
    panel.addUserMessage("first");
    panel.addResponse("second");
    panel.addUserMessage("third");

    ASSERT_EQ(panel.history().size(), 3u);
    EXPECT_EQ(panel.history()[0].text, "first");
    EXPECT_TRUE(panel.history()[0].is_user);
    EXPECT_EQ(panel.history()[1].text, "second");
    EXPECT_FALSE(panel.history()[1].is_user);
    EXPECT_EQ(panel.history()[2].text, "third");
    EXPECT_TRUE(panel.history()[2].is_user);
}

TEST(AIPanelTest, ClearHistoryEmptiesMessages) {
    AIPanel panel;
    panel.addUserMessage("msg1");
    panel.addResponse("msg2");
    EXPECT_EQ(panel.messageCount(), 2u);
    panel.clearHistory();
    EXPECT_EQ(panel.messageCount(), 0u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Waiting state
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, SetWaitingTogglesState) {
    AIPanel panel;
    panel.setWaiting(true);
    EXPECT_TRUE(panel.isWaiting());
    panel.setWaiting(false);
    EXPECT_FALSE(panel.isWaiting());
}

// ═══════════════════════════════════════════════════════════════════════════
// Streaming text
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, SetStreamingTextUpdatesDisplay) {
    AIPanel panel;
    panel.setStreamingText("partial response...");
    // Streaming text does not add to history
    EXPECT_EQ(panel.messageCount(), 0u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Initialization
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, InitializeWithNullBusDoesNotCrash) {
    AIPanel panel;
    EXPECT_NO_THROW(panel.initialize(nullptr));
}

// ═══════════════════════════════════════════════════════════════════════════
// Submit clears input
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, InputClearedAfterSubmit) {
    AIPanel panel;
    ActionBus bus;
    panel.initialize(&bus);
    panel.open();
    panel.handleTextInput('H');
    panel.handleTextInput('i');
    EXPECT_EQ(panel.inputText(), "Hi");
    // Enter = 0x28
    panel.handleKey(0x28, true);
    EXPECT_TRUE(panel.inputText().empty());
    // Message was added to history
    EXPECT_EQ(panel.messageCount(), 1u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Scroll offset
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, ScrollOffsetStartsAtZero) {
    AIPanel panel;
    // Panel doesn't directly expose scroll_offset_, but scroll keys work
    panel.open();
    // Just verify up/down keys are consumed without crash
    EXPECT_TRUE(panel.handleKey(0x52, true)); // Up
    EXPECT_TRUE(panel.handleKey(0x51, true)); // Down
}

// ═══════════════════════════════════════════════════════════════════════════
// REQ-SEC-008: AI Response Sanitization
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIPanelTest, SanitizeResponse_StripsScriptTags) {
    std::string input = "Hello <script>alert('xss')</script> world";
    auto result = AIPanel::sanitizeResponse(input);
    EXPECT_EQ(result, "Hello  world");
    EXPECT_EQ(result.find("script"), std::string::npos);
}

TEST(AIPanelTest, SanitizeResponse_StripsScriptTagsCaseInsensitive) {
    std::string input = "text <SCRIPT>evil()</SCRIPT> more";
    auto result = AIPanel::sanitizeResponse(input);
    EXPECT_EQ(result.find("SCRIPT"), std::string::npos);
    EXPECT_EQ(result.find("evil"), std::string::npos);
}

TEST(AIPanelTest, SanitizeResponse_StripsImgTags) {
    std::string input = "see <img src=\"http://evil.com/track.png\"> this";
    auto result = AIPanel::sanitizeResponse(input);
    EXPECT_EQ(result.find("img"), std::string::npos);
    EXPECT_NE(result.find("see"), std::string::npos);
}

TEST(AIPanelTest, SanitizeResponse_StripsJavascriptURI) {
    std::string input = "click javascript:alert(1) here";
    auto result = AIPanel::sanitizeResponse(input);
    EXPECT_EQ(result.find("javascript:"), std::string::npos);
}

TEST(AIPanelTest, SanitizeResponse_StripsFileURI) {
    std::string input = "open file:///etc/passwd please";
    auto result = AIPanel::sanitizeResponse(input);
    EXPECT_EQ(result.find("file://"), std::string::npos);
}

TEST(AIPanelTest, SanitizeResponse_PreservesNormalText) {
    std::string input = "This is a normal AI response with no issues.";
    auto result = AIPanel::sanitizeResponse(input);
    EXPECT_EQ(result, input);
}

TEST(AIPanelTest, AddResponse_SanitizesBeforeStoring) {
    AIPanel panel;
    panel.addResponse("Hello <script>evil()</script> world");
    ASSERT_EQ(panel.messageCount(), 1u);
    EXPECT_EQ(panel.history()[0].text.find("script"), std::string::npos);
    EXPECT_NE(panel.history()[0].text.find("Hello"), std::string::npos);
}

} // namespace
} // namespace legends
