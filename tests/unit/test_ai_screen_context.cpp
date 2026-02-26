// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for AI screen context capture.

#include <gtest/gtest.h>
#include "app/ai_screen_context.h"

#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// cp437ToUtf8 — ASCII passthrough
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIScreenContextTest, Cp437ToUtf8AsciiSpace) {
    EXPECT_EQ(cp437ToUtf8(0x20), " ");
}

TEST(AIScreenContextTest, Cp437ToUtf8AsciiUpperA) {
    EXPECT_EQ(cp437ToUtf8('A'), "A");
}

TEST(AIScreenContextTest, Cp437ToUtf8AsciiLowerZ) {
    EXPECT_EQ(cp437ToUtf8('z'), "z");
}

TEST(AIScreenContextTest, Cp437ToUtf8AsciiDigitZero) {
    EXPECT_EQ(cp437ToUtf8('0'), "0");
}

TEST(AIScreenContextTest, Cp437ToUtf8AsciiTilde) {
    EXPECT_EQ(cp437ToUtf8('~'), "~");
}

// ═══════════════════════════════════════════════════════════════════════════
// cp437ToUtf8 — special characters
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIScreenContextTest, Cp437ToUtf8NullByteIsSpace) {
    std::string result = cp437ToUtf8(0x00);
    // Null byte maps to space
    EXPECT_EQ(result, " ");
}

TEST(AIScreenContextTest, Cp437ToUtf8SmileyFace) {
    std::string result = cp437ToUtf8(0x01);
    // U+263A ☺ = E2 98 BA
    EXPECT_EQ(result, "\xE2\x98\xBA");
}

TEST(AIScreenContextTest, Cp437ToUtf8Heart) {
    std::string result = cp437ToUtf8(0x03);
    // U+2665 ♥ = E2 99 A5
    EXPECT_EQ(result, "\xE2\x99\xA5");
}

// ═══════════════════════════════════════════════════════════════════════════
// cp437ToUtf8 — box drawing characters
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIScreenContextTest, Cp437ToUtf8HorizontalBar) {
    std::string result = cp437ToUtf8(0xC4);
    // U+2500 ─ = E2 94 80
    EXPECT_EQ(result, "\xE2\x94\x80");
}

TEST(AIScreenContextTest, Cp437ToUtf8VerticalBar) {
    std::string result = cp437ToUtf8(0xB3);
    // U+2502 │ = E2 94 82
    EXPECT_EQ(result, "\xE2\x94\x82");
}

TEST(AIScreenContextTest, Cp437ToUtf8TopLeftCorner) {
    std::string result = cp437ToUtf8(0xDA);
    // U+250C ┌ = E2 94 8C
    EXPECT_EQ(result, "\xE2\x94\x8C");
}

// ═══════════════════════════════════════════════════════════════════════════
// cp437ToUtf8 — extended characters (0x80-0xFF)
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIScreenContextTest, Cp437ToUtf8UpperCCedilla) {
    std::string result = cp437ToUtf8(0x80);
    // U+00C7 Ç = C3 87
    EXPECT_EQ(result, "\xC3\x87");
}

TEST(AIScreenContextTest, Cp437ToUtf8LowerUUmlaut) {
    std::string result = cp437ToUtf8(0x81);
    // U+00FC ü = C3 BC
    EXPECT_EQ(result, "\xC3\xBC");
}

// ═══════════════════════════════════════════════════════════════════════════
// formatScreenContext
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIScreenContextTest, FormatScreenContextIncludesDimensions) {
    std::string result = formatScreenContext("Hello", 0, 0, 80, 25);
    EXPECT_NE(result.find("80x25"), std::string::npos);
}

TEST(AIScreenContextTest, FormatScreenContextIncludesCursorPosition) {
    std::string result = formatScreenContext("Hello", 10, 5, 80, 25);
    EXPECT_NE(result.find("(10,5)"), std::string::npos);
}

TEST(AIScreenContextTest, FormatScreenContextWrapsInCodeBlock) {
    std::string result = formatScreenContext("Hello", 0, 0, 80, 25);
    EXPECT_NE(result.find("```"), std::string::npos);
    // Should contain opening and closing code fences
    auto first = result.find("```");
    auto second = result.find("```", first + 3);
    EXPECT_NE(second, std::string::npos);
}

TEST(AIScreenContextTest, FormatScreenContextEmptyText) {
    std::string result = formatScreenContext("", 0, 0, 80, 25);
    EXPECT_NE(result.find("Screen"), std::string::npos);
    EXPECT_NE(result.find("Cursor"), std::string::npos);
}

// ═══════════════════════════════════════════════════════════════════════════
// captureScreenContext with null handle
// ═══════════════════════════════════════════════════════════════════════════

TEST(AIScreenContextTest, CaptureScreenContextNullHandleReturnsEmpty) {
    std::string result = captureScreenContext(nullptr);
    EXPECT_TRUE(result.empty());
}

} // namespace
} // namespace legends
