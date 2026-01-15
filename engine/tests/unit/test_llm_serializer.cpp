/**
 * @file test_llm_serializer.cpp
 * @brief Unit tests for LLM text serialization.
 */

#include <gtest/gtest.h>
#include <aibox/llm_serializer.h>
#include <cstring>

using namespace aibox::llm;

// ─────────────────────────────────────────────────────────────────────────────
// CP437 to Unicode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(Cp437ToUnicodeTest, AsciiPrintable) {
    // Standard ASCII printable characters should map to themselves
    for (uint8_t c = 0x20; c < 0x7F; ++c) {
        EXPECT_EQ(cp437_to_unicode(c), static_cast<char32_t>(c))
            << "Failed for character: " << static_cast<int>(c);
    }
}

TEST(Cp437ToUnicodeTest, Space) {
    EXPECT_EQ(cp437_to_unicode(0x20), U' ');
}

TEST(Cp437ToUnicodeTest, Letters) {
    EXPECT_EQ(cp437_to_unicode('A'), U'A');
    EXPECT_EQ(cp437_to_unicode('Z'), U'Z');
    EXPECT_EQ(cp437_to_unicode('a'), U'a');
    EXPECT_EQ(cp437_to_unicode('z'), U'z');
}

TEST(Cp437ToUnicodeTest, Digits) {
    EXPECT_EQ(cp437_to_unicode('0'), U'0');
    EXPECT_EQ(cp437_to_unicode('9'), U'9');
}

TEST(Cp437ToUnicodeTest, BoxDrawingLight) {
    // Light box drawing characters
    EXPECT_EQ(cp437_to_unicode(0xC4), U'\u2500');  // ─ horizontal
    EXPECT_EQ(cp437_to_unicode(0xB3), U'\u2502');  // │ vertical
    EXPECT_EQ(cp437_to_unicode(0xDA), U'\u250C');  // ┌ top-left
    EXPECT_EQ(cp437_to_unicode(0xBF), U'\u2510');  // ┐ top-right
    EXPECT_EQ(cp437_to_unicode(0xC0), U'\u2514');  // └ bottom-left
    EXPECT_EQ(cp437_to_unicode(0xD9), U'\u2518');  // ┘ bottom-right
}

TEST(Cp437ToUnicodeTest, BoxDrawingDouble) {
    // Double box drawing characters
    EXPECT_EQ(cp437_to_unicode(0xCD), U'\u2550');  // ═ horizontal
    EXPECT_EQ(cp437_to_unicode(0xBA), U'\u2551');  // ║ vertical
    EXPECT_EQ(cp437_to_unicode(0xC9), U'\u2554');  // ╔ top-left
    EXPECT_EQ(cp437_to_unicode(0xBB), U'\u2557');  // ╗ top-right
    EXPECT_EQ(cp437_to_unicode(0xC8), U'\u255A');  // ╚ bottom-left
    EXPECT_EQ(cp437_to_unicode(0xBC), U'\u255D');  // ╝ bottom-right
}

TEST(Cp437ToUnicodeTest, ControlCharacters) {
    // Control characters map to special symbols
    EXPECT_EQ(cp437_to_unicode(0x01), U'\u263A');  // ☺
    EXPECT_EQ(cp437_to_unicode(0x02), U'\u263B');  // ☻
    EXPECT_EQ(cp437_to_unicode(0x03), U'\u2665');  // ♥
    EXPECT_EQ(cp437_to_unicode(0x04), U'\u2666');  // ♦
    EXPECT_EQ(cp437_to_unicode(0x05), U'\u2663');  // ♣
    EXPECT_EQ(cp437_to_unicode(0x06), U'\u2660');  // ♠
}

TEST(Cp437ToUnicodeTest, ExtendedLatin) {
    // Extended Latin characters
    EXPECT_EQ(cp437_to_unicode(0x80), U'\u00C7');  // Ç
    EXPECT_EQ(cp437_to_unicode(0x81), U'\u00FC');  // ü
    EXPECT_EQ(cp437_to_unicode(0x82), U'\u00E9');  // é
    EXPECT_EQ(cp437_to_unicode(0xA4), U'\u00F1');  // ñ
    EXPECT_EQ(cp437_to_unicode(0xA5), U'\u00D1');  // Ñ
}

TEST(Cp437ToUnicodeTest, GreekLetters) {
    EXPECT_EQ(cp437_to_unicode(0xE0), U'\u03B1');  // α
    EXPECT_EQ(cp437_to_unicode(0xE1), U'\u00DF');  // ß (German sharp s)
    EXPECT_EQ(cp437_to_unicode(0xE2), U'\u0393');  // Γ
    EXPECT_EQ(cp437_to_unicode(0xE3), U'\u03C0');  // π
}

TEST(Cp437ToUnicodeTest, MathSymbols) {
    EXPECT_EQ(cp437_to_unicode(0xEC), U'\u221E');  // ∞
    EXPECT_EQ(cp437_to_unicode(0xF1), U'\u00B1');  // ±
    EXPECT_EQ(cp437_to_unicode(0xFB), U'\u221A');  // √
}

TEST(Cp437ToUnicodeTest, BlockElements) {
    EXPECT_EQ(cp437_to_unicode(0xB0), U'\u2591');  // ░ light shade
    EXPECT_EQ(cp437_to_unicode(0xB1), U'\u2592');  // ▒ medium shade
    EXPECT_EQ(cp437_to_unicode(0xB2), U'\u2593');  // ▓ dark shade
    EXPECT_EQ(cp437_to_unicode(0xDB), U'\u2588');  // █ full block
}

// ─────────────────────────────────────────────────────────────────────────────
// UTF-8 Encoding Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(EncodeUtf8Test, SingleByte) {
    char buffer[4];
    EXPECT_EQ(encode_utf8(U'A', buffer), 1u);
    EXPECT_EQ(buffer[0], 'A');
}

TEST(EncodeUtf8Test, TwoBytes) {
    char buffer[4];
    EXPECT_EQ(encode_utf8(U'\u00E9', buffer), 2u);  // é
    EXPECT_EQ(static_cast<uint8_t>(buffer[0]), 0xC3);
    EXPECT_EQ(static_cast<uint8_t>(buffer[1]), 0xA9);
}

TEST(EncodeUtf8Test, ThreeBytes) {
    char buffer[4];
    EXPECT_EQ(encode_utf8(U'\u2550', buffer), 3u);  // ═
    EXPECT_EQ(static_cast<uint8_t>(buffer[0]), 0xE2);
    EXPECT_EQ(static_cast<uint8_t>(buffer[1]), 0x95);
    EXPECT_EQ(static_cast<uint8_t>(buffer[2]), 0x90);
}

TEST(EncodeUtf8Test, FourBytes) {
    char buffer[4];
    EXPECT_EQ(encode_utf8(U'\U0001F600', buffer), 4u);  // 😀
    EXPECT_EQ(static_cast<uint8_t>(buffer[0]), 0xF0);
    EXPECT_EQ(static_cast<uint8_t>(buffer[1]), 0x9F);
    EXPECT_EQ(static_cast<uint8_t>(buffer[2]), 0x98);
    EXPECT_EQ(static_cast<uint8_t>(buffer[3]), 0x80);
}

// ─────────────────────────────────────────────────────────────────────────────
// CP437 Char to UTF-8 Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(Cp437CharToUtf8Test, AsciiChar) {
    EXPECT_EQ(cp437_char_to_utf8('A'), "A");
    EXPECT_EQ(cp437_char_to_utf8(' '), " ");
    EXPECT_EQ(cp437_char_to_utf8('0'), "0");
}

TEST(Cp437CharToUtf8Test, BoxCharacter) {
    std::string result = cp437_char_to_utf8(0xC9);  // ╔
    EXPECT_EQ(result, "\xE2\x95\x94");
}

TEST(Cp437CharToUtf8Test, ExtendedCharacter) {
    std::string result = cp437_char_to_utf8(0x82);  // é
    EXPECT_EQ(result, "\xC3\xA9");
}

// ─────────────────────────────────────────────────────────────────────────────
// Box Drawing Constants Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(BoxDrawingTest, DoubleLineConstants) {
    EXPECT_STREQ(box::TOP_LEFT, "\u2554");
    EXPECT_STREQ(box::TOP_RIGHT, "\u2557");
    EXPECT_STREQ(box::BOTTOM_LEFT, "\u255A");
    EXPECT_STREQ(box::BOTTOM_RIGHT, "\u255D");
    EXPECT_STREQ(box::HORIZONTAL, "\u2550");
    EXPECT_STREQ(box::VERTICAL, "\u2551");
}

TEST(BoxDrawingTest, SingleLineConstants) {
    EXPECT_STREQ(box::LIGHT_HORIZONTAL, "\u2500");
    EXPECT_STREQ(box::LIGHT_VERTICAL, "\u2502");
    EXPECT_STREQ(box::LIGHT_TOP_LEFT, "\u250C");
    EXPECT_STREQ(box::LIGHT_TOP_RIGHT, "\u2510");
    EXPECT_STREQ(box::LIGHT_BOT_LEFT, "\u2514");
    EXPECT_STREQ(box::LIGHT_BOT_RIGHT, "\u2518");
}

// ─────────────────────────────────────────────────────────────────────────────
// SerializerOptions Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(SerializerOptionsTest, DefaultValues) {
    SerializerOptions opts{};

    EXPECT_TRUE(opts.include_box_border);
    EXPECT_TRUE(opts.trim_trailing_spaces);
    EXPECT_TRUE(opts.mark_cursor);
    EXPECT_FALSE(opts.use_rle);
    EXPECT_EQ(opts.rle_threshold, 4u);
}

TEST(SerializerOptionsTest, CustomValues) {
    SerializerOptions opts;
    opts.include_box_border = false;
    opts.trim_trailing_spaces = false;
    opts.mark_cursor = false;
    opts.use_rle = true;
    opts.rle_threshold = 8;

    EXPECT_FALSE(opts.include_box_border);
    EXPECT_FALSE(opts.trim_trailing_spaces);
    EXPECT_FALSE(opts.mark_cursor);
    EXPECT_TRUE(opts.use_rle);
    EXPECT_EQ(opts.rle_threshold, 8u);
}

// ─────────────────────────────────────────────────────────────────────────────
// String Utility Tests (trim_trailing_spaces)
// ─────────────────────────────────────────────────────────────────────────────

TEST(TrimTrailingSpacesTest, NoSpaces) {
    EXPECT_EQ(trim_trailing_spaces("hello"), "hello");
}

TEST(TrimTrailingSpacesTest, TrailingSpaces) {
    EXPECT_EQ(trim_trailing_spaces("hello   "), "hello");
}

TEST(TrimTrailingSpacesTest, OnlySpaces) {
    EXPECT_EQ(trim_trailing_spaces("     "), "");
}

TEST(TrimTrailingSpacesTest, Empty) {
    EXPECT_EQ(trim_trailing_spaces(""), "");
}

TEST(TrimTrailingSpacesTest, LeadingSpaces) {
    EXPECT_EQ(trim_trailing_spaces("  hello"), "  hello");
}

TEST(TrimTrailingSpacesTest, MixedSpaces) {
    EXPECT_EQ(trim_trailing_spaces("  hello world  "), "  hello world");
}

// ─────────────────────────────────────────────────────────────────────────────
// Trim Lines Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TrimLinesTest, SingleLine) {
    // trim_lines always appends newlines to each processed line
    EXPECT_EQ(trim_lines("hello   "), "hello\n");
}

TEST(TrimLinesTest, MultipleLines) {
    std::string input = "hello   \nworld  \n";
    std::string expected = "hello\nworld\n";
    EXPECT_EQ(trim_lines(input), expected);
}

TEST(TrimLinesTest, EmptyLines) {
    std::string input = "hello\n   \nworld\n";
    std::string expected = "hello\n\nworld\n";
    EXPECT_EQ(trim_lines(input), expected);
}

// ─────────────────────────────────────────────────────────────────────────────
// RLE Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ApplyRleTest, NoRuns) {
    EXPECT_EQ(apply_rle("abc"), "abc");
}

TEST(ApplyRleTest, ShortRun) {
    // Run of 3 should not be encoded (below threshold of 4)
    EXPECT_EQ(apply_rle("aaa"), "aaa");
}

TEST(ApplyRleTest, MinimumRun) {
    // Run of 4 should be encoded
    std::string result = apply_rle("aaaa");
    EXPECT_NE(result, "aaaa");
    // Should contain a tilde for RLE notation
    EXPECT_NE(result.find('~'), std::string::npos);
}

TEST(ApplyRleTest, LongRun) {
    std::string result = apply_rle("          ");  // 10 spaces
    // Should be significantly shorter due to RLE
    EXPECT_LT(result.size(), 10u);
}

TEST(ApplyRleTest, CustomThreshold) {
    // With threshold 6, run of 5 should not be encoded
    EXPECT_EQ(apply_rle("aaaaa", 6), "aaaaa");

    // With threshold 4, run of 5 should be encoded
    std::string result = apply_rle("aaaaa", 4);
    EXPECT_NE(result, "aaaaa");
}

TEST(ApplyRleTest, MixedContent) {
    std::string input = "hello          world";  // Many spaces
    std::string result = apply_rle(input);

    // Original text should be preserved
    EXPECT_NE(result.find("hello"), std::string::npos);
    EXPECT_NE(result.find("world"), std::string::npos);

    // Should be shorter than input
    EXPECT_LT(result.size(), input.size());
}

// ─────────────────────────────────────────────────────────────────────────────
// Decode RLE Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DecodeRleTest, NoRle) {
    EXPECT_EQ(decode_rle("hello"), "hello");
}

TEST(DecodeRleTest, RoundTrip) {
    std::string original = "hello          world";  // Many spaces
    std::string encoded = apply_rle(original);
    std::string decoded = decode_rle(encoded);

    EXPECT_EQ(decoded, original);
}

TEST(DecodeRleTest, MultipleRuns) {
    std::string original = "aaaaabbbbccccc";
    std::string encoded = apply_rle(original);
    std::string decoded = decode_rle(encoded);

    EXPECT_EQ(decoded, original);
}

// ─────────────────────────────────────────────────────────────────────────────
// JSON Escape Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(JsonEscapeTest, NoEscape) {
    EXPECT_EQ(json_escape("hello"), "hello");
}

TEST(JsonEscapeTest, Quotes) {
    EXPECT_EQ(json_escape("he said \"hi\""), "he said \\\"hi\\\"");
}

TEST(JsonEscapeTest, Backslash) {
    EXPECT_EQ(json_escape("C:\\path"), "C:\\\\path");
}

TEST(JsonEscapeTest, Newline) {
    EXPECT_EQ(json_escape("line1\nline2"), "line1\\nline2");
}

TEST(JsonEscapeTest, Tab) {
    EXPECT_EQ(json_escape("a\tb"), "a\\tb");
}

TEST(JsonEscapeTest, CarriageReturn) {
    EXPECT_EQ(json_escape("a\rb"), "a\\rb");
}

TEST(JsonEscapeTest, ControlCharacters) {
    std::string input(1, '\x01');  // Control character
    std::string result = json_escape(input);
    // Should be escaped as \u0001
    EXPECT_NE(result.find("\\u"), std::string::npos);
}

// ─────────────────────────────────────────────────────────────────────────────
// JSON Unescape Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(JsonUnescapeTest, NoEscape) {
    EXPECT_EQ(json_unescape("hello"), "hello");
}

TEST(JsonUnescapeTest, EscapedQuote) {
    EXPECT_EQ(json_unescape("\\\""), "\"");
}

TEST(JsonUnescapeTest, EscapedBackslash) {
    EXPECT_EQ(json_unescape("\\\\"), "\\");
}

TEST(JsonUnescapeTest, EscapedNewline) {
    EXPECT_EQ(json_unescape("\\n"), "\n");
}

TEST(JsonUnescapeTest, RoundTrip) {
    std::string original = "he said \"hi\"\npath: C:\\test";
    std::string escaped = json_escape(original);
    std::string unescaped = json_unescape(escaped);

    EXPECT_EQ(unescaped, original);
}

// ─────────────────────────────────────────────────────────────────────────────
// Token Estimation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(EstimateTokensTest, Empty) {
    EXPECT_EQ(estimate_tokens(""), 0u);
}

TEST(EstimateTokensTest, ShortText) {
    // "hello" is 5 characters, roughly 1-2 tokens
    size_t tokens = estimate_tokens("hello");
    EXPECT_GE(tokens, 1u);
    EXPECT_LE(tokens, 5u);
}

TEST(EstimateTokensTest, LongerText) {
    std::string text = "The quick brown fox jumps over the lazy dog.";
    size_t tokens = estimate_tokens(text);

    // ~44 characters, roughly 11 tokens at 4 chars/token
    EXPECT_GE(tokens, 5u);
    EXPECT_LE(tokens, 20u);
}

TEST(EstimateTokensTest, BoxCharacters) {
    // Box drawing characters typically take more tokens
    std::string text = "\u2554\u2550\u2550\u2550\u2557";  // ╔═══╗
    size_t tokens = estimate_tokens(text);

    // Should estimate higher for special characters
    EXPECT_GE(tokens, 5u);
}

TEST(EstimateTokensTest, Proportional) {
    std::string short_text = "hello";
    std::string long_text = "hello world this is a much longer piece of text";

    size_t short_tokens = estimate_tokens(short_text);
    size_t long_tokens = estimate_tokens(long_text);

    EXPECT_LT(short_tokens, long_tokens);
}

// ─────────────────────────────────────────────────────────────────────────────
// CP437 to UTF-8 Array Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(Cp437ToUtf8ArrayTest, SimpleAscii) {
    uint8_t data[] = {'H', 'e', 'l', 'l', 'o'};
    std::string result = cp437_to_utf8(data, 5);
    EXPECT_EQ(result, "Hello");
}

TEST(Cp437ToUtf8ArrayTest, WithBoxChars) {
    uint8_t data[] = {0xC9, 0xCD, 0xCD, 0xBB};  // ╔══╗
    std::string result = cp437_to_utf8(data, 4);

    // Each box char is 3 UTF-8 bytes
    EXPECT_EQ(result.size(), 12u);
}

TEST(Cp437ToUtf8ArrayTest, Empty) {
    std::string result = cp437_to_utf8(nullptr, 0);
    EXPECT_TRUE(result.empty());
}

TEST(Cp437ToUtf8ArrayTest, MixedContent) {
    // "A" + box char + "B"
    uint8_t data[] = {'A', 0xB3, 'B'};  // A│B
    std::string result = cp437_to_utf8(data, 3);

    EXPECT_EQ(result[0], 'A');
    EXPECT_EQ(result.back(), 'B');
    EXPECT_GT(result.size(), 3u);  // Box char expands
}
