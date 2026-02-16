/**
 * @file test_text_input_utf8.cpp
 * @brief Unit tests for UTF-8 text input edge cases (BUG-1 fix).
 *
 * Validates that truncated multi-byte UTF-8 sequences do not cause
 * buffer overreads in legends_text_input().
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>

class TextInputUtf8Test : public ::testing::Test {
protected:
    legends_handle h_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
        legends_create(nullptr, &h_);
    }

    void TearDown() override {
        if (h_) legends_destroy(h_);
        pal::Platform::shutdown();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Truncated UTF-8 sequences — must not overread past null terminator
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(TextInputUtf8Test, TruncatedUtf8_2byte) {
    // 0xC3 starts a 2-byte sequence but the continuation byte is missing
    const char input[] = "\xC3";
    EXPECT_EQ(legends_text_input(h_, input), LEGENDS_OK);
}

TEST_F(TextInputUtf8Test, TruncatedUtf8_3byte) {
    // 0xE0 starts a 3-byte sequence, only 1 continuation byte present
    const char input[] = "\xE0\x80";
    EXPECT_EQ(legends_text_input(h_, input), LEGENDS_OK);
}

TEST_F(TextInputUtf8Test, TruncatedUtf8_4byte) {
    // 0xF0 starts a 4-byte sequence, only 2 continuation bytes present
    const char input[] = "\xF0\x80\x80";
    EXPECT_EQ(legends_text_input(h_, input), LEGENDS_OK);
}

// ─────────────────────────────────────────────────────────────────────────────
// Valid inputs
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(TextInputUtf8Test, ValidUtf8Passthrough) {
    // e-acute (U+00E9) = 0xC3 0xA9
    const char input[] = "Hello \xC3\xA9";
    EXPECT_EQ(legends_text_input(h_, input), LEGENDS_OK);
}

TEST_F(TextInputUtf8Test, EmptyString) {
    EXPECT_EQ(legends_text_input(h_, ""), LEGENDS_OK);
}

TEST_F(TextInputUtf8Test, MixedAsciiAndTruncated) {
    // Normal ASCII followed by a truncated 3-byte sequence
    const char input[] = "abc\xE0\x80";
    EXPECT_EQ(legends_text_input(h_, input), LEGENDS_OK);
}
