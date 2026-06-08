// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for AI screen context capture.

#include <gtest/gtest.h>
#include "app/ai_screen_context.h"
#include <legends/runtime_host.h>

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

class FakeRuntimeHost : public RuntimeHost {
public:
    std::vector<legends_text_cell_t> mock_cells;
    legends_text_info_t mock_info{};
    legends_error_t mock_error = LEGENDS_OK;

    legends_error_t step_ms(uint32_t, legends_step_result_t*) override { return LEGENDS_OK; }
    legends_error_t step_cycles(uint64_t, legends_step_result_t*) override { return LEGENDS_OK; }

    legends_error_t capture_text(
        legends_text_cell_t* cells,
        size_t cells_count,
        size_t* cells_count_out,
        legends_text_info_t* info_out) override {
        if (mock_error != LEGENDS_OK) {
            return mock_error;
        }
        if (info_out) {
            *info_out = mock_info;
        }
        if (cells_count_out) {
            *cells_count_out = mock_cells.size();
        }
        if (cells && cells_count >= mock_cells.size()) {
            std::copy(mock_cells.begin(), mock_cells.end(), cells);
        }
        return LEGENDS_OK;
    }

    legends_error_t capture_rgb(uint8_t*, size_t, size_t*, uint16_t*, uint16_t*) override { return LEGENDS_OK; }
    legends_error_t inject_key(uint8_t, bool) override { return LEGENDS_OK; }
    legends_error_t inject_mouse(int16_t, int16_t, uint8_t) override { return LEGENDS_OK; }
    legends_error_t save_state(void*, size_t, size_t*) override { return LEGENDS_OK; }
    legends_error_t load_state(const void*, size_t) override { return LEGENDS_OK; }
    legends_error_t mount_drive(char, std::string_view, uint32_t) override { return LEGENDS_OK; }
    legends_error_t unmount_drive(char) override { return LEGENDS_OK; }
    legends_error_t get_total_cycles(uint64_t*) override { return LEGENDS_OK; }
    legends_error_t is_frame_dirty(int*) override { return LEGENDS_OK; }
    legends_error_t inject_key_ext(uint8_t, bool) override { return LEGENDS_OK; }
    legends_error_t capture_audio(int16_t*, size_t, size_t*) override { return LEGENDS_OK; }
    legends_error_t capture_midi_audio(int16_t*, size_t, size_t*) override { return LEGENDS_OK; }

    legends_error_t reset() override { return LEGENDS_OK; }
    legends_error_t text_input(std::string_view) override { return LEGENDS_OK; }
    legends_error_t get_cursor(uint8_t*, uint8_t*, int*) override { return LEGENDS_OK; }
    legends_error_t joystick_event(uint8_t, uint8_t, uint8_t, uint8_t) override { return LEGENDS_OK; }
    legends_error_t set_log_callback(legends_log_callback_t, void*) override { return LEGENDS_OK; }
    legends_error_t set_midi_device(std::string_view) override { return LEGENDS_OK; }
    legends_error_t set_midi_soundfont(std::string_view) override { return LEGENDS_OK; }
    legends_error_t set_midi_romdir(std::string_view) override { return LEGENDS_OK; }
    legends_error_t set_printer_output(std::string_view) override { return LEGENDS_OK; }
    legends_error_t set_ttf_font(std::string_view, uint32_t) override { return LEGENDS_OK; }
    legends_error_t ipx_enable(bool) override { return LEGENDS_OK; }
    legends_error_t ipx_connect(std::string_view, uint16_t) override { return LEGENDS_OK; }
    legends_error_t ipx_disconnect() override { return LEGENDS_OK; }
    legends_error_t glide_enable(bool) override { return LEGENDS_OK; }
    legends_error_t glide_set_resolution(uint16_t, uint16_t) override { return LEGENDS_OK; }
    legends_error_t set_machine_pc98(bool) override { return LEGENDS_OK; }
};

namespace {

TEST(AIScreenContextTest, CaptureScreenContextWithFakeRuntime) {
    FakeRuntimeHost runtime;
    runtime.mock_info.columns = 5;
    runtime.mock_info.rows = 2;
    for (int i = 0; i < 10; ++i) {
        legends_text_cell_t cell{};
        cell.character = static_cast<uint8_t>('A' + i);
        cell.attribute = 0x07;
        runtime.mock_cells.push_back(cell);
    }

    std::string result = captureScreenContext(runtime);
    EXPECT_EQ(result, "ABCDE\nFGHIJ");
}

TEST(AIScreenContextTest, CaptureScreenContextWithFakeRuntimeErrorReturnsEmpty) {
    FakeRuntimeHost runtime;
    runtime.mock_error = LEGENDS_ERR_NOT_SUPPORTED;
    std::string result = captureScreenContext(runtime);
    EXPECT_TRUE(result.empty());
}

} // namespace
} // namespace legends
