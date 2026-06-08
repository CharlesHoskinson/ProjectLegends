// SPDX-License-Identifier: GPL-2.0-or-later

// Copyright (C) 2024-2025 Charles Hoskinson and Contributors

//

// AI screen context capture — CP437 to UTF-8 conversion and screen capture.



#include "app/ai_screen_context.h"

#include <legends/runtime_host.h>



#include <algorithm>

#include <cstring>

#include <vector>



namespace legends {



// ─────────────────────────────────────────────────────────────────────────────

// CP437 to UTF-8 lookup table

// ─────────────────────────────────────────────────────────────────────────────



// Static lookup table: maps all 256 CP437 byte values to pre-encoded

// UTF-8 string literals. ASCII printable range (0x20-0x7E) maps 1:1.

// Control codes and high bytes map to their standard CP437 graphical

// Unicode equivalents (box-drawing, Greek letters, math symbols, etc.).

static const char* const kCp437ToUtf8[256] = {

    // 0x00-0x0F: Control / special characters

    " ",           // 0x00 NUL → space

    "\xE2\x98\xBA", // 0x01 ☺

    "\xE2\x98\xBB", // 0x02 ☻

    "\xE2\x99\xA5", // 0x03 ♥

    "\xE2\x99\xA6", // 0x04 ♦

    "\xE2\x99\xA3", // 0x05 ♣

    "\xE2\x99\xA0", // 0x06 ♠

    "\xE2\x80\xA2", // 0x07 • (bullet)

    "\xE2\x97\x98", // 0x08 ◘

    "\xE2\x97\x8B", // 0x09 ○

    "\xE2\x97\x99", // 0x0A ◙

    "\xE2\x99\x82", // 0x0B ♂

    "\xE2\x99\x80", // 0x0C ♀

    "\xE2\x99\xAA", // 0x0D ♪

    "\xE2\x99\xAB", // 0x0E ♫

    "\xE2\x98\xBC", // 0x0F ☼



    // 0x10-0x1F: More special characters

    "\xE2\x96\xBA", // 0x10 ►

    "\xE2\x97\x84", // 0x11 ◄

    "\xE2\x86\x95", // 0x12 ↕

    "\xE2\x80\xBC", // 0x13 ‼

    "\xC2\xB6",     // 0x14 ¶

    "\xC2\xA7",     // 0x15 §

    "\xE2\x96\xAC", // 0x16 ▬

    "\xE2\x86\xA8", // 0x17 ↨

    "\xE2\x86\x91", // 0x18 ↑

    "\xE2\x86\x93", // 0x19 ↓

    "\xE2\x86\x92", // 0x1A →

    "\xE2\x86\x90", // 0x1B ←

    "\xE2\x88\x9F", // 0x1C ∟

    "\xE2\x86\x94", // 0x1D ↔

    "\xE2\x96\xB2", // 0x1E ▲

    "\xE2\x96\xBC", // 0x1F ▼



    // 0x20-0x7E: ASCII printable (pass through)

    " ", "!", "\"", "#", "$", "%", "&", "'",

    "(", ")", "*", "+", ",", "-", ".", "/",

    "0", "1", "2", "3", "4", "5", "6", "7",

    "8", "9", ":", ";", "<", "=", ">", "?",

    "@", "A", "B", "C", "D", "E", "F", "G",

    "H", "I", "J", "K", "L", "M", "N", "O",

    "P", "Q", "R", "S", "T", "U", "V", "W",

    "X", "Y", "Z", "[", "\\", "]", "^", "_",

    "`", "a", "b", "c", "d", "e", "f", "g",

    "h", "i", "j", "k", "l", "m", "n", "o",

    "p", "q", "r", "s", "t", "u", "v", "w",

    "x", "y", "z", "{", "|", "}", "~",



    // 0x7F: DEL → ⌂

    "\xE2\x8C\x82",



    // 0x80-0x8F: Accented characters

    "\xC3\x87",     // 0x80 Ç

    "\xC3\xBC",     // 0x81 ü

    "\xC3\xA9",     // 0x82 é

    "\xC3\xA2",     // 0x83 â

    "\xC3\xA4",     // 0x84 ä

    "\xC3\xA0",     // 0x85 à

    "\xC3\xA5",     // 0x86 å

    "\xC3\xA7",     // 0x87 ç

    "\xC3\xAA",     // 0x88 ê

    "\xC3\xAB",     // 0x89 ë

    "\xC3\xA8",     // 0x8A è

    "\xC3\xAF",     // 0x8B ï

    "\xC3\xAE",     // 0x8C î

    "\xC3\xAC",     // 0x8D ì

    "\xC3\x84",     // 0x8E Ä

    "\xC3\x85",     // 0x8F Å



    // 0x90-0x9F

    "\xC3\x89",     // 0x90 É

    "\xC3\xA6",     // 0x91 æ

    "\xC3\x86",     // 0x92 Æ

    "\xC3\xB4",     // 0x93 ô

    "\xC3\xB6",     // 0x94 ö

    "\xC3\xB2",     // 0x95 ò

    "\xC3\xBB",     // 0x96 û

    "\xC3\xB9",     // 0x97 ù

    "\xC3\xBF",     // 0x98 ÿ

    "\xC3\x96",     // 0x99 Ö

    "\xC3\x9C",     // 0x9A Ü

    "\xC2\xA2",     // 0x9B ¢

    "\xC2\xA3",     // 0x9C £

    "\xC2\xA5",     // 0x9D ¥

    "\xE2\x82\xA7", // 0x9E ₧

    "\xC6\x92",     // 0x9F ƒ



    // 0xA0-0xAF

    "\xC3\xA1",     // 0xA0 á

    "\xC3\xAD",     // 0xA1 í

    "\xC3\xB3",     // 0xA2 ó

    "\xC3\xBA",     // 0xA3 ú

    "\xC3\xB1",     // 0xA4 ñ

    "\xC3\x91",     // 0xA5 Ñ

    "\xC2\xAA",     // 0xA6 ª

    "\xC2\xBA",     // 0xA7 º

    "\xC2\xBF",     // 0xA8 ¿

    "\xE2\x8C\x90", // 0xA9 ⌐

    "\xC2\xAC",     // 0xAA ¬

    "\xC2\xBD",     // 0xAB ½

    "\xC2\xBC",     // 0xAC ¼

    "\xC2\xA1",     // 0xAD ¡

    "\xC2\xAB",     // 0xAE «

    "\xC2\xBB",     // 0xAF »



    // 0xB0-0xBF: Box drawing light

    "\xE2\x96\x91", // 0xB0 ░

    "\xE2\x96\x92", // 0xB1 ▒

    "\xE2\x96\x93", // 0xB2 ▓

    "\xE2\x94\x82", // 0xB3 │

    "\xE2\x94\xA4", // 0xB4 ┤

    "\xE2\x95\xA1", // 0xB5 ╡

    "\xE2\x95\xA2", // 0xB6 ╢

    "\xE2\x95\x96", // 0xB7 ╖

    "\xE2\x95\x95", // 0xB8 ╕

    "\xE2\x95\xA3", // 0xB9 ╣

    "\xE2\x95\x91", // 0xBA ║

    "\xE2\x95\x97", // 0xBB ╗

    "\xE2\x95\x9D", // 0xBC ╝

    "\xE2\x95\x9C", // 0xBD ╜

    "\xE2\x95\x9B", // 0xBE ╛

    "\xE2\x94\x90", // 0xBF ┐



    // 0xC0-0xCF: Box drawing continued

    "\xE2\x94\x94", // 0xC0 └

    "\xE2\x94\xB4", // 0xC1 ┴

    "\xE2\x94\xAC", // 0xC2 ┬

    "\xE2\x94\x9C", // 0xC3 ├

    "\xE2\x94\x80", // 0xC4 ─

    "\xE2\x94\xBC", // 0xC5 ┼

    "\xE2\x95\x9E", // 0xC6 ╞

    "\xE2\x95\x9F", // 0xC7 ╟

    "\xE2\x95\x9A", // 0xC8 ╚

    "\xE2\x95\x94", // 0xC9 ╔

    "\xE2\x95\xA9", // 0xCA ╩

    "\xE2\x95\xA6", // 0xCB ╦

    "\xE2\x95\xA0", // 0xCC ╠

    "\xE2\x95\x90", // 0xCD ═

    "\xE2\x95\xAC", // 0xCE ╬

    "\xE2\x95\xA7", // 0xCF ╧



    // 0xD0-0xDF: Box drawing continued

    "\xE2\x95\xA8", // 0xD0 ╨

    "\xE2\x95\xA4", // 0xD1 ╤

    "\xE2\x95\xA5", // 0xD2 ╥

    "\xE2\x95\x99", // 0xD3 ╙

    "\xE2\x95\x98", // 0xD4 ╘

    "\xE2\x95\x92", // 0xD5 ╒

    "\xE2\x95\x93", // 0xD6 ╓

    "\xE2\x95\xAB", // 0xD7 ╫

    "\xE2\x95\xAA", // 0xD8 ╪

    "\xE2\x94\x98", // 0xD9 ┘

    "\xE2\x94\x8C", // 0xDA ┌

    "\xE2\x96\x88", // 0xDB █

    "\xE2\x96\x84", // 0xDC ▄

    "\xE2\x96\x8C", // 0xDD ▌

    "\xE2\x96\x90", // 0xDE ▐

    "\xE2\x96\x80", // 0xDF ▀



    // 0xE0-0xEF: Greek and math

    "\xCE\xB1",     // 0xE0 α

    "\xC3\x9F",     // 0xE1 ß

    "\xCE\x93",     // 0xE2 Γ

    "\xCF\x80",     // 0xE3 π

    "\xCE\xA3",     // 0xE4 Σ

    "\xCF\x83",     // 0xE5 σ

    "\xC2\xB5",     // 0xE6 µ

    "\xCF\x84",     // 0xE7 τ

    "\xCE\xA6",     // 0xE8 Φ

    "\xCE\x98",     // 0xE9 Θ

    "\xCE\xA9",     // 0xEA Ω

    "\xCE\xB4",     // 0xEB δ

    "\xE2\x88\x9E", // 0xEC ∞

    "\xCF\x86",     // 0xED φ

    "\xCE\xB5",     // 0xEE ε

    "\xE2\x88\xA9", // 0xEF ∩



    // 0xF0-0xFF: Math and symbols

    "\xE2\x89\xA1", // 0xF0 ≡

    "\xC2\xB1",     // 0xF1 ±

    "\xE2\x89\xA5", // 0xF2 ≥

    "\xE2\x89\xA4", // 0xF3 ≤

    "\xE2\x8C\xA0", // 0xF4 ⌠

    "\xE2\x8C\xA1", // 0xF5 ⌡

    "\xC3\xB7",     // 0xF6 ÷

    "\xE2\x89\x88", // 0xF7 ≈

    "\xC2\xB0",     // 0xF8 °

    "\xE2\x88\x99", // 0xF9 ∙

    "\xC2\xB7",     // 0xFA ·

    "\xE2\x88\x9A", // 0xFB √

    "\xE2\x81\xBF", // 0xFC ⁿ

    "\xC2\xB2",     // 0xFD ²

    "\xE2\x96\xA0", // 0xFE ■

    "\xC2\xA0",     // 0xFF NBSP

};



// ─────────────────────────────────────────────────────────────────────────────

// CP437 to UTF-8 conversion

// ─────────────────────────────────────────────────────────────────────────────



std::string cp437ToUtf8(uint8_t cp437_char) {

    return kCp437ToUtf8[cp437_char];

}



// ─────────────────────────────────────────────────────────────────────────────

// Screen context capture

// ─────────────────────────────────────────────────────────────────────────────



std::string captureScreenContext(RuntimeHost& runtime, uint32_t max_chars) {

    // First call: query required cell count

    size_t cell_count = 0;

    legends_text_info_t info{};

    legends_error_t err = runtime.capture_text(nullptr, 0, &cell_count, &info);

    if (err != LEGENDS_OK || cell_count == 0) {

        return {};

    }



    // Second call: fill cell buffer

    std::vector<legends_text_cell_t> cells(cell_count);

    err = runtime.capture_text(cells.data(), cell_count, &cell_count, &info);

    if (err != LEGENDS_OK) {

        return {};

    }



    uint8_t columns = info.columns;

    if (columns == 0) columns = 80;



    // Convert cells to UTF-8 string with newlines at row boundaries

    std::string result;

    result.reserve(cell_count * 2);



    for (size_t i = 0; i < cell_count; ++i) {

        // Add newline at row boundary (except at start)

        if (i > 0 && (i % columns) == 0) {

            // Trim trailing whitespace from the previous row

            while (!result.empty() && result.back() == ' ') {

                result.pop_back();

            }

            result += '\n';

        }



        result += cp437ToUtf8(cells[i].character);

    }



    // Trim trailing whitespace from last row

    while (!result.empty() && result.back() == ' ') {

        result.pop_back();

    }



    // Truncate to max_chars if needed

    if (result.size() > max_chars) {

        result.resize(max_chars);

    }



    return result;

}



std::string captureScreenContext(legends_handle handle, uint32_t max_chars) {

    if (handle == nullptr) {

        return {};

    }

    InProcessEngineRuntime runtime(handle, false);

    return captureScreenContext(runtime, max_chars);

}



// ─────────────────────────────────────────────────────────────────────────────

// Format screen context as structured prompt

// ─────────────────────────────────────────────────────────────────────────────



std::string formatScreenContext(const std::string& screen_text,

                                uint8_t cursor_x, uint8_t cursor_y,

                                uint8_t columns, uint8_t rows) {

    std::string result;

    result.reserve(screen_text.size() + 128);



    result += "Screen (";

    result += std::to_string(columns);

    result += "x";

    result += std::to_string(rows);

    result += "):\n```\n";

    result += screen_text;

    result += "\n```\nCursor at (";

    result += std::to_string(cursor_x);

    result += ",";

    result += std::to_string(cursor_y);

    result += ")";



    return result;

}



} // namespace legends
