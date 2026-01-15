/**
 * @file llm_serializer.h
 * @brief CP437 to UTF-8 conversion and canonical text serialization.
 *
 * Provides utilities for converting DOS text mode content (CP437 encoding)
 * to UTF-8 and generating token-efficient representations for LLMs.
 */

#pragma once

#include <array>
#include <cstdint>
#include <string>
#include <string_view>

namespace legends::llm {

// ─────────────────────────────────────────────────────────────────────────────
// CP437 to Unicode Mapping
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Complete CP437 to Unicode mapping table.
 *
 * Code Page 437 is the original IBM PC character set, including
 * box drawing characters, Greek letters, and various symbols.
 */
constexpr std::array<char32_t, 256> CP437_TO_UNICODE = {{
    // 0x00-0x0F: Control characters rendered as symbols
    U'\u0000', U'\u263A', U'\u263B', U'\u2665', U'\u2666', U'\u2663', U'\u2660', U'\u2022',
    U'\u25D8', U'\u25CB', U'\u25D9', U'\u2642', U'\u2640', U'\u266A', U'\u266B', U'\u263C',
    // 0x10-0x1F: More symbols
    U'\u25BA', U'\u25C4', U'\u2195', U'\u203C', U'\u00B6', U'\u00A7', U'\u25AC', U'\u21A8',
    U'\u2191', U'\u2193', U'\u2192', U'\u2190', U'\u221F', U'\u2194', U'\u25B2', U'\u25BC',
    // 0x20-0x7E: Standard ASCII (maps to itself)
    U' ', U'!', U'"', U'#', U'$', U'%', U'&', U'\'', U'(', U')', U'*', U'+', U',', U'-', U'.', U'/',
    U'0', U'1', U'2', U'3', U'4', U'5', U'6', U'7', U'8', U'9', U':', U';', U'<', U'=', U'>', U'?',
    U'@', U'A', U'B', U'C', U'D', U'E', U'F', U'G', U'H', U'I', U'J', U'K', U'L', U'M', U'N', U'O',
    U'P', U'Q', U'R', U'S', U'T', U'U', U'V', U'W', U'X', U'Y', U'Z', U'[', U'\\', U']', U'^', U'_',
    U'`', U'a', U'b', U'c', U'd', U'e', U'f', U'g', U'h', U'i', U'j', U'k', U'l', U'm', U'n', U'o',
    U'p', U'q', U'r', U's', U't', U'u', U'v', U'w', U'x', U'y', U'z', U'{', U'|', U'}', U'~',
    // 0x7F: House symbol
    U'\u2302',
    // 0x80-0x9F: Extended Latin and symbols
    U'\u00C7', U'\u00FC', U'\u00E9', U'\u00E2', U'\u00E4', U'\u00E0', U'\u00E5', U'\u00E7',
    U'\u00EA', U'\u00EB', U'\u00E8', U'\u00EF', U'\u00EE', U'\u00EC', U'\u00C4', U'\u00C5',
    U'\u00C9', U'\u00E6', U'\u00C6', U'\u00F4', U'\u00F6', U'\u00F2', U'\u00FB', U'\u00F9',
    U'\u00FF', U'\u00D6', U'\u00DC', U'\u00A2', U'\u00A3', U'\u00A5', U'\u20A7', U'\u0192',
    // 0xA0-0xAF: More Latin and symbols
    U'\u00E1', U'\u00ED', U'\u00F3', U'\u00FA', U'\u00F1', U'\u00D1', U'\u00AA', U'\u00BA',
    U'\u00BF', U'\u2310', U'\u00AC', U'\u00BD', U'\u00BC', U'\u00A1', U'\u00AB', U'\u00BB',
    // 0xB0-0xBF: Box drawing light
    U'\u2591', U'\u2592', U'\u2593', U'\u2502', U'\u2524', U'\u2561', U'\u2562', U'\u2556',
    U'\u2555', U'\u2563', U'\u2551', U'\u2557', U'\u255D', U'\u255C', U'\u255B', U'\u2510',
    // 0xC0-0xCF: Box drawing continued
    U'\u2514', U'\u2534', U'\u252C', U'\u251C', U'\u2500', U'\u253C', U'\u255E', U'\u255F',
    U'\u255A', U'\u2554', U'\u2569', U'\u2566', U'\u2560', U'\u2550', U'\u256C', U'\u2567',
    // 0xD0-0xDF: Box drawing continued
    U'\u2568', U'\u2564', U'\u2565', U'\u2559', U'\u2558', U'\u2552', U'\u2553', U'\u256B',
    U'\u256A', U'\u2518', U'\u250C', U'\u2588', U'\u2584', U'\u258C', U'\u2590', U'\u2580',
    // 0xE0-0xEF: Greek letters and math symbols
    U'\u03B1', U'\u00DF', U'\u0393', U'\u03C0', U'\u03A3', U'\u03C3', U'\u00B5', U'\u03C4',
    U'\u03A6', U'\u0398', U'\u03A9', U'\u03B4', U'\u221E', U'\u03C6', U'\u03B5', U'\u2229',
    // 0xF0-0xFF: Math and misc symbols
    U'\u2261', U'\u00B1', U'\u2265', U'\u2264', U'\u2320', U'\u2321', U'\u00F7', U'\u2248',
    U'\u00B0', U'\u2219', U'\u00B7', U'\u221A', U'\u207F', U'\u00B2', U'\u25A0', U'\u00A0'
}};

// ─────────────────────────────────────────────────────────────────────────────
// Character Conversion Functions
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Convert a single CP437 character to its Unicode code point.
 */
[[nodiscard]] constexpr char32_t cp437_to_unicode(uint8_t cp437_char) noexcept {
    return CP437_TO_UNICODE[cp437_char];
}

/**
 * @brief Encode a Unicode code point to UTF-8.
 *
 * @param codepoint Unicode code point
 * @param[out] output Buffer to write UTF-8 bytes (must be at least 4 bytes)
 * @return Number of bytes written (1-4)
 */
[[nodiscard]] inline size_t encode_utf8(char32_t codepoint, char* output) noexcept {
    if (codepoint < 0x80) {
        output[0] = static_cast<char>(codepoint);
        return 1;
    } else if (codepoint < 0x800) {
        output[0] = static_cast<char>(0xC0 | (codepoint >> 6));
        output[1] = static_cast<char>(0x80 | (codepoint & 0x3F));
        return 2;
    } else if (codepoint < 0x10000) {
        output[0] = static_cast<char>(0xE0 | (codepoint >> 12));
        output[1] = static_cast<char>(0x80 | ((codepoint >> 6) & 0x3F));
        output[2] = static_cast<char>(0x80 | (codepoint & 0x3F));
        return 3;
    } else {
        output[0] = static_cast<char>(0xF0 | (codepoint >> 18));
        output[1] = static_cast<char>(0x80 | ((codepoint >> 12) & 0x3F));
        output[2] = static_cast<char>(0x80 | ((codepoint >> 6) & 0x3F));
        output[3] = static_cast<char>(0x80 | (codepoint & 0x3F));
        return 4;
    }
}

/**
 * @brief Convert a single CP437 character to UTF-8 string.
 */
[[nodiscard]] inline std::string cp437_char_to_utf8(uint8_t cp437_char) {
    char32_t unicode = cp437_to_unicode(cp437_char);
    char buffer[4];
    size_t len = encode_utf8(unicode, buffer);
    return std::string(buffer, len);
}

/**
 * @brief Convert a CP437 byte array to UTF-8 string.
 *
 * @param data CP437 encoded bytes
 * @param length Number of bytes
 * @return UTF-8 encoded string
 */
[[nodiscard]] std::string cp437_to_utf8(const uint8_t* data, size_t length);

/**
 * @brief Convert a CP437 string_view to UTF-8.
 */
[[nodiscard]] inline std::string cp437_to_utf8(std::string_view cp437) {
    return cp437_to_utf8(reinterpret_cast<const uint8_t*>(cp437.data()), cp437.size());
}

// ─────────────────────────────────────────────────────────────────────────────
// Box Drawing Characters (UTF-8)
// ─────────────────────────────────────────────────────────────────────────────

namespace box {

/// Double line box drawing characters
constexpr const char* TOP_LEFT     = "\u2554";  // ╔
constexpr const char* TOP_RIGHT    = "\u2557";  // ╗
constexpr const char* BOTTOM_LEFT  = "\u255A";  // ╚
constexpr const char* BOTTOM_RIGHT = "\u255D";  // ╝
constexpr const char* HORIZONTAL   = "\u2550";  // ═
constexpr const char* VERTICAL     = "\u2551";  // ║
constexpr const char* T_DOWN       = "\u2566";  // ╦
constexpr const char* T_UP         = "\u2569";  // ╩
constexpr const char* T_RIGHT      = "\u2560";  // ╠
constexpr const char* T_LEFT       = "\u2563";  // ╣
constexpr const char* CROSS        = "\u256C";  // ╬

/// Single line box drawing characters
constexpr const char* LIGHT_HORIZONTAL = "\u2500";  // ─
constexpr const char* LIGHT_VERTICAL   = "\u2502";  // │
constexpr const char* LIGHT_TOP_LEFT   = "\u250C";  // ┌
constexpr const char* LIGHT_TOP_RIGHT  = "\u2510";  // ┐
constexpr const char* LIGHT_BOT_LEFT   = "\u2514";  // └
constexpr const char* LIGHT_BOT_RIGHT  = "\u2518";  // ┘

} // namespace box

// ─────────────────────────────────────────────────────────────────────────────
// Text Serialization
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Options for canonical text serialization.
 */
struct SerializerOptions {
    bool include_box_border{true};      ///< Add box drawing border around screen
    bool trim_trailing_spaces{true};    ///< Remove trailing spaces from lines
    bool mark_cursor{true};             ///< Mark cursor position with underscore
    bool use_rle{false};                ///< Apply run-length encoding
    size_t rle_threshold{4};            ///< Minimum run length for RLE
};

/**
 * @brief Serialize text mode screen to canonical format.
 *
 * Converts CP437 screen data to UTF-8 with optional box borders,
 * cursor marking, and RLE compression.
 *
 * @param data Raw screen data (character bytes only, no attributes)
 * @param columns Number of columns
 * @param rows Number of rows
 * @param cursor_x Cursor X position
 * @param cursor_y Cursor Y position
 * @param cursor_visible Whether cursor is visible
 * @param options Serialization options
 * @return Canonical text representation
 */
[[nodiscard]] std::string serialize_text_screen(
    const uint8_t* data,
    uint8_t columns,
    uint8_t rows,
    uint8_t cursor_x,
    uint8_t cursor_y,
    bool cursor_visible,
    const SerializerOptions& options = {}
);

/**
 * @brief Serialize text mode screen with attributes.
 *
 * @param char_data Character bytes (CP437)
 * @param attr_data Attribute bytes (foreground/background colors)
 * @param columns Number of columns
 * @param rows Number of rows
 * @param cursor_x Cursor X position
 * @param cursor_y Cursor Y position
 * @param cursor_visible Whether cursor is visible
 * @param options Serialization options
 * @return Canonical text representation
 */
[[nodiscard]] std::string serialize_text_screen_with_attrs(
    const uint8_t* char_data,
    const uint8_t* attr_data,
    uint8_t columns,
    uint8_t rows,
    uint8_t cursor_x,
    uint8_t cursor_y,
    bool cursor_visible,
    const SerializerOptions& options = {}
);

// ─────────────────────────────────────────────────────────────────────────────
// String Utilities
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Trim trailing spaces from a string.
 */
[[nodiscard]] std::string trim_trailing_spaces(std::string_view str);

/**
 * @brief Trim trailing spaces from each line in a multi-line string.
 */
[[nodiscard]] std::string trim_lines(const std::string& text);

/**
 * @brief Apply run-length encoding to repeated characters.
 *
 * Replaces runs of 4+ identical characters with notation like "~5x ".
 *
 * @param text Input text
 * @param threshold Minimum run length to encode (default: 4)
 * @return RLE-encoded text
 */
[[nodiscard]] std::string apply_rle(const std::string& text, size_t threshold = 4);

/**
 * @brief Decode RLE-encoded text.
 *
 * @param encoded RLE-encoded text
 * @return Decoded text
 */
[[nodiscard]] std::string decode_rle(const std::string& encoded);

// ─────────────────────────────────────────────────────────────────────────────
// JSON Utilities
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Escape a string for JSON inclusion.
 *
 * Escapes backslash, quotes, and control characters.
 */
[[nodiscard]] std::string json_escape(std::string_view str);

/**
 * @brief Unescape a JSON string value.
 */
[[nodiscard]] std::string json_unescape(std::string_view str);

// ─────────────────────────────────────────────────────────────────────────────
// Token Estimation
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Estimate token count for text.
 *
 * Uses a rough heuristic based on typical LLM tokenization:
 * - ~4 characters per token for English text
 * - Box drawing characters count as ~2 tokens each
 * - Whitespace and punctuation may affect tokenization
 *
 * @param text Text to estimate
 * @return Estimated token count
 */
[[nodiscard]] size_t estimate_tokens(std::string_view text) noexcept;

} // namespace legends::llm
