/**
 * @file llm_serializer.cpp
 * @brief Implementation of LLM text serialization utilities.
 */

#include <aibox/llm_serializer.h>
#include <algorithm>
#include <cctype>
#include <iomanip>
#include <sstream>

namespace aibox::llm {

// ─────────────────────────────────────────────────────────────────────────────
// CP437 to UTF-8 Conversion
// ─────────────────────────────────────────────────────────────────────────────

std::string cp437_to_utf8(const uint8_t* data, size_t length) {
    if (data == nullptr || length == 0) {
        return {};
    }

    std::string result;
    result.reserve(length * 2);  // Estimate: most chars need 1-2 bytes

    for (size_t i = 0; i < length; ++i) {
        char32_t unicode = cp437_to_unicode(data[i]);
        char buffer[4];
        size_t len = encode_utf8(unicode, buffer);
        result.append(buffer, len);
    }

    return result;
}

// ─────────────────────────────────────────────────────────────────────────────
// String Utilities
// ─────────────────────────────────────────────────────────────────────────────

std::string trim_trailing_spaces(std::string_view str) {
    auto end = str.find_last_not_of(' ');
    if (end == std::string_view::npos) {
        return {};
    }
    return std::string(str.substr(0, end + 1));
}

std::string trim_lines(const std::string& text) {
    std::ostringstream result;
    std::istringstream stream(text);
    std::string line;

    while (std::getline(stream, line)) {
        result << trim_trailing_spaces(line) << '\n';
    }

    return result.str();
}

std::string apply_rle(const std::string& text, size_t threshold) {
    if (text.empty() || threshold < 2) {
        return text;
    }

    std::ostringstream result;
    size_t i = 0;

    while (i < text.size()) {
        char c = text[i];
        size_t run_start = i;

        // Count consecutive identical characters
        while (i < text.size() && text[i] == c) {
            ++i;
        }

        size_t run_length = i - run_start;

        if (run_length >= threshold) {
            // Encode as RLE: ~<count>x<char>
            result << '~' << run_length << 'x' << c;
        } else {
            // Output literally
            for (size_t j = 0; j < run_length; ++j) {
                result << c;
            }
        }
    }

    return result.str();
}

std::string decode_rle(const std::string& encoded) {
    std::ostringstream result;
    size_t i = 0;

    while (i < encoded.size()) {
        if (encoded[i] == '~') {
            // Parse RLE sequence: ~<count>x<char>
            ++i;
            size_t count = 0;
            while (i < encoded.size() && std::isdigit(encoded[i])) {
                count = count * 10 + (encoded[i] - '0');
                ++i;
            }

            if (i < encoded.size() && encoded[i] == 'x') {
                ++i;
                if (i < encoded.size()) {
                    char c = encoded[i++];
                    for (size_t j = 0; j < count; ++j) {
                        result << c;
                    }
                }
            }
        } else {
            result << encoded[i++];
        }
    }

    return result.str();
}

// ─────────────────────────────────────────────────────────────────────────────
// JSON Utilities
// ─────────────────────────────────────────────────────────────────────────────

std::string json_escape(std::string_view str) {
    std::ostringstream result;

    for (char c : str) {
        switch (c) {
            case '"':  result << "\\\""; break;
            case '\\': result << "\\\\"; break;
            case '\n': result << "\\n"; break;
            case '\r': result << "\\r"; break;
            case '\t': result << "\\t"; break;
            case '\b': result << "\\b"; break;
            case '\f': result << "\\f"; break;
            default:
                if (static_cast<unsigned char>(c) < 0x20) {
                    // Control character - escape as \uXXXX
                    result << "\\u"
                           << std::hex << std::setfill('0') << std::setw(4)
                           << static_cast<int>(static_cast<unsigned char>(c))
                           << std::dec;
                } else {
                    result << c;
                }
        }
    }

    return result.str();
}

std::string json_unescape(std::string_view str) {
    std::ostringstream result;
    size_t i = 0;

    while (i < str.size()) {
        if (str[i] == '\\' && i + 1 < str.size()) {
            ++i;
            switch (str[i]) {
                case '"':  result << '"';  break;
                case '\\': result << '\\'; break;
                case 'n':  result << '\n'; break;
                case 'r':  result << '\r'; break;
                case 't':  result << '\t'; break;
                case 'b':  result << '\b'; break;
                case 'f':  result << '\f'; break;
                case 'u':
                    // Parse \uXXXX
                    if (i + 4 < str.size()) {
                        try {
                            int codepoint = std::stoi(
                                std::string(str.substr(i + 1, 4)),
                                nullptr, 16
                            );
                            char buffer[4];
                            size_t len = encode_utf8(codepoint, buffer);
                            result.write(buffer, len);
                            i += 4;
                        } catch (...) {
                            result << '\\' << 'u';
                        }
                    }
                    break;
                default:
                    result << '\\' << str[i];
            }
            ++i;
        } else {
            result << str[i++];
        }
    }

    return result.str();
}

// ─────────────────────────────────────────────────────────────────────────────
// Token Estimation
// ─────────────────────────────────────────────────────────────────────────────

size_t estimate_tokens(std::string_view text) noexcept {
    if (text.empty()) {
        return 0;
    }

    // Rough heuristics:
    // - ASCII text: ~4 characters per token
    // - Multi-byte UTF-8: ~1-2 tokens per character
    // - Whitespace and punctuation may affect tokenization

    size_t char_count = 0;
    size_t multibyte_count = 0;

    for (size_t i = 0; i < text.size(); ++i) {
        unsigned char c = static_cast<unsigned char>(text[i]);
        if ((c & 0x80) == 0) {
            // ASCII
            ++char_count;
        } else if ((c & 0xC0) == 0xC0) {
            // Start of multi-byte sequence
            ++multibyte_count;
            // Skip continuation bytes
            while (i + 1 < text.size() &&
                   (static_cast<unsigned char>(text[i + 1]) & 0xC0) == 0x80) {
                ++i;
            }
        }
    }

    // Estimate: ASCII chars / 4 + multibyte * 2
    return (char_count / 4) + (multibyte_count * 2) + 1;
}

// ─────────────────────────────────────────────────────────────────────────────
// Text Serialization
// ─────────────────────────────────────────────────────────────────────────────

std::string serialize_text_screen(
    const uint8_t* data,
    uint8_t columns,
    uint8_t rows,
    uint8_t cursor_x,
    uint8_t cursor_y,
    bool cursor_visible,
    const SerializerOptions& options
) {
    if (data == nullptr || columns == 0 || rows == 0) {
        return {};
    }

    std::ostringstream oss;

    // Top border
    if (options.include_box_border) {
        oss << box::TOP_LEFT;
        for (int i = 0; i < columns; ++i) {
            oss << box::HORIZONTAL;
        }
        oss << box::TOP_RIGHT << '\n';
    }

    // Screen content
    for (uint8_t row = 0; row < rows; ++row) {
        if (options.include_box_border) {
            oss << box::VERTICAL;
        }

        std::string line;
        for (uint8_t col = 0; col < columns; ++col) {
            size_t idx = row * columns + col;
            uint8_t ch = data[idx];

            // Mark cursor position
            if (options.mark_cursor && cursor_visible &&
                row == cursor_y && col == cursor_x) {
                line += '_';
            } else {
                line += cp437_char_to_utf8(ch);
            }
        }

        if (options.trim_trailing_spaces) {
            line = trim_trailing_spaces(line);
            // Pad back if we have a border
            if (options.include_box_border) {
                while (line.length() < columns) {
                    line += ' ';
                }
            }
        }

        oss << line;

        if (options.include_box_border) {
            oss << box::VERTICAL;
        }
        oss << '\n';
    }

    // Bottom border
    if (options.include_box_border) {
        oss << box::BOTTOM_LEFT;
        for (int i = 0; i < columns; ++i) {
            oss << box::HORIZONTAL;
        }
        oss << box::BOTTOM_RIGHT << '\n';
    }

    std::string result = oss.str();

    if (options.use_rle) {
        result = apply_rle(result, options.rle_threshold);
    }

    return result;
}

std::string serialize_text_screen_with_attrs(
    const uint8_t* char_data,
    const uint8_t* attr_data,
    uint8_t columns,
    uint8_t rows,
    uint8_t cursor_x,
    uint8_t cursor_y,
    bool cursor_visible,
    const SerializerOptions& options
) {
    // For now, ignore attributes and just serialize characters
    // Future: could include color information in special format
    (void)attr_data;
    return serialize_text_screen(
        char_data, columns, rows,
        cursor_x, cursor_y, cursor_visible,
        options
    );
}

} // namespace aibox::llm
