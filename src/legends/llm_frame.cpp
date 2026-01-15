/**
 * @file llm_frame.cpp
 * @brief Implementation of LLM frame structures.
 */

#include <legends/llm_frame.h>
#include <legends/llm_serializer.h>
#include <chrono>
#include <iomanip>
#include <sstream>

namespace legends::llm {

// ─────────────────────────────────────────────────────────────────────────────
// TokenEfficientFrame Implementation
// ─────────────────────────────────────────────────────────────────────────────

std::string TokenEfficientFrame::to_json() const {
    std::ostringstream oss;
    oss << "{";
    oss << "\"frame_id\":" << frame_id << ",";
    oss << "\"timestamp_us\":" << timestamp_us << ",";
    oss << "\"mode\":" << static_cast<int>(mode) << ",";
    oss << "\"mode_name\":\"" << to_string(mode) << "\",";
    oss << "\"columns\":" << static_cast<int>(text_columns) << ",";
    oss << "\"rows\":" << static_cast<int>(text_rows) << ",";

    // Escape text content for JSON
    oss << "\"text\":\"" << json_escape(text_content) << "\",";

    // Cursor
    oss << "\"cursor\":{";
    oss << "\"x\":" << static_cast<int>(cursor.column) << ",";
    oss << "\"y\":" << static_cast<int>(cursor.row) << ",";
    oss << "\"visible\":" << (cursor.visible ? "true" : "false");
    oss << "},";

    // Input status
    oss << "\"input\":{";
    oss << "\"pending_keys\":" << static_cast<int>(input_status.pending_keystrokes) << ",";
    oss << "\"pending_mouse\":" << static_cast<int>(input_status.pending_mouse_events);
    if (input_status.last_key_name) {
        oss << ",\"last_key\":\"" << *input_status.last_key_name << "\"";
    }
    oss << "},";

    // Hypercall log
    oss << "\"hypercalls\":[";
    for (size_t i = 0; i < hypercall_log.size(); ++i) {
        if (i > 0) oss << ",";
        const auto& entry = hypercall_log[i];
        oss << "{\"cmd\":" << entry.command_id
            << ",\"a\":" << entry.param_a
            << ",\"b\":" << entry.param_b
            << ",\"status\":" << entry.status
            << ",\"ok\":" << (entry.success ? "true" : "false") << "}";
    }
    oss << "],";

    // Metadata
    if (!program_name.empty()) {
        oss << "\"program\":\"" << json_escape(program_name) << "\",";
    }
    if (!working_dir.empty()) {
        oss << "\"cwd\":\"" << json_escape(working_dir) << "\",";
    }

    // Flags
    oss << "\"flags\":" << static_cast<int>(flags);

    oss << "}";
    return oss.str();
}

std::string TokenEfficientFrame::to_canonical_text() const {
    std::ostringstream oss;

    // Frame header (minimal)
    oss << "[Frame " << frame_id << " @ " << timestamp_us << "us]\n";

    // Mode indicator
    oss << "[Mode: " << to_string(mode) << "]\n";

    if (!is_text()) {
        oss << "[Graphics mode - text unavailable]\n";
        return oss.str();
    }

    // Screen border (top)
    oss << box::TOP_LEFT;
    for (int i = 0; i < text_columns; ++i) {
        oss << box::HORIZONTAL;
    }
    oss << box::TOP_RIGHT << "\n";

    // Text content with side borders
    std::istringstream content_stream(text_content);
    std::string line;
    int row = 0;
    while (std::getline(content_stream, line) && row < text_rows) {
        oss << box::VERTICAL;

        // Pad or truncate line to exact column width
        std::string display_line = line;
        if (display_line.length() < text_columns) {
            display_line.append(text_columns - display_line.length(), ' ');
        } else if (display_line.length() > text_columns) {
            display_line = display_line.substr(0, text_columns);
        }

        // Mark cursor position
        if (cursor.visible && row == cursor.row) {
            if (cursor.column < display_line.length()) {
                display_line[cursor.column] = '_';
            }
        }

        oss << display_line << box::VERTICAL << "\n";
        ++row;
    }

    // Fill remaining rows if content is short
    while (row < text_rows) {
        oss << box::VERTICAL;
        std::string empty_line(text_columns, ' ');
        if (cursor.visible && row == cursor.row && cursor.column < text_columns) {
            empty_line[cursor.column] = '_';
        }
        oss << empty_line << box::VERTICAL << "\n";
        ++row;
    }

    // Screen border (bottom)
    oss << box::BOTTOM_LEFT;
    for (int i = 0; i < text_columns; ++i) {
        oss << box::HORIZONTAL;
    }
    oss << box::BOTTOM_RIGHT << "\n";

    // Cursor position (explicit)
    oss << "[Cursor: " << static_cast<int>(cursor.column) << ","
        << static_cast<int>(cursor.row);
    if (!cursor.visible) {
        oss << " (hidden)";
    }
    oss << "]\n";

    // Input status
    if (input_status.pending_keystrokes > 0 || input_status.pending_mouse_events > 0) {
        oss << "[Input pending:";
        if (input_status.pending_keystrokes > 0) {
            oss << " " << static_cast<int>(input_status.pending_keystrokes) << " keys";
        }
        if (input_status.pending_mouse_events > 0) {
            oss << " " << static_cast<int>(input_status.pending_mouse_events) << " mouse";
        }
        oss << "]\n";
    }

    // Hypercall log (if any)
    if (!hypercall_log.empty()) {
        oss << "[Recent hypercalls:]\n";
        for (const auto& entry : hypercall_log) {
            oss << "  CMD=0x" << std::hex << std::setfill('0') << std::setw(4)
                << entry.command_id
                << " A=0x" << std::setw(8) << entry.param_a
                << " B=0x" << std::setw(8) << entry.param_b
                << " -> " << (entry.success ? "OK" : "ERR")
                << std::dec << "\n";
        }
    }

    return oss.str();
}

size_t TokenEfficientFrame::estimate_tokens() const noexcept {
    // Rough estimation:
    // - Text content: ~4 characters per token
    // - Box drawing: ~2 tokens per character
    // - Header/metadata: ~50 tokens

    size_t text_tokens = text_content.length() / 4;
    size_t box_chars = (text_columns + 2) * 2 + text_rows * 2;
    size_t box_tokens = box_chars * 2;

    return text_tokens + box_tokens + 50;
}

// ─────────────────────────────────────────────────────────────────────────────
// FrameBuilder Implementation
// ─────────────────────────────────────────────────────────────────────────────

TokenEfficientFrame FrameBuilder::build_full_frame(
    uint8_t columns,
    uint8_t rows,
    const uint8_t* screen_data,
    uint8_t cursor_x,
    uint8_t cursor_y,
    bool cursor_visible
) {
    TokenEfficientFrame frame;

    // Increment frame ID
    frame.frame_id = ++frame_id_;

    // Timestamp
    auto now = std::chrono::high_resolution_clock::now();
    auto duration = now.time_since_epoch();
    frame.timestamp_us = std::chrono::duration_cast<std::chrono::microseconds>(duration).count();

    // Determine video mode
    if (columns == 40 && rows == 25) {
        frame.mode = VideoMode::Text40x25;
    } else if (columns == 80 && rows == 25) {
        frame.mode = VideoMode::Text80x25;
    } else if (columns == 80 && rows == 43) {
        frame.mode = VideoMode::Text80x43;
    } else if (columns == 80 && rows == 50) {
        frame.mode = VideoMode::Text80x50;
    } else {
        frame.mode = VideoMode::Unknown;
    }

    frame.text_columns = columns;
    frame.text_rows = rows;

    // Set flags
    frame.flags = FrameFlags::TextMode;
    if (cursor_visible) {
        frame.flags |= FrameFlags::CursorVisible;
    }

    // Serialize text content
    frame.text_content = serialize_text_mode(columns, rows, screen_data);

    // Cursor state
    frame.cursor.column = cursor_x;
    frame.cursor.row = cursor_y;
    frame.cursor.visible = cursor_visible;
    frame.cursor.blink_phase = true;

    // Copy hypercall log
    size_t log_count = std::min(hypercall_log_.size(), hypercall_log_limit_);
    if (log_count > 0) {
        size_t start = hypercall_log_.size() - log_count;
        frame.hypercall_log.assign(
            hypercall_log_.begin() + start,
            hypercall_log_.end()
        );
    }

    // Cache this frame for diff
    last_frame_ = frame;

    return frame;
}

TokenEfficientFrame FrameBuilder::build_diff_frame(
    uint8_t columns,
    uint8_t rows,
    const uint8_t* screen_data,
    uint8_t cursor_x,
    uint8_t cursor_y,
    bool cursor_visible
) {
    // For now, just return full frame
    // TODO: Implement actual diff logic
    auto frame = build_full_frame(columns, rows, screen_data, cursor_x, cursor_y, cursor_visible);
    frame.flags |= FrameFlags::Dirty;
    return frame;
}

size_t FrameBuilder::estimate_current_tokens() const noexcept {
    if (last_frame_) {
        return last_frame_->estimate_tokens();
    }
    return 0;
}

void FrameBuilder::add_hypercall_log(const HypercallLogEntry& entry) {
    hypercall_log_.push_back(entry);

    // Keep log bounded
    if (hypercall_log_.size() > hypercall_log_limit_ * 2) {
        hypercall_log_.erase(
            hypercall_log_.begin(),
            hypercall_log_.begin() + hypercall_log_limit_
        );
    }
}

void FrameBuilder::reset() noexcept {
    last_frame_.reset();
    // Don't reset frame_id_ - keep it monotonic
}

std::string FrameBuilder::serialize_text_mode(
    uint8_t columns,
    uint8_t rows,
    const uint8_t* screen_data
) {
    if (screen_data == nullptr) {
        return {};
    }

    std::ostringstream oss;

    for (uint8_t row = 0; row < rows; ++row) {
        std::string line;
        for (uint8_t col = 0; col < columns; ++col) {
            size_t idx = row * columns + col;
            line += cp437_char_to_utf8(screen_data[idx]);
        }

        if (trim_trailing_spaces_) {
            line = legends::llm::trim_trailing_spaces(line);
        }

        oss << line;
        if (row < rows - 1) {
            oss << '\n';
        }
    }

    std::string result = oss.str();

    if (rle_enabled_) {
        result = apply_rle(result);
    }

    return result;
}

std::string FrameBuilder::apply_rle(const std::string& text) {
    return legends::llm::apply_rle(text);
}

std::string FrameBuilder::trim_lines(const std::string& text) {
    return legends::llm::trim_lines(text);
}

} // namespace legends::llm
