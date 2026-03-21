// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AI Assistant overlay panel — rendering, keyboard input, chat display.

#include "app/ai_panel.h"
#include "app/action_bus.h"
#include "legends/internal/cp437_font_8x16.h"

#include <gsl-lite/gsl-lite.hpp>

#include <algorithm>
#include <cstring>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// Text rendering helpers (same pattern as MenuSystem)
// ─────────────────────────────────────────────────────────────────────────────

namespace {

// Modifies rgb buffer in-place — darkens each pixel to 1/4 brightness.
void darkenRect(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
                int x, int y, int w, int h) {
    for (int py = y; py < y + h && py < buf_h; ++py) {
        if (py < 0) continue;
        for (int px = x; px < x + w && px < buf_w; ++px) {
            if (px < 0) continue;
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb[idx]     = static_cast<uint8_t>(rgb[idx] / 4);
            rgb[idx + 1] = static_cast<uint8_t>(rgb[idx + 1] / 4);
            rgb[idx + 2] = static_cast<uint8_t>(rgb[idx + 2] / 4);
        }
    }
}

// Modifies rgb buffer in-place — renders a single CP437 glyph.
void drawChar(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
              int x, int y, uint8_t ch,
              uint8_t fr, uint8_t fg, uint8_t fb,
              uint8_t br, uint8_t bg, uint8_t bb) {
    const auto& font = internal::CP437_FONT_8x16;
    int glyph_offset = static_cast<int>(ch) * 16;

    for (int row = 0; row < 16; ++row) {
        int py = y + row;
        if (py < 0 || py >= buf_h) continue;

        uint8_t bits = font[static_cast<size_t>(glyph_offset + row)];
        for (int col = 0; col < 8; ++col) {
            int px = x + col;
            if (px < 0 || px >= buf_w) continue;

            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            bool set = (bits & (0x80 >> col)) != 0;
            rgb[idx]     = set ? fr : br;
            rgb[idx + 1] = set ? fg : bg;
            rgb[idx + 2] = set ? fb : bb;
        }
    }
}

// Modifies rgb buffer in-place — renders a string of CP437 glyphs.
void drawString(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
                int x, int y, const std::string& text,
                uint8_t fr, uint8_t fg, uint8_t fb,
                uint8_t br, uint8_t bg, uint8_t bb) {
    for (size_t i = 0; i < text.size(); ++i) {
        drawChar(rgb, buf_w, buf_h, pitch,
                 x + static_cast<int>(i) * 8, y,
                 static_cast<uint8_t>(text[i]),
                 fr, fg, fb, br, bg, bb);
    }
}

// Modifies rgb buffer in-place — fills a rectangle with a solid color.
void fillRect(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
              int x, int y, int w, int h,
              uint8_t r, uint8_t g, uint8_t b) {
    for (int py = y; py < y + h && py < buf_h; ++py) {
        if (py < 0) continue;
        for (int px = x; px < x + w && px < buf_w; ++px) {
            if (px < 0) continue;
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb[idx]     = r;
            rgb[idx + 1] = g;
            rgb[idx + 2] = b;
        }
    }
}

// Word-wrap text into lines of max_chars width
std::vector<std::string> wordWrap(const std::string& text, int max_chars) {
    std::vector<std::string> lines;
    if (max_chars <= 0) return lines;

    size_t pos = 0;
    while (pos < text.size()) {
        // Find next newline
        size_t nl = text.find('\n', pos);
        std::string segment;
        if (nl != std::string::npos) {
            segment = text.substr(pos, nl - pos);
            pos = nl + 1;
        } else {
            segment = text.substr(pos);
            pos = text.size();
        }

        // Wrap the segment
        if (segment.empty()) {
            lines.emplace_back();
            continue;
        }

        size_t seg_pos = 0;
        while (seg_pos < segment.size()) {
            if (static_cast<int>(segment.size() - seg_pos) <= max_chars) {
                lines.push_back(segment.substr(seg_pos));
                break;
            }

            // Find last space within max_chars
            size_t break_at = static_cast<size_t>(max_chars);
            size_t last_space = segment.rfind(' ', seg_pos + break_at);
            if (last_space != std::string::npos && last_space > seg_pos) {
                lines.push_back(segment.substr(seg_pos, last_space - seg_pos));
                seg_pos = last_space + 1;
            } else {
                // No space found, hard break
                lines.push_back(segment.substr(seg_pos, break_at));
                seg_pos += break_at;
            }
        }
    }

    return lines;
}

} // anonymous namespace

// ─────────────────────────────────────────────────────────────────────────────
// Initialization
// ─────────────────────────────────────────────────────────────────────────────

void AIPanel::initialize(ActionBus* bus) {
    gsl_Expects(bus != nullptr);
    bus_ = bus;
}

// ─────────────────────────────────────────────────────────────────────────────
// Open / Close
// ─────────────────────────────────────────────────────────────────────────────

void AIPanel::open() {
    open_ = true;
}

void AIPanel::close() {
    open_ = false;
}

// ─────────────────────────────────────────────────────────────────────────────
// Keyboard input
// ─────────────────────────────────────────────────────────────────────────────

bool AIPanel::handleKey(uint16_t scancode, bool down, uint8_t /*character*/) {
    if (!open_ || !down) return false;

    // SDL3 scancodes
    constexpr uint16_t kEnter     = 0x28;
    constexpr uint16_t kEsc       = 0x29;
    constexpr uint16_t kBackspace = 0x2A;
    constexpr uint16_t kUp        = 0x52;
    constexpr uint16_t kDown      = 0x51;

    switch (scancode) {
        case kEnter:
            submitQuery();
            return true;

        case kEsc:
            close();
            return true;

        case kBackspace:
            if (!input_text_.empty()) {
                input_text_.pop_back();
            }
            return true;

        case kUp:
            scroll_offset_ = std::max(0, scroll_offset_ - 1);
            return true;

        case kDown:
            scroll_offset_ += 1;
            return true;

        default:
            return false;
    }
}

void AIPanel::handleTextInput(char ch) {
    if (!open_) return;

    // Accept printable ASCII characters
    if (ch >= 0x20 && ch <= 0x7E) {
        input_text_ += ch;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Submit query
// ─────────────────────────────────────────────────────────────────────────────

void AIPanel::submitQuery() {
    if (input_text_.empty()) return;

    addUserMessage(input_text_);
    input_text_.clear();

    if (bus_) {
        bus_->dispatch(Action::AISubmitQuery);
        waiting_ = true;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Chat history management
// ─────────────────────────────────────────────────────────────────────────────

void AIPanel::addResponse(const std::string& text) {
    history_.push_back({false, text});
    waiting_ = false;
    streaming_text_.clear();
}

void AIPanel::addUserMessage(const std::string& text) {
    history_.push_back({true, text});
}

void AIPanel::setStreamingText(const std::string& text) {
    streaming_text_ = text;
}

void AIPanel::clearHistory() {
    history_.clear();
    streaming_text_.clear();
    scroll_offset_ = 0;
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering
// ─────────────────────────────────────────────────────────────────────────────

void AIPanel::render(uint8_t* rgb_buffer, uint16_t width, uint16_t height,
                     uint32_t pitch) const {
    gsl_Expects(rgb_buffer != nullptr);
    if (!open_) return;

    // Default pitch = tightly packed RGB24
    if (pitch == 0) pitch = static_cast<uint32_t>(width) * 3;

    // Panel dimensions (right 40% of screen)
    int panel_w = static_cast<int>(static_cast<float>(width) * panel_width_fraction_);
    int panel_x = width - panel_w;
    int panel_h = height;

    // Darken the panel area for semi-transparent background
    darkenRect(rgb_buffer, width, height, pitch,
               panel_x, 0, panel_w, panel_h);

    // Fill with dark background
    fillRect(rgb_buffer, width, height, pitch,
             panel_x, 0, panel_w, panel_h,
             20, 20, 30);

    // ── Title bar ──────────────────────────────────────────────────────
    int title_h = kCharH + 4;
    fillRect(rgb_buffer, width, height, pitch,
             panel_x, 0, panel_w, title_h,
             40, 40, 80);

    std::string title = " AI Assistant";
    drawString(rgb_buffer, width, height, pitch,
               panel_x + kPadding, 2, title,
               220, 220, 255,    // fg: light blue-white
               40, 40, 80);      // bg: dark blue

    // ── Input box at bottom ────────────────────────────────────────────
    int input_h = kCharH + kPadding;
    int input_y = height - input_h;
    fillRect(rgb_buffer, width, height, pitch,
             panel_x, input_y, panel_w, input_h,
             30, 30, 50);

    // Draw input text with cursor
    int max_input_chars = (panel_w - kPadding * 2) / kCharW;
    std::string display_input = input_text_;
    if (static_cast<int>(display_input.size()) > max_input_chars - 1) {
        display_input = display_input.substr(
            display_input.size() - static_cast<size_t>(max_input_chars - 1));
    }
    display_input += '_'; // cursor

    drawString(rgb_buffer, width, height, pitch,
               panel_x + kPadding, input_y + kPadding / 2,
               display_input,
               200, 200, 200,    // fg: light gray
               30, 30, 50);      // bg: dark

    // ── Chat history area ──────────────────────────────────────────────
    int chat_y_start = title_h + kPadding;
    int chat_y_end = input_y - kPadding;
    int chat_area_h = chat_y_end - chat_y_start;
    int max_text_chars = (panel_w - kPadding * 2) / kCharW;
    if (max_text_chars <= 0) return;

    // Build all wrapped lines for display
    struct DisplayLine {
        std::string text;
        bool is_user;
    };
    std::vector<DisplayLine> all_lines;

    for (const auto& msg : history_) {
        // Add prefix
        std::string prefix = msg.is_user ? "> " : "";
        auto wrapped = wordWrap(prefix + msg.text, max_text_chars);
        for (auto& line : wrapped) {
            all_lines.push_back({std::move(line), msg.is_user});
        }
        // Add blank line between messages
        all_lines.push_back({"", msg.is_user});
    }

    // Show "Waiting..." indicator
    if (waiting_) {
        if (!streaming_text_.empty()) {
            auto wrapped = wordWrap(streaming_text_, max_text_chars);
            for (auto& line : wrapped) {
                all_lines.push_back({std::move(line), false});
            }
        } else {
            all_lines.push_back({"Waiting...", false});
        }
    }

    // Calculate visible lines
    int visible_lines = chat_area_h / kCharH;
    int total_lines = static_cast<int>(all_lines.size());
    int start_line = std::max(0, total_lines - visible_lines - scroll_offset_);

    // Draw visible lines
    int draw_y = chat_y_start;
    for (int i = start_line; i < total_lines && draw_y + kCharH <= chat_y_end; ++i) {
        const auto& line = all_lines[static_cast<size_t>(i)];

        // User messages in cyan, assistant in green
        uint8_t fr, fg_c, fb;
        if (line.is_user) {
            fr = 100; fg_c = 200; fb = 255; // cyan
        } else {
            fr = 150; fg_c = 220; fb = 150; // green
        }

        if (!line.text.empty()) {
            drawString(rgb_buffer, width, height, pitch,
                       panel_x + kPadding, draw_y,
                       line.text,
                       fr, fg_c, fb,
                       20, 20, 30);   // bg: panel background
        }

        draw_y += kCharH;
    }
}

} // namespace legends
