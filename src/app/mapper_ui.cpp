// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MapperUI — interactive key mapper visual overlay implementation.
// REQ-MAPPER-001: Key mapper visual UI

#include "app/mapper_ui.h"
#include "app/action_bus.h"
#include "app/input_mapper.h"
#include "app/overlay_render.h"

#include <algorithm>
#include <cstring>
#include <span>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// SDL3 scancode names (subset for display)
// ─────────────────────────────────────────────────────────────────────────────

namespace {

struct ScancodeEntry {
    uint16_t    code;
    const char* name;
};

// Common SDL3 scancodes for the mapping list.
// This covers the standard keyboard; additional keys can be added as needed.
constexpr ScancodeEntry kScancodeNames[] = {
    {0x04, "A"},     {0x05, "B"},     {0x06, "C"},     {0x07, "D"},
    {0x08, "E"},     {0x09, "F"},     {0x0A, "G"},     {0x0B, "H"},
    {0x0C, "I"},     {0x0D, "J"},     {0x0E, "K"},     {0x0F, "L"},
    {0x10, "M"},     {0x11, "N"},     {0x12, "O"},     {0x13, "P"},
    {0x14, "Q"},     {0x15, "R"},     {0x16, "S"},     {0x17, "T"},
    {0x18, "U"},     {0x19, "V"},     {0x1A, "W"},     {0x1B, "X"},
    {0x1C, "Y"},     {0x1D, "Z"},
    {0x1E, "1"},     {0x1F, "2"},     {0x20, "3"},     {0x21, "4"},
    {0x22, "5"},     {0x23, "6"},     {0x24, "7"},     {0x25, "8"},
    {0x26, "9"},     {0x27, "0"},
    {0x28, "Return"},{0x29, "Escape"},{0x2A, "Backspace"},
    {0x2B, "Tab"},   {0x2C, "Space"},
    {0x3A, "F1"},    {0x3B, "F2"},    {0x3C, "F3"},    {0x3D, "F4"},
    {0x3E, "F5"},    {0x3F, "F6"},    {0x40, "F7"},    {0x41, "F8"},
    {0x42, "F9"},    {0x43, "F10"},   {0x44, "F11"},   {0x45, "F12"},
    {0x4F, "Right"}, {0x50, "Left"},  {0x51, "Down"},  {0x52, "Up"},
    {0xE0, "LCtrl"}, {0xE1, "LShift"},{0xE2, "LAlt"},
    {0xE4, "RCtrl"}, {0xE5, "RShift"},{0xE6, "RAlt"},
};

constexpr size_t kScancodeNameCount = sizeof(kScancodeNames) / sizeof(kScancodeNames[0]);

const char* scancodeName(uint16_t code) {
    for (size_t i = 0; i < kScancodeNameCount; ++i) {
        if (kScancodeNames[i].code == code) return kScancodeNames[i].name;
    }
    return nullptr;
}

} // anonymous namespace

// ─────────────────────────────────────────────────────────────────────────────
// Initialization
// ─────────────────────────────────────────────────────────────────────────────

void MapperUI::initialize(ActionBus* bus, InputMapper* mapper) {
    gsl_Expects(bus != nullptr);
    gsl_Expects(mapper != nullptr);

    bus_    = bus;
    mapper_ = mapper;
    initialized_ = true;
    buildMappingList();
}

void MapperUI::buildMappingList() {
    entries_.clear();
    entries_.reserve(kScancodeNameCount);
    for (size_t i = 0; i < kScancodeNameCount; ++i) {
        MappingEntry entry;
        entry.sdl_scancode = kScancodeNames[i].code;
        entry.label = kScancodeNames[i].name;
        entries_.push_back(std::move(entry));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Open / Close
// ─────────────────────────────────────────────────────────────────────────────

void MapperUI::open() {
    open_ = true;
    state_ = State::Idle;
    selected_index_ = 0;
    scroll_offset_ = 0;
    pending_remaps_.clear();
}

void MapperUI::close() {
    open_ = false;
    state_ = State::Idle;
    pending_remaps_.clear();
}

// ─────────────────────────────────────────────────────────────────────────────
// State Machine
// ─────────────────────────────────────────────────────────────────────────────

void MapperUI::startCapture() {
    if (!open_) return;
    state_ = State::Capturing;
}

void MapperUI::cancelCapture() {
    state_ = State::Idle;
}

void MapperUI::handleCapturedKey(uint16_t scancode) {
    if (state_ != State::Capturing) return;
    if (selected_index_ >= 0 && selected_index_ < static_cast<int>(entries_.size())) {
        addPendingRemap(entries_[static_cast<size_t>(selected_index_)].sdl_scancode, scancode);
    }
    state_ = State::Idle;
}

// ─────────────────────────────────────────────────────────────────────────────
// Key Handling
// ─────────────────────────────────────────────────────────────────────────────

bool MapperUI::handleKey(uint16_t scancode, bool down) {
    if (!open_ || !down) return false;

    constexpr uint16_t kUp    = 0x52;
    constexpr uint16_t kDown  = 0x51;
    constexpr uint16_t kEnter = 0x28;
    constexpr uint16_t kEsc   = 0x29;

    // In capturing mode, Escape cancels; anything else is a captured key
    if (state_ == State::Capturing) {
        if (scancode == kEsc) {
            cancelCapture();
        } else {
            handleCapturedKey(scancode);
        }
        return true;
    }

    // Idle mode navigation
    int count = static_cast<int>(entries_.size());

    switch (scancode) {
        case kUp:
            if (count > 0 && selected_index_ > 0) {
                selected_index_--;
                ensureScrollVisible();
            }
            return true;

        case kDown:
            if (count > 0 && selected_index_ < count - 1) {
                selected_index_++;
                ensureScrollVisible();
            }
            return true;

        case kEnter:
            startCapture();
            return true;

        case kEsc:
            close();
            return true;

        default:
            return true;  // Consume all keys when open
    }
}

void MapperUI::ensureScrollVisible() {
    if (selected_index_ < scroll_offset_) {
        scroll_offset_ = selected_index_;
    }
    if (selected_index_ >= scroll_offset_ + kVisibleRows) {
        scroll_offset_ = selected_index_ - kVisibleRows + 1;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Pending Remaps
// ─────────────────────────────────────────────────────────────────────────────

void MapperUI::addPendingRemap(uint16_t sdl_from, uint16_t sdl_to) {
    // Replace existing pending remap for this key if any
    for (auto& pr : pending_remaps_) {
        if (pr.sdl_from == sdl_from) {
            pr.sdl_to = sdl_to;
            return;
        }
    }
    pending_remaps_.push_back({sdl_from, sdl_to});
}

void MapperUI::commitRemaps() {
    if (!mapper_) return;
    for (const auto& pr : pending_remaps_) {
        mapper_->remap(pr.sdl_from, pr.sdl_to);
    }
    pending_remaps_.clear();
}

void MapperUI::discardRemaps() {
    pending_remaps_.clear();
}

// ─────────────────────────────────────────────────────────────────────────────
// Main Render
// ─────────────────────────────────────────────────────────────────────────────

void MapperUI::render(uint8_t* rgb, uint16_t w, uint16_t h, uint32_t pitch) const {
    if (!open_) return;

    gsl_Expects(rgb != nullptr);

    if (pitch == 0) pitch = static_cast<uint32_t>(w) * 3;
    std::span<uint8_t> buf{rgb, static_cast<size_t>(pitch) * h};

    // Darken full background
    overlay::darkenRect(buf, w, h, pitch, 0, 0, w, h);

    // Panel dimensions
    int panel_x = kPanelMargin;
    int panel_y = kPanelMargin;
    int panel_w = w - kPanelMargin * 2;
    int panel_h = h - kPanelMargin * 2;

    if (panel_w <= 0 || panel_h <= 0) return;

    // Fill panel background (dark blue)
    overlay::fillRect(buf, w, h, pitch,
             panel_x, panel_y, panel_w, panel_h,
             0, 0, 80);

    // Title bar
    std::string title = (state_ == State::Capturing)
        ? " Key Mapper - Press any key... "
        : " Key Mapper ";
    overlay::fillRect(buf, w, h, pitch,
             panel_x, panel_y, panel_w, kTitleH,
             0, 0, 170);
    overlay::drawString(buf, w, h, pitch,
               panel_x + kCharW, panel_y + 4, title,
               255, 255, 255,  // white
               0, 0, 170);     // dark blue

    // Mapping list
    int list_y = panel_y + kTitleH + 4;
    int list_x = panel_x + kCharW;
    int visible = std::min(kVisibleRows, static_cast<int>(entries_.size()) - scroll_offset_);

    for (int i = 0; i < visible; ++i) {
        int entry_idx = scroll_offset_ + i;
        if (entry_idx < 0 || entry_idx >= static_cast<int>(entries_.size())) break;

        const auto& entry = entries_[static_cast<size_t>(entry_idx)];
        bool selected = (entry_idx == selected_index_);

        // Build display string: "KeyName -> AT 0xNN"
        auto at = mapper_ ? mapper_->translate(entry.sdl_scancode) : ATScancode{0, false};

        // Check pending remaps
        const char* remap_name = nullptr;
        for (const auto& pr : pending_remaps_) {
            if (pr.sdl_from == entry.sdl_scancode) {
                remap_name = scancodeName(pr.sdl_to);
                break;
            }
        }

        char line[80];
        if (remap_name) {
            std::snprintf(line, sizeof(line), "%-10s -> %-10s [pending]",
                         entry.label.c_str(), remap_name);
        } else {
            std::snprintf(line, sizeof(line), "%-10s -> AT 0x%02X%s",
                         entry.label.c_str(), at.code, at.extended ? " (E0)" : "");
        }

        int iy = list_y + i * kCharH;
        if (selected) {
            overlay::drawString(buf, w, h, pitch,
                       list_x, iy, line,
                       0, 0, 0,              // black text
                       200, 200, 200);       // light gray bg
        } else {
            overlay::drawString(buf, w, h, pitch,
                       list_x, iy, line,
                       200, 200, 200,        // light gray text
                       0, 0, 80);            // dark blue bg
        }
    }

    // Status bar at bottom of panel
    int status_y = panel_y + panel_h - kCharH - 4;
    std::string status = "Enter=Remap  Esc=Close";
    if (state_ == State::Capturing) {
        status = "Press key to assign, Esc=Cancel";
    }
    overlay::drawString(buf, w, h, pitch,
               list_x, status_y, status,
               170, 170, 170,
               0, 0, 80);
}

} // namespace legends
