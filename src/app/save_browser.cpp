// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// SaveBrowser — visual save slot browser implementation.
// REQ-SAVE-003: Save slot visual browser

#include "app/save_browser.h"
#include "app/action_bus.h"
#include "app/save_manager.h"
#include "app/overlay_render.h"

#include <algorithm>
#include <cstring>
#include <span>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// Initialization
// ─────────────────────────────────────────────────────────────────────────────

void SaveBrowser::initialize(ActionBus* bus, SaveManager* mgr) {
    gsl_Expects(bus != nullptr);
    gsl_Expects(mgr != nullptr);

    bus_      = bus;
    save_mgr_ = mgr;
    initialized_ = true;
}

// ─────────────────────────────────────────────────────────────────────────────
// Open / Close
// ─────────────────────────────────────────────────────────────────────────────

void SaveBrowser::openForSave() {
    open_ = true;
    mode_ = Mode::Save;
    selected_row_ = 0;
    selected_col_ = 0;
    refreshSlotCache();
}

void SaveBrowser::openForLoad() {
    open_ = true;
    mode_ = Mode::Load;
    selected_row_ = 0;
    selected_col_ = 0;
    refreshSlotCache();
}

void SaveBrowser::close() {
    open_ = false;
}

SaveBrowser::Mode SaveBrowser::mode() const {
    gsl_Expects(open_);
    return mode_;
}

int SaveBrowser::selectedSlot() const {
    gsl_Expects(open_);
    return selected_row_ * kCols + selected_col_ + 1;  // 1-based
}

// ─────────────────────────────────────────────────────────────────────────────
// Slot Cache
// ─────────────────────────────────────────────────────────────────────────────

void SaveBrowser::refreshSlotCache() {
    for (int i = 0; i < kTotalSlots; ++i) {
        int slot = i + 1;
        slots_[i].occupied = save_mgr_ ? save_mgr_->isSlotOccupied(slot) : false;

        if (slots_[i].occupied) {
            // Mark as saved — file timestamp conversion varies by platform
            slots_[i].timestamp = "Saved";
        } else {
            slots_[i].timestamp = "Empty";
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Key Handling
// ─────────────────────────────────────────────────────────────────────────────

bool SaveBrowser::handleKey(uint16_t scancode, bool down) {
    if (!open_ || !down) return false;

    constexpr uint16_t kUp    = 0x52;
    constexpr uint16_t kDown  = 0x51;
    constexpr uint16_t kLeft  = 0x50;
    constexpr uint16_t kRight = 0x4F;
    constexpr uint16_t kEnter = 0x28;
    constexpr uint16_t kEsc   = 0x29;

    switch (scancode) {
        case kUp:
            selected_row_--;
            if (selected_row_ < 0) selected_row_ = kRows - 1;
            return true;

        case kDown:
            selected_row_++;
            if (selected_row_ >= kRows) selected_row_ = 0;
            return true;

        case kLeft:
            selected_col_--;
            if (selected_col_ < 0) selected_col_ = kCols - 1;
            return true;

        case kRight:
            selected_col_++;
            if (selected_col_ >= kCols) selected_col_ = 0;
            return true;

        case kEnter: {
            int slot = selectedSlot();
            if (bus_) {
                if (mode_ == Mode::Save) {
                    bus_->dispatch(Action::SaveState, slot);
                } else {
                    bus_->dispatch(Action::LoadState, slot);
                }
            }
            close();
            return true;
        }

        case kEsc:
            close();
            return true;

        default:
            return true;  // Consume all keys when open
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Mouse Click
// ─────────────────────────────────────────────────────────────────────────────

bool SaveBrowser::handleMouseClick(int32_t /*x*/, int32_t /*y*/) {
    if (!open_) return false;

    // TODO: Map click coordinates to grid cell for direct slot selection
    close();
    return true;
}

// ─────────────────────────────────────────────────────────────────────────────
// Main Render
// ─────────────────────────────────────────────────────────────────────────────

void SaveBrowser::render(uint8_t* rgb, uint16_t w, uint16_t h, uint32_t pitch) const {
    if (!open_) return;

    gsl_Expects(rgb != nullptr);

    if (pitch == 0) pitch = static_cast<uint32_t>(w) * 3;
    std::span<uint8_t> buf{rgb, static_cast<size_t>(pitch) * h};

    // Darken full background
    overlay::darkenRect(buf, w, h, pitch, 0, 0, w, h);

    // Grid dimensions
    int grid_w = kCols * kCellW + (kCols - 1) * kCellPad;
    int grid_h = kRows * kCellH + (kRows - 1) * kCellPad;

    // Center the grid
    int grid_x = (w - grid_w) / 2;
    int grid_y = (h - grid_h) / 2 + kTitleH;

    // Title
    std::string title = (mode_ == Mode::Save) ? "Save State" : "Load State";
    int title_x = (w - static_cast<int>(title.size()) * kCharW) / 2;
    int title_y = grid_y - kTitleH;
    overlay::drawString(buf, w, h, pitch,
               title_x, title_y, title,
               255, 255, 255,
               0, 0, 0);

    // Draw cells
    for (int row = 0; row < kRows; ++row) {
        for (int col = 0; col < kCols; ++col) {
            int slot_idx = row * kCols + col;
            int cell_x = grid_x + col * (kCellW + kCellPad);
            int cell_y = grid_y + row * (kCellH + kCellPad);

            bool selected = (row == selected_row_ && col == selected_col_);
            const auto& slot = slots_[slot_idx];

            // Cell background
            if (selected) {
                overlay::fillRect(buf, w, h, pitch,
                         cell_x, cell_y, kCellW, kCellH,
                         60, 60, 120);  // highlighted
                // Selection border (1px white)
                overlay::fillRect(buf, w, h, pitch,
                         cell_x, cell_y, kCellW, 1, 255, 255, 255);
                overlay::fillRect(buf, w, h, pitch,
                         cell_x, cell_y + kCellH - 1, kCellW, 1, 255, 255, 255);
                overlay::fillRect(buf, w, h, pitch,
                         cell_x, cell_y, 1, kCellH, 255, 255, 255);
                overlay::fillRect(buf, w, h, pitch,
                         cell_x + kCellW - 1, cell_y, 1, kCellH, 255, 255, 255);
            } else {
                overlay::fillRect(buf, w, h, pitch,
                         cell_x, cell_y, kCellW, kCellH,
                         30, 30, 60);   // normal
            }

            // Slot number
            char slot_num[8];
            std::snprintf(slot_num, sizeof(slot_num), "Slot %d", slot_idx + 1);
            int text_x = cell_x + (kCellW - static_cast<int>(std::strlen(slot_num)) * kCharW) / 2;
            int text_y = cell_y + kCellH / 2 - kCharH;
            overlay::drawString(buf, w, h, pitch,
                       text_x, text_y, slot_num,
                       255, 255, 255,
                       selected ? static_cast<uint8_t>(60) : static_cast<uint8_t>(30),
                       selected ? static_cast<uint8_t>(60) : static_cast<uint8_t>(30),
                       selected ? static_cast<uint8_t>(120) : static_cast<uint8_t>(60));

            // Status / timestamp
            const std::string& status = slot.timestamp;
            int st_x = cell_x + (kCellW - static_cast<int>(status.size()) * kCharW) / 2;
            int st_y = text_y + kCharH + 4;
            overlay::drawString(buf, w, h, pitch,
                       st_x, st_y, status,
                       slot.occupied ? static_cast<uint8_t>(170) : static_cast<uint8_t>(100),
                       slot.occupied ? static_cast<uint8_t>(170) : static_cast<uint8_t>(100),
                       slot.occupied ? static_cast<uint8_t>(170) : static_cast<uint8_t>(100),
                       selected ? static_cast<uint8_t>(60) : static_cast<uint8_t>(30),
                       selected ? static_cast<uint8_t>(60) : static_cast<uint8_t>(30),
                       selected ? static_cast<uint8_t>(120) : static_cast<uint8_t>(60));
        }
    }

    // Footer help text
    std::string footer = "Arrow keys=Navigate  Enter=Select  Esc=Cancel";
    int footer_x = (w - static_cast<int>(footer.size()) * kCharW) / 2;
    int footer_y = grid_y + grid_h + 8;
    overlay::drawString(buf, w, h, pitch,
               footer_x, footer_y, footer,
               170, 170, 170,
               0, 0, 0);
}

} // namespace legends
