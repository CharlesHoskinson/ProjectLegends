// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// SaveBrowser — visual save slot browser with 3x3 grid layout.
// Displays thumbnails and timestamps for occupied save slots.
// @requirement REQ-SAVE-003

#pragma once

#include <legends/gsl.hpp>

#include <cstdint>
#include <string>
#include <vector>

namespace legends {

class ActionBus;
class SaveManager;

/// @brief Visual save slot browser overlay.
///
/// Displays a 3x3 grid of save slots with thumbnails and metadata.
/// Supports both Save and Load modes, dispatching appropriate actions
/// through the ActionBus when a slot is selected.
class SaveBrowser {
public:
    /// Browser mode: saving or loading.
    enum class Mode : uint8_t {
        Save,
        Load,
    };

    /// Grid dimensions.
    static constexpr int kRows       = 3;
    static constexpr int kCols       = 3;
    static constexpr int kTotalSlots = kRows * kCols;  // 9 slots

    /// @brief Initialize with required dependencies.
    /// @param bus Action bus for dispatching save/load actions (must not be null).
    /// @param mgr Save manager for querying slot state (must not be null).
    void initialize(ActionBus* bus, SaveManager* mgr);

    /// @brief Open the browser in save mode.
    void openForSave();

    /// @brief Open the browser in load mode.
    void openForLoad();

    /// @brief Close the browser.
    void close();

    /// @brief Check if the browser is currently open.
    [[nodiscard]] bool isOpen() const { return open_; }

    /// @brief Get the current mode (Save or Load).
    /// @pre isOpen() must be true.
    [[nodiscard]] Mode mode() const;

    /// @brief Get the currently selected slot number (1-based).
    /// @pre isOpen() must be true.
    [[nodiscard]] int selectedSlot() const;

    /// @brief Handle a key event. Returns true if consumed.
    /// @param scancode SDL3 scancode.
    /// @param down     True for key-down, false for key-up.
    [[nodiscard]] bool handleKey(uint16_t scancode, bool down);

    /// @brief Handle a mouse click. Returns true if consumed.
    /// @param x Mouse X coordinate in pixels.
    /// @param y Mouse Y coordinate in pixels.
    [[nodiscard]] bool handleMouseClick(int32_t x, int32_t y);

    /// @brief Render the browser overlay into an RGB24 buffer.
    /// @param rgb   Destination RGB24 pixel buffer (must not be null when open).
    /// @param w     Buffer width in pixels.
    /// @param h     Buffer height in pixels.
    /// @param pitch Row stride in bytes (0 = w * 3).
    void render(uint8_t* rgb, uint16_t w, uint16_t h, uint32_t pitch = 0) const;

private:
    // ─────────────────────────────────────────────────────────────────────
    // Slot cache
    // ─────────────────────────────────────────────────────────────────────

    struct SlotCache {
        bool        occupied = false;
        std::string timestamp;  // Human-readable timestamp or "Empty"
    };

    void refreshSlotCache();

    // ─────────────────────────────────────────────────────────────────────
    // Data
    // ─────────────────────────────────────────────────────────────────────

    ActionBus*   bus_         = nullptr;
    SaveManager* save_mgr_    = nullptr;
    bool         open_        = false;
    bool         initialized_ = false;
    Mode         mode_        = Mode::Save;

    int          selected_row_ = 0;
    int          selected_col_ = 0;

    SlotCache    slots_[kTotalSlots] = {};

    // Layout constants
    static constexpr int kCharW      = 8;
    static constexpr int kCharH      = 16;
    static constexpr int kCellW      = 160;  // pixels per cell
    static constexpr int kCellH      = 120;  // pixels per cell
    static constexpr int kCellPad    = 8;    // padding between cells
    static constexpr int kTitleH     = kCharH + 8;
};

} // namespace legends
