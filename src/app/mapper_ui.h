// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MapperUI — interactive key mapper visual overlay.
// Renders a scrollable list of SDL→AT scancode mappings with
// capture mode for reassigning keys.
// @requirement REQ-MAPPER-001

#pragma once

#include <legends/gsl.hpp>

#include <cstdint>
#include <string>
#include <vector>

namespace legends {

class ActionBus;
class InputMapper;

/// @brief Interactive key mapper overlay panel.
///
/// Displays a scrollable list of scancode mappings and allows the user
/// to remap keys through a capture workflow. Rendered directly into the
/// RGB framebuffer using the CP437 bitmap font.
class MapperUI {
public:
    /// State machine for the mapper UI.
    enum class State : uint8_t {
        Idle,       ///< Browsing the mapping list
        Capturing,  ///< Waiting for a key press to assign
    };

    /// @brief Initialize with required dependencies.
    /// @param bus   Action bus for dispatching events (must not be null).
    /// @param mapper Input mapper to read/write remappings (must not be null).
    void initialize(ActionBus* bus, InputMapper* mapper);

    /// @brief Open the mapper overlay.
    void open();

    /// @brief Close the mapper overlay.
    void close();

    /// @brief Check if the mapper is currently open.
    bool isOpen() const { return open_; }

    /// @brief Get the current state machine state.
    /// @return Current state (Idle or Capturing).
    State state() const { return state_; }

    /// @brief Begin capturing a key for the selected mapping entry.
    void startCapture();

    /// @brief Cancel the active capture, returning to Idle.
    void cancelCapture();

    /// @brief Handle a captured key press during capture mode.
    /// @param scancode SDL3 scancode of the pressed key.
    void handleCapturedKey(uint16_t scancode);

    /// @brief Handle a key event. Returns true if consumed.
    /// @param scancode SDL3 scancode.
    /// @param down     True for key-down, false for key-up.
    bool handleKey(uint16_t scancode, bool down);

    /// @brief Get the currently selected list index.
    int selectedIndex() const { return selected_index_; }

    /// @brief Get the current scroll offset.
    int scrollOffset() const { return scroll_offset_; }

    /// @brief Render the mapper overlay into an RGB24 buffer.
    /// @param rgb   Destination RGB24 pixel buffer (must not be null when open).
    /// @param w     Buffer width in pixels.
    /// @param h     Buffer height in pixels.
    /// @param pitch Row stride in bytes (0 = w * 3).
    void render(uint8_t* rgb, uint16_t w, uint16_t h, uint32_t pitch = 0) const;

    /// @brief Add a pending remap (not yet committed to the mapper).
    /// @param sdl_from Source SDL scancode.
    /// @param sdl_to   Target SDL scancode.
    void addPendingRemap(uint16_t sdl_from, uint16_t sdl_to);

    /// @brief Commit all pending remaps to the real InputMapper.
    void commitRemaps();

    /// @brief Discard all pending remaps without applying.
    void discardRemaps();

private:
    // ─────────────────────────────────────────────────────────────────────
    // Rendering helpers (match MenuSystem patterns)
    // ─────────────────────────────────────────────────────────────────────

    void drawChar(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
                  int x, int y, uint8_t ch,
                  uint8_t fr, uint8_t fg, uint8_t fb,
                  uint8_t br, uint8_t bg, uint8_t bb) const;
    void drawString(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
                    int x, int y, const std::string& text,
                    uint8_t fr, uint8_t fg, uint8_t fb,
                    uint8_t br, uint8_t bg, uint8_t bb) const;
    void darkenRect(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
                    int x, int y, int w, int h) const;
    void fillRect(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h, uint32_t pitch,
                  int x, int y, int w, int h,
                  uint8_t r, uint8_t g, uint8_t b) const;

    // ─────────────────────────────────────────────────────────────────────
    // Data
    // ─────────────────────────────────────────────────────────────────────

    /// Entry in the mapping list shown to the user.
    struct MappingEntry {
        uint16_t    sdl_scancode;
        std::string label;  // Human-readable name
    };

    void buildMappingList();
    void ensureScrollVisible();

    ActionBus*   bus_    = nullptr;
    InputMapper* mapper_ = nullptr;
    bool         open_   = false;
    State        state_  = State::Idle;
    bool         initialized_ = false;

    int          selected_index_ = 0;
    int          scroll_offset_  = 0;

    std::vector<MappingEntry> entries_;

    /// Pending remaps: sdl_from → sdl_to
    struct PendingRemap {
        uint16_t sdl_from;
        uint16_t sdl_to;
    };
    std::vector<PendingRemap> pending_remaps_;

    // Layout constants
    static constexpr int kCharW       = 8;
    static constexpr int kCharH       = 16;
    static constexpr int kPanelMargin = 40;   // pixels from edge
    static constexpr int kTitleH      = kCharH + 8;
    static constexpr int kVisibleRows = 20;
};

} // namespace legends
