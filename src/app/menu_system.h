// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MenuSystem — overlay menu rendered directly into the RGB framebuffer.
// Uses an embedded CP437 8x16 bitmap font for text rendering.
// Keyboard and mouse navigation, pause-on-open.

#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace legends {

class ActionBus;

struct MenuItem {
    std::string label;
    int action_id;     // Cast to Action enum
    int param;         // Action parameter (e.g., save slot)
    bool separator;    // True = horizontal rule, label ignored

    MenuItem() : action_id(-1), param(0), separator(true) {}
    MenuItem(std::string lbl, int act, int p = 0)
        : label(std::move(lbl)), action_id(act), param(p), separator(false) {}

    [[nodiscard]] static MenuItem Separator() { return MenuItem{}; }
};

struct Menu {
    std::string title;
    std::vector<MenuItem> items;
};

class MenuSystem {
public:
    void initialize(ActionBus* bus);

    void open();
    void close();
    [[nodiscard]] bool isOpen() const { return open_; }

    /// Handle a key press. Returns true if consumed.
    [[nodiscard]] bool handleKey(uint16_t scancode, bool down);

    /// Handle a mouse click. Returns true if consumed.
    [[nodiscard]] bool handleMouseClick(int32_t x, int32_t y);

    /// Render the menu overlay into an RGB24 buffer.
    /// pitch = row stride in bytes. 0 means width * 3 (tightly packed RGB24).
    void render(uint8_t* rgb_buffer, uint16_t width, uint16_t height,
                uint32_t pitch = 0);

    // ── Bar Mode (REQ-MENU-001) ─────────────────────────────────────────

    /// Check if the persistent menu bar is visible (hidden in fullscreen).
    [[nodiscard]] bool isBarVisible() const { return !fullscreen_; }

    /// Set fullscreen state (hides/shows the persistent bar).
    void setFullscreen(bool fs) { fullscreen_ = fs; }

    /// Check if a dropdown panel is currently open (bar mode).
    [[nodiscard]] bool isDropdownOpen() const { return dropdown_open_; }

    /// Get the currently selected menu index.
    [[nodiscard]] int selectedMenuIndex() const { return selected_menu_; }

    /// Handle a mouse click in bar mode (called even when overlay is not open).
    /// Returns true if consumed.
    [[nodiscard]] bool handleBarClick(int32_t x, int32_t y);

    /// Render the persistent menu bar (no full-screen darken).
    /// pitch = row stride in bytes. 0 means width * 3.
    void renderBar(uint8_t* rgb_buffer, uint16_t width, uint16_t height,
                   uint32_t pitch = 0);

private:
    void buildMenus();
    void activateItem();

    ActionBus* bus_ = nullptr;
    bool open_ = false;
    bool fullscreen_ = false;
    bool dropdown_open_ = false;
    int selected_menu_ = 0;
    int selected_item_ = -1;
    std::vector<Menu> menus_;

    // Layout computed on render
    static constexpr int kCharW = 8;
    static constexpr int kCharH = 16;
    static constexpr int kMenuBarH = kCharH + 4;  // pixels
    static constexpr int kItemPadX = 2;            // chars of padding
};

} // namespace legends
