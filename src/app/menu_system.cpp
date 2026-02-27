// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MenuSystem — overlay rendering, keyboard/mouse navigation.

#include "app/menu_system.h"
#include "app/action_bus.h"
#include "legends/internal/cp437_font_8x16.h"

#include <algorithm>
#include <cstring>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// Initialization
// ─────────────────────────────────────────────────────────────────────────────

void MenuSystem::initialize(ActionBus* bus) {
    bus_ = bus;
    buildMenus();
}

void MenuSystem::buildMenus() {
    menus_.clear();

    // Main
    {
        Menu m;
        m.title = "Main";
        m.items.emplace_back("Pause/Resume", static_cast<int>(Action::TogglePause));
        m.items.emplace_back("Reset", static_cast<int>(Action::Reset));
        m.items.push_back(MenuItem::Separator());
        m.items.emplace_back("Quit", static_cast<int>(Action::Quit));
        menus_.push_back(std::move(m));
    }

    // CPU
    {
        Menu m;
        m.title = "CPU";
        m.items.emplace_back("PC-98 Mode", static_cast<int>(Action::SetMachinePC98));
        menus_.push_back(std::move(m));
    }

    // Video
    {
        Menu m;
        m.title = "Video";
        m.items.emplace_back("Toggle Fullscreen", static_cast<int>(Action::ToggleFullscreen));
        m.items.push_back(MenuItem::Separator());
        m.items.emplace_back("Toggle Shaders", static_cast<int>(Action::ToggleShaders));
        m.items.emplace_back("Next Shader", static_cast<int>(Action::NextShader));
        m.items.emplace_back("Previous Shader", static_cast<int>(Action::PrevShader));
        m.items.emplace_back("Load Custom .glsl", static_cast<int>(Action::LoadCustomShader));
        m.items.push_back(MenuItem::Separator());
        m.items.emplace_back("TTF Font Mode", static_cast<int>(Action::ToggleTTFMode));
        m.items.push_back(MenuItem::Separator());
        m.items.emplace_back("3dfx Glide Emulation", static_cast<int>(Action::ToggleGlide));
        menus_.push_back(std::move(m));
    }

    // Sound
    {
        Menu m;
        m.title = "Sound";
        m.items.emplace_back("Volume Up", static_cast<int>(Action::VolumeUp));
        m.items.emplace_back("Volume Down", static_cast<int>(Action::VolumeDown));
        m.items.emplace_back("Mute/Unmute", static_cast<int>(Action::ToggleMute));
        m.items.push_back(MenuItem::Separator());
        m.items.emplace_back("MIDI Device", static_cast<int>(Action::SetMIDIDevice));
        menus_.push_back(std::move(m));
    }

    // DOS
    {
        Menu m;
        m.title = "DOS";
        m.items.emplace_back("Mount Directory...", static_cast<int>(Action::MountDrive), 0);
        m.items.emplace_back("Mount Image...", static_cast<int>(Action::MountDrive), 1);
        m.items.push_back(MenuItem::Separator());
        m.items.emplace_back("Unmount Drive...", static_cast<int>(Action::UnmountDrive));
        menus_.push_back(std::move(m));
    }

    // Network
    {
        Menu m;
        m.title = "Network";
        m.items.emplace_back("IPX Connect", static_cast<int>(Action::IPXConnect));
        m.items.emplace_back("IPX Disconnect", static_cast<int>(Action::IPXDisconnect));
        menus_.push_back(std::move(m));
    }

    // Save
    {
        Menu m;
        m.title = "Save";
        m.items.emplace_back("Save Slot Browser...", static_cast<int>(Action::OpenSaveBrowser), 0);
        m.items.emplace_back("Load Slot Browser...", static_cast<int>(Action::OpenSaveBrowser), 1);
        m.items.push_back(MenuItem::Separator());
        for (int i = 1; i <= 9; ++i) {
            m.items.emplace_back("Save Slot " + std::to_string(i),
                                 static_cast<int>(Action::SaveState), i);
        }
        m.items.push_back(MenuItem::Separator());
        for (int i = 1; i <= 9; ++i) {
            m.items.emplace_back("Load Slot " + std::to_string(i),
                                 static_cast<int>(Action::LoadState), i);
        }
        menus_.push_back(std::move(m));
    }

    // Capture
    {
        Menu m;
        m.title = "Capture";
        m.items.emplace_back("Screenshot", static_cast<int>(Action::Screenshot));
        m.items.emplace_back("Start/Stop Video Recording", static_cast<int>(Action::ToggleVideoCapture));
        m.items.push_back(MenuItem::Separator());
        m.items.emplace_back("Printer Output", static_cast<int>(Action::TogglePrinter));
        menus_.push_back(std::move(m));
    }

    // Tools
    {
        Menu m;
        m.title = "Tools";
        m.items.emplace_back("AI Assistant", static_cast<int>(Action::ToggleAIPanel));
        menus_.push_back(std::move(m));
    }

    // Input
    {
        Menu m;
        m.title = "Input";
        m.items.emplace_back("Key Mapper", static_cast<int>(Action::OpenMapper));
        m.items.emplace_back("Paste Clipboard", static_cast<int>(Action::ClipboardPaste));
        menus_.push_back(std::move(m));
    }

    // Help
    {
        Menu m;
        m.title = "Help";
        m.items.emplace_back("About Project Legends", -1);
        menus_.push_back(std::move(m));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Open / Close
// ─────────────────────────────────────────────────────────────────────────────

void MenuSystem::open() {
    open_ = true;
    selected_menu_ = 0;
    selected_item_ = 0;
}

void MenuSystem::close() {
    open_ = false;
    selected_item_ = -1;
}

// ─────────────────────────────────────────────────────────────────────────────
// Keyboard navigation
// ─────────────────────────────────────────────────────────────────────────────

bool MenuSystem::handleKey(uint16_t scancode, bool down) {
    if (!open_ || !down) return false;

    // SDL3 scancodes for navigation
    constexpr uint16_t kUp    = 0x52;
    constexpr uint16_t kDown  = 0x51;
    constexpr uint16_t kLeft  = 0x50;
    constexpr uint16_t kRight = 0x4F;
    constexpr uint16_t kEnter = 0x28;
    constexpr uint16_t kEsc   = 0x29;
    constexpr uint16_t kF12   = 0x45;

    if (menus_.empty()) return false;

    const auto& menu = menus_[static_cast<size_t>(selected_menu_)];
    int item_count = static_cast<int>(menu.items.size());

    switch (scancode) {
        case kUp:
            if (item_count > 0) {
                int start = selected_item_;
                do {
                    selected_item_--;
                    if (selected_item_ < 0) selected_item_ = item_count - 1;
                } while (menu.items[static_cast<size_t>(selected_item_)].separator &&
                         selected_item_ != start);
            }
            return true;

        case kDown:
            if (item_count > 0) {
                int start = selected_item_;
                do {
                    selected_item_++;
                    if (selected_item_ >= item_count) selected_item_ = 0;
                } while (menu.items[static_cast<size_t>(selected_item_)].separator &&
                         selected_item_ != start);
            }
            return true;

        case kLeft:
            selected_menu_--;
            if (selected_menu_ < 0) selected_menu_ = static_cast<int>(menus_.size()) - 1;
            selected_item_ = 0;
            return true;

        case kRight:
            selected_menu_++;
            if (selected_menu_ >= static_cast<int>(menus_.size())) selected_menu_ = 0;
            selected_item_ = 0;
            return true;

        case kEnter:
            activateItem();
            return true;

        case kEsc:
        case kF12:
            close();
            return true;

        default:
            return false;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Mouse click
// ─────────────────────────────────────────────────────────────────────────────

bool MenuSystem::handleMouseClick(int32_t x, int32_t y) {
    if (!open_) return false;

    // Check menu bar clicks
    if (y < kMenuBarH) {
        int cx = 0;
        for (size_t i = 0; i < menus_.size(); ++i) {
            int title_w = static_cast<int>(menus_[i].title.size() + 2) * kCharW;
            if (x >= cx && x < cx + title_w) {
                selected_menu_ = static_cast<int>(i);
                selected_item_ = 0;
                return true;
            }
            cx += title_w;
        }
        return true;
    }

    // Check dropdown item clicks
    // Compute dropdown position
    int drop_x = 0;
    for (int i = 0; i < selected_menu_; ++i) {
        drop_x += static_cast<int>(menus_[static_cast<size_t>(i)].title.size() + 2) * kCharW;
    }

    const auto& menu = menus_[static_cast<size_t>(selected_menu_)];
    int drop_y = kMenuBarH;
    for (size_t i = 0; i < menu.items.size(); ++i) {
        int item_h = kCharH;
        if (menu.items[i].separator) item_h = 4;
        if (y >= drop_y && y < drop_y + item_h) {
            if (!menu.items[i].separator) {
                selected_item_ = static_cast<int>(i);
                activateItem();
            }
            return true;
        }
        drop_y += item_h;
    }

    // Click outside — close
    close();
    return true;
}

// ─────────────────────────────────────────────────────────────────────────────
// Activate selected item
// ─────────────────────────────────────────────────────────────────────────────

void MenuSystem::activateItem() {
    if (!bus_ || menus_.empty()) return;
    if (selected_menu_ < 0 || selected_menu_ >= static_cast<int>(menus_.size())) return;

    const auto& menu = menus_[static_cast<size_t>(selected_menu_)];
    if (selected_item_ < 0 || selected_item_ >= static_cast<int>(menu.items.size())) return;

    const auto& item = menu.items[static_cast<size_t>(selected_item_)];
    if (item.separator || item.action_id < 0) return;

    close(); // Close menu before dispatching
    bus_->dispatch(static_cast<Action>(item.action_id), item.param);
}

// ─────────────────────────────────────────────────────────────────────────────
// Bar Mode (REQ-MENU-001)
// ─────────────────────────────────────────────────────────────────────────────

bool MenuSystem::handleBarClick(int32_t x, int32_t y) {
    if (menus_.empty()) return false;

    // If dropdown is open, check dropdown item clicks first
    if (dropdown_open_) {
        // Check if click is in the dropdown panel
        int drop_x = 0;
        for (int i = 0; i < selected_menu_; ++i) {
            drop_x += static_cast<int>(menus_[static_cast<size_t>(i)].title.size() + 2) * kCharW;
        }

        const auto& menu = menus_[static_cast<size_t>(selected_menu_)];
        int drop_y = kMenuBarH;

        // Compute dropdown dimensions
        int max_label = 0;
        for (const auto& item : menu.items) {
            if (!item.separator) {
                int len = static_cast<int>(item.label.size());
                if (len > max_label) max_label = len;
            }
        }
        int drop_w = (max_label + kItemPadX * 2) * kCharW;
        if (drop_w < 80) drop_w = 80;

        int drop_h = 0;
        for (const auto& item : menu.items) {
            drop_h += item.separator ? 4 : kCharH;
        }

        // Check click in dropdown area
        if (x >= drop_x && x < drop_x + drop_w &&
            y >= drop_y && y < drop_y + drop_h) {
            // Find which item was clicked
            int item_y = drop_y;
            for (size_t i = 0; i < menu.items.size(); ++i) {
                int item_h = menu.items[i].separator ? 4 : kCharH;
                if (y >= item_y && y < item_y + item_h) {
                    if (!menu.items[i].separator) {
                        selected_item_ = static_cast<int>(i);
                        activateItem();
                        dropdown_open_ = false;
                    }
                    return true;
                }
                item_y += item_h;
            }
        }
    }

    // Check if click is in the menu bar area
    if (y < kMenuBarH) {
        int cx = 0;
        for (size_t i = 0; i < menus_.size(); ++i) {
            int title_w = static_cast<int>(menus_[i].title.size() + 2) * kCharW;
            if (x >= cx && x < cx + title_w) {
                selected_menu_ = static_cast<int>(i);
                selected_item_ = 0;
                dropdown_open_ = true;
                return true;
            }
            cx += title_w;
        }
        return true;
    }

    // Click outside bar and dropdown — close dropdown
    dropdown_open_ = false;
    return false;
}

void MenuSystem::renderBar(uint8_t* rgb_buffer, uint16_t width, uint16_t height,
                            uint32_t pitch) {
    if (menus_.empty() || width == 0 || height == 0) return;

    if (pitch == 0) pitch = static_cast<uint32_t>(width) * 3;

    // Fill menu bar background (dark blue)
    for (int py = 0; py < kMenuBarH && py < height; ++py) {
        for (int px = 0; px < width; ++px) {
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb_buffer[idx]     = 0;
            rgb_buffer[idx + 1] = 0;
            rgb_buffer[idx + 2] = 170; // dark blue
        }
    }

    // Draw menu titles
    int title_x = 0;
    for (size_t i = 0; i < menus_.size(); ++i) {
        bool selected = dropdown_open_ && (static_cast<int>(i) == selected_menu_);
        std::string label = " " + menus_[i].title + " ";
        if (selected) {
            drawString(rgb_buffer, width, height, pitch,
                       title_x, 2, label,
                       0, 0, 170,        // fg: dark blue
                       255, 255, 255);   // bg: white (inverted)
        } else {
            drawString(rgb_buffer, width, height, pitch,
                       title_x, 2, label,
                       255, 255, 255,    // fg: white
                       0, 0, 170);       // bg: dark blue
        }
        title_x += static_cast<int>(label.size()) * kCharW;
    }

    // If dropdown is open, render it (no full-screen darken)
    if (!dropdown_open_) return;
    if (selected_menu_ < 0 || selected_menu_ >= static_cast<int>(menus_.size())) return;

    const auto& menu = menus_[static_cast<size_t>(selected_menu_)];

    int drop_x = 0;
    for (int i = 0; i < selected_menu_; ++i) {
        drop_x += static_cast<int>(menus_[static_cast<size_t>(i)].title.size() + 2) * kCharW;
    }

    int max_label = 0;
    for (const auto& item : menu.items) {
        if (!item.separator) {
            int len = static_cast<int>(item.label.size());
            if (len > max_label) max_label = len;
        }
    }
    int drop_w = (max_label + kItemPadX * 2) * kCharW;
    if (drop_w < 80) drop_w = 80;

    int drop_h = 0;
    for (const auto& item : menu.items) {
        drop_h += item.separator ? 4 : kCharH;
    }

    int drop_y = kMenuBarH;
    if (drop_x + drop_w > width) drop_x = width - drop_w;
    if (drop_x < 0) drop_x = 0;

    // Fill dropdown background (black)
    for (int py = drop_y; py < drop_y + drop_h && py < height; ++py) {
        for (int px = drop_x; px < drop_x + drop_w && px < width; ++px) {
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb_buffer[idx]     = 0;
            rgb_buffer[idx + 1] = 0;
            rgb_buffer[idx + 2] = 0;
        }
    }

    // Draw items
    int item_y = drop_y;
    for (size_t i = 0; i < menu.items.size(); ++i) {
        const auto& item = menu.items[i];

        if (item.separator) {
            int line_y = item_y + 2;
            if (line_y >= 0 && line_y < height) {
                for (int px = drop_x + 4; px < drop_x + drop_w - 4 && px < width; ++px) {
                    if (px < 0) continue;
                    size_t idx = static_cast<size_t>(line_y) * pitch + static_cast<size_t>(px) * 3;
                    rgb_buffer[idx]     = 128;
                    rgb_buffer[idx + 1] = 128;
                    rgb_buffer[idx + 2] = 128;
                }
            }
            item_y += 4;
            continue;
        }

        bool highlighted = (static_cast<int>(i) == selected_item_);
        std::string padded = std::string(kItemPadX, ' ') + item.label;
        while (static_cast<int>(padded.size()) * kCharW < drop_w) {
            padded += ' ';
        }

        if (highlighted) {
            drawString(rgb_buffer, width, height, pitch,
                       drop_x, item_y, padded,
                       0, 0, 0,              // fg: black
                       200, 200, 200);       // bg: light gray
        } else {
            bool disabled = (item.action_id < 0);
            drawString(rgb_buffer, width, height, pitch,
                       drop_x, item_y, padded,
                       disabled ? static_cast<uint8_t>(128) : static_cast<uint8_t>(255),
                       disabled ? static_cast<uint8_t>(128) : static_cast<uint8_t>(255),
                       disabled ? static_cast<uint8_t>(128) : static_cast<uint8_t>(255),
                       0, 0, 0);             // bg: black
        }

        item_y += kCharH;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering
// ─────────────────────────────────────────────────────────────────────────────

void MenuSystem::darkenRect(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h,
                            uint32_t pitch,
                            int x, int y, int w, int h) const {
    for (int py = y; py < y + h && py < buf_h; ++py) {
        if (py < 0) continue;
        for (int px = x; px < x + w && px < buf_w; ++px) {
            if (px < 0) continue;
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb[idx]     = static_cast<uint8_t>(rgb[idx] / 3);
            rgb[idx + 1] = static_cast<uint8_t>(rgb[idx + 1] / 3);
            rgb[idx + 2] = static_cast<uint8_t>(rgb[idx + 2] / 3);
        }
    }
}

void MenuSystem::drawChar(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h,
                          uint32_t pitch,
                          int x, int y, uint8_t ch,
                          uint8_t fr, uint8_t fg, uint8_t fb,
                          uint8_t br, uint8_t bg, uint8_t bb) const {
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

void MenuSystem::drawString(uint8_t* rgb, uint16_t buf_w, uint16_t buf_h,
                            uint32_t pitch,
                            int x, int y, const std::string& text,
                            uint8_t fr, uint8_t fg, uint8_t fb,
                            uint8_t br, uint8_t bg, uint8_t bb) const {
    for (size_t i = 0; i < text.size(); ++i) {
        drawChar(rgb, buf_w, buf_h, pitch,
                 x + static_cast<int>(i) * kCharW, y,
                 static_cast<uint8_t>(text[i]),
                 fr, fg, fb, br, bg, bb);
    }
}

void MenuSystem::render(uint8_t* rgb_buffer, uint16_t width, uint16_t height,
                        uint32_t pitch) {
    if (!open_ || menus_.empty()) return;

    // Default pitch = tightly packed RGB24
    if (pitch == 0) pitch = static_cast<uint32_t>(width) * 3;

    // Semi-transparent darkened background
    darkenRect(rgb_buffer, width, height, pitch, 0, 0, width, height);

    // ── Menu bar ────────────────────────────────────────────────────────
    // Fill menu bar background
    for (int py = 0; py < kMenuBarH && py < height; ++py) {
        for (int px = 0; px < width; ++px) {
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb_buffer[idx]     = 0;
            rgb_buffer[idx + 1] = 0;
            rgb_buffer[idx + 2] = 170; // dark blue
        }
    }

    // Draw menu titles
    int title_x = 0;
    for (size_t i = 0; i < menus_.size(); ++i) {
        bool selected = (static_cast<int>(i) == selected_menu_);
        std::string label = " " + menus_[i].title + " ";
        if (selected) {
            drawString(rgb_buffer, width, height, pitch,
                       title_x, 2, label,
                       0, 0, 170,        // fg: dark blue
                       255, 255, 255);   // bg: white (inverted)
        } else {
            drawString(rgb_buffer, width, height, pitch,
                       title_x, 2, label,
                       255, 255, 255,    // fg: white
                       0, 0, 170);       // bg: dark blue
        }
        title_x += static_cast<int>(label.size()) * kCharW;
    }

    // ── Dropdown panel ──────────────────────────────────────────────────
    if (selected_menu_ < 0 || selected_menu_ >= static_cast<int>(menus_.size())) return;

    const auto& menu = menus_[static_cast<size_t>(selected_menu_)];

    // Compute dropdown X position
    int drop_x = 0;
    for (int i = 0; i < selected_menu_; ++i) {
        drop_x += static_cast<int>(menus_[static_cast<size_t>(i)].title.size() + 2) * kCharW;
    }

    // Compute dropdown width (widest item + padding)
    int max_label = 0;
    for (const auto& item : menu.items) {
        if (!item.separator) {
            int len = static_cast<int>(item.label.size());
            if (len > max_label) max_label = len;
        }
    }
    int drop_w = (max_label + kItemPadX * 2) * kCharW;
    if (drop_w < 80) drop_w = 80;

    // Compute dropdown height
    int drop_h = 0;
    for (const auto& item : menu.items) {
        drop_h += item.separator ? 4 : kCharH;
    }

    int drop_y = kMenuBarH;

    // Clamp to screen bounds
    if (drop_x + drop_w > width) drop_x = width - drop_w;
    if (drop_x < 0) drop_x = 0;

    // Fill dropdown background (black)
    for (int py = drop_y; py < drop_y + drop_h && py < height; ++py) {
        for (int px = drop_x; px < drop_x + drop_w && px < width; ++px) {
            size_t idx = static_cast<size_t>(py) * pitch + static_cast<size_t>(px) * 3;
            rgb_buffer[idx]     = 0;
            rgb_buffer[idx + 1] = 0;
            rgb_buffer[idx + 2] = 0;
        }
    }

    // Draw items
    int item_y = drop_y;
    for (size_t i = 0; i < menu.items.size(); ++i) {
        const auto& item = menu.items[i];

        if (item.separator) {
            // Draw horizontal line
            int line_y = item_y + 2;
            if (line_y >= 0 && line_y < height) {
                for (int px = drop_x + 4; px < drop_x + drop_w - 4 && px < width; ++px) {
                    if (px < 0) continue;
                    size_t idx = static_cast<size_t>(line_y) * pitch + static_cast<size_t>(px) * 3;
                    rgb_buffer[idx]     = 128;
                    rgb_buffer[idx + 1] = 128;
                    rgb_buffer[idx + 2] = 128;
                }
            }
            item_y += 4;
            continue;
        }

        bool highlighted = (static_cast<int>(i) == selected_item_);
        std::string padded = std::string(kItemPadX, ' ') + item.label;
        // Pad to full width
        while (static_cast<int>(padded.size()) * kCharW < drop_w) {
            padded += ' ';
        }

        if (highlighted) {
            drawString(rgb_buffer, width, height, pitch,
                       drop_x, item_y, padded,
                       0, 0, 0,              // fg: black
                       200, 200, 200);       // bg: light gray
        } else {
            bool disabled = (item.action_id < 0);
            drawString(rgb_buffer, width, height, pitch,
                       drop_x, item_y, padded,
                       disabled ? static_cast<uint8_t>(128) : static_cast<uint8_t>(255),
                       disabled ? static_cast<uint8_t>(128) : static_cast<uint8_t>(255),
                       disabled ? static_cast<uint8_t>(128) : static_cast<uint8_t>(255),
                       0, 0, 0);             // bg: black
        }

        item_y += kCharH;
    }
}

} // namespace legends
