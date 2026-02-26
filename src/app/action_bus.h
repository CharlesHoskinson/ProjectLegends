// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ActionBus — centralized action dispatch for hotkeys and menu items.
// All user-triggered actions (pause, screenshot, save state, etc.) are
// routed through this bus so that input handling, menus, and tests can
// share a single code path.

#pragma once

#include <cstdint>
#include <functional>
#include <unordered_map>
#include <vector>

namespace legends {

enum class Action : uint16_t {
    Quit,
    Pause,
    Resume,
    TogglePause,
    Reset,
    SaveState,          // param = slot 1-9
    LoadState,          // param = slot 1-9
    Screenshot,
    OpenMapper,
    ClipboardPaste,
    VolumeUp,
    VolumeDown,
    ToggleMute,
    ReleaseMouseCapture,
    OpenMenu,

    // ── Phase 3: Enhanced Features ──────────────────────────────────────

    // Sprint 1: Fullscreen + Joystick
    ToggleFullscreen,

    // Sprint 2: Shaders
    ToggleShaders,
    NextShader,
    PrevShader,
    LoadCustomShader,

    // Sprint 3: AI Assistant
    ToggleAIPanel,
    AISubmitQuery,

    // Sprint 4: MIDI
    SetMIDIDevice,          // param = device index

    // Sprint 5: Printer + TTF
    TogglePrinter,
    ToggleTTFMode,

    // Sprint 6: IPX + 3dfx
    IPXConnect,
    IPXDisconnect,
    ToggleGlide,

    // Sprint 7: PC-98
    SetMachinePC98,
};

class ActionBus {
public:
    using Handler = std::function<void(int param)>;

    /// Dispatch an action to all registered handlers.
    void dispatch(Action action, int param = 0);

    /// Register a handler for an action. Multiple handlers per action allowed.
    void registerHandler(Action action, Handler handler);

    /// Remove all handlers for a specific action.
    void clearHandlers(Action action);

    /// Remove all handlers.
    void clearAll();

    /// Return the number of handlers registered for an action.
    size_t handlerCount(Action action) const;

    /// Return total number of dispatches (for testing).
    uint32_t dispatchCount() const { return dispatch_count_; }

private:
    std::unordered_map<Action, std::vector<Handler>> handlers_;
    uint32_t dispatch_count_ = 0;
};

} // namespace legends
