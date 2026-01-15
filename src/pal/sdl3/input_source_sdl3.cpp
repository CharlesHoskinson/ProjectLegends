// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL3 Input Source Implementation
//
// SDL3 changes event constant names (SDL_EVENT_* instead of SDL_*)
// and field names (event.key.key instead of event.key.keysym.sym)

#include "pal/input_source.h"
#include <SDL3/SDL.h>
#include <memory>

namespace pal {
namespace sdl3 {

/// SDL3 input source - translates SDL3 events to PAL events
class InputSourceSDL3 : public IInputSource {
public:
    InputSourceSDL3() = default;
    ~InputSourceSDL3() override { shutdown(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result initialize() override {
        if (initialized_) {
            return Result::AlreadyInitialized;
        }
        initialized_ = true;
        return Result::Success;
    }

    void shutdown() override {
        if (mouse_captured_) {
            SDL_SetWindowRelativeMouseMode(nullptr, false);
        }
        initialized_ = false;
        mouse_captured_ = false;
        relative_mouse_ = false;
    }

    bool isInitialized() const override {
        return initialized_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Event Polling
    // ═══════════════════════════════════════════════════════════════════════

    uint32_t poll(InputEvent* events, uint32_t max_events) override {
        if (!initialized_ || events == nullptr || max_events == 0) {
            return 0;
        }

        uint32_t count = 0;
        SDL_Event sdl_event;

        while (count < max_events && SDL_PollEvent(&sdl_event)) {
            InputEvent& event = events[count];

            if (translateEvent(sdl_event, event)) {
                event.host_timestamp_us = SDL_GetTicks() * 1000ULL;
                ++count;
            }
        }

        return count;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Mouse Capture
    // ═══════════════════════════════════════════════════════════════════════

    Result setMouseCapture(bool capture) override {
        if (!initialized_) {
            return Result::NotInitialized;
        }

        // SDL3: Use SDL_SetWindowRelativeMouseMode with window
        // For simplicity, we capture on the focused window
        SDL_Window* window = SDL_GetKeyboardFocus();
        if (window) {
            SDL_SetWindowRelativeMouseMode(window, capture);
        }

        mouse_captured_ = capture;
        return Result::Success;
    }

    bool isMouseCaptured() const override {
        return mouse_captured_;
    }

    Result setRelativeMouseMode(bool relative) override {
        if (!initialized_) {
            return Result::NotInitialized;
        }

        SDL_Window* window = SDL_GetKeyboardFocus();
        if (window) {
            if (!SDL_SetWindowRelativeMouseMode(window, relative)) {
                return Result::NotSupported;
            }
        }

        relative_mouse_ = relative;
        return Result::Success;
    }

    bool isRelativeMouseMode() const override {
        return relative_mouse_;
    }

private:
    bool translateEvent(const SDL_Event& sdl, InputEvent& event) {
        switch (sdl.type) {
            // SDL3: New event constant names
            case SDL_EVENT_KEY_DOWN:
                event.type = InputEventType::KeyDown;
                event.key.scancode = static_cast<uint16_t>(sdl.key.scancode);
                event.key.keycode = static_cast<uint16_t>(sdl.key.key & 0xFFFF);  // SDL3: .key not .keysym.sym
                event.key.repeat = sdl.key.repeat != 0;
                return true;

            case SDL_EVENT_KEY_UP:
                event.type = InputEventType::KeyUp;
                event.key.scancode = static_cast<uint16_t>(sdl.key.scancode);
                event.key.keycode = static_cast<uint16_t>(sdl.key.key & 0xFFFF);
                event.key.repeat = false;
                return true;

            case SDL_EVENT_MOUSE_MOTION:
                event.type = InputEventType::MouseMotion;
                event.mouse_motion.x = static_cast<int32_t>(sdl.motion.x);
                event.mouse_motion.y = static_cast<int32_t>(sdl.motion.y);
                event.mouse_motion.dx = static_cast<int32_t>(sdl.motion.xrel);
                event.mouse_motion.dy = static_cast<int32_t>(sdl.motion.yrel);
                return true;

            case SDL_EVENT_MOUSE_BUTTON_DOWN:
                event.type = InputEventType::MouseButtonDown;
                event.mouse_button.button = sdl.button.button;
                event.mouse_button.clicks = sdl.button.clicks;
                event.mouse_button.x = static_cast<int32_t>(sdl.button.x);
                event.mouse_button.y = static_cast<int32_t>(sdl.button.y);
                return true;

            case SDL_EVENT_MOUSE_BUTTON_UP:
                event.type = InputEventType::MouseButtonUp;
                event.mouse_button.button = sdl.button.button;
                event.mouse_button.clicks = 0;
                event.mouse_button.x = static_cast<int32_t>(sdl.button.x);
                event.mouse_button.y = static_cast<int32_t>(sdl.button.y);
                return true;

            case SDL_EVENT_MOUSE_WHEEL:
                event.type = InputEventType::MouseWheel;
                event.mouse_wheel.dx = static_cast<int32_t>(sdl.wheel.x);
                event.mouse_wheel.dy = static_cast<int32_t>(sdl.wheel.y);
                return true;

            case SDL_EVENT_JOYSTICK_AXIS_MOTION:
                event.type = InputEventType::JoystickAxis;
                event.joy_axis.id = static_cast<uint8_t>(sdl.jaxis.which);
                event.joy_axis.axis = static_cast<int16_t>(sdl.jaxis.axis);
                event.joy_axis.value = sdl.jaxis.value;
                return true;

            case SDL_EVENT_JOYSTICK_BUTTON_DOWN:
            case SDL_EVENT_JOYSTICK_BUTTON_UP:
                event.type = InputEventType::JoystickButton;
                event.joy_button.id = static_cast<uint8_t>(sdl.jbutton.which);
                event.joy_button.button = sdl.jbutton.button;
                event.joy_button.pressed = (sdl.type == SDL_EVENT_JOYSTICK_BUTTON_DOWN);
                return true;

            case SDL_EVENT_WINDOW_CLOSE_REQUESTED:
                event.type = InputEventType::WindowClose;
                return true;

            case SDL_EVENT_WINDOW_RESIZED:
                event.type = InputEventType::WindowResize;
                event.window_resize.width = static_cast<uint32_t>(sdl.window.data1);
                event.window_resize.height = static_cast<uint32_t>(sdl.window.data2);
                return true;

            case SDL_EVENT_WINDOW_FOCUS_GAINED:
                event.type = InputEventType::WindowFocus;
                event.window_focus.focused = true;
                return true;

            case SDL_EVENT_WINDOW_FOCUS_LOST:
                event.type = InputEventType::WindowUnfocus;
                event.window_focus.focused = false;
                return true;

            case SDL_EVENT_QUIT:
                event.type = InputEventType::WindowClose;
                return true;

            default:
                return false;
        }
    }

    bool initialized_ = false;
    bool mouse_captured_ = false;
    bool relative_mouse_ = false;
};

} // namespace sdl3

// Factory function
std::unique_ptr<IInputSource> createInputSourceSDL3() {
    return std::make_unique<sdl3::InputSourceSDL3>();
}

} // namespace pal
