// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL2 Input Source Implementation

#include "pal/input_source.h"
#include <SDL.h>
#include <memory>

namespace pal {
namespace sdl2 {

/// SDL2 input source - translates SDL events to PAL events
class InputSourceSDL2 : public IInputSource {
public:
    InputSourceSDL2() = default;
    ~InputSourceSDL2() override { shutdown(); }

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
            SDL_SetRelativeMouseMode(SDL_FALSE);
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

        if (capture) {
            SDL_SetRelativeMouseMode(SDL_TRUE);
        } else {
            SDL_SetRelativeMouseMode(SDL_FALSE);
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

        if (SDL_SetRelativeMouseMode(relative ? SDL_TRUE : SDL_FALSE) != 0) {
            return Result::NotSupported;
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
            case SDL_KEYDOWN:
                event.type = InputEventType::KeyDown;
                event.key.scancode = static_cast<uint16_t>(sdl.key.keysym.scancode);
                event.key.keycode = static_cast<uint16_t>(sdl.key.keysym.sym & 0xFFFF);
                event.key.repeat = sdl.key.repeat != 0;
                return true;

            case SDL_KEYUP:
                event.type = InputEventType::KeyUp;
                event.key.scancode = static_cast<uint16_t>(sdl.key.keysym.scancode);
                event.key.keycode = static_cast<uint16_t>(sdl.key.keysym.sym & 0xFFFF);
                event.key.repeat = false;
                return true;

            case SDL_MOUSEMOTION:
                event.type = InputEventType::MouseMotion;
                event.mouse_motion.x = sdl.motion.x;
                event.mouse_motion.y = sdl.motion.y;
                event.mouse_motion.dx = sdl.motion.xrel;
                event.mouse_motion.dy = sdl.motion.yrel;
                return true;

            case SDL_MOUSEBUTTONDOWN:
                event.type = InputEventType::MouseButtonDown;
                event.mouse_button.button = sdl.button.button;
                event.mouse_button.clicks = sdl.button.clicks;
                event.mouse_button.x = sdl.button.x;
                event.mouse_button.y = sdl.button.y;
                return true;

            case SDL_MOUSEBUTTONUP:
                event.type = InputEventType::MouseButtonUp;
                event.mouse_button.button = sdl.button.button;
                event.mouse_button.clicks = 0;
                event.mouse_button.x = sdl.button.x;
                event.mouse_button.y = sdl.button.y;
                return true;

            case SDL_MOUSEWHEEL:
                event.type = InputEventType::MouseWheel;
                event.mouse_wheel.dx = sdl.wheel.x;
                event.mouse_wheel.dy = sdl.wheel.y;
                return true;

            case SDL_JOYAXISMOTION:
                event.type = InputEventType::JoystickAxis;
                event.joy_axis.id = static_cast<uint8_t>(sdl.jaxis.which);
                event.joy_axis.axis = static_cast<int16_t>(sdl.jaxis.axis);
                event.joy_axis.value = sdl.jaxis.value;
                return true;

            case SDL_JOYBUTTONDOWN:
            case SDL_JOYBUTTONUP:
                event.type = InputEventType::JoystickButton;
                event.joy_button.id = static_cast<uint8_t>(sdl.jbutton.which);
                event.joy_button.button = sdl.jbutton.button;
                event.joy_button.pressed = (sdl.type == SDL_JOYBUTTONDOWN);
                return true;

            case SDL_WINDOWEVENT:
                return translateWindowEvent(sdl.window, event);

            case SDL_QUIT:
                event.type = InputEventType::WindowClose;
                return true;

            default:
                return false;
        }
    }

    bool translateWindowEvent(const SDL_WindowEvent& win, InputEvent& event) {
        switch (win.event) {
            case SDL_WINDOWEVENT_CLOSE:
                event.type = InputEventType::WindowClose;
                return true;

            case SDL_WINDOWEVENT_RESIZED:
            case SDL_WINDOWEVENT_SIZE_CHANGED:
                event.type = InputEventType::WindowResize;
                event.window_resize.width = static_cast<uint32_t>(win.data1);
                event.window_resize.height = static_cast<uint32_t>(win.data2);
                return true;

            case SDL_WINDOWEVENT_FOCUS_GAINED:
                event.type = InputEventType::WindowFocus;
                event.window_focus.focused = true;
                return true;

            case SDL_WINDOWEVENT_FOCUS_LOST:
                event.type = InputEventType::WindowUnfocus;
                event.window_focus.focused = false;
                return true;

            default:
                return false;
        }
    }

    bool initialized_ = false;
    bool mouse_captured_ = false;
    bool relative_mouse_ = false;
};

} // namespace sdl2

// Factory function
std::unique_ptr<IInputSource> createInputSourceSDL2() {
    return std::make_unique<sdl2::InputSourceSDL2>();
}

} // namespace pal
