// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Input Source Interface

#pragma once

#include "pal/types.h"
#include <cstdint>

namespace pal {

/// Type of input event
enum class InputEventType {
    None = 0,
    KeyDown,
    KeyUp,
    MouseMotion,
    MouseButtonDown,
    MouseButtonUp,
    MouseWheel,
    JoystickAxis,
    JoystickButton,
    WindowClose,
    WindowResize,
    WindowFocus,
    WindowUnfocus
};

/// Input event from the host
///
/// @note host_timestamp_us is from IHostClock, NOT emulated time!
///       Event timestamps should NOT be used for emulation timing.
struct InputEvent {
    InputEventType type = InputEventType::None;
    uint64_t host_timestamp_us = 0;  // Host clock timestamp

    union {
        struct {
            uint16_t scancode;   // Hardware scancode
            uint16_t keycode;    // Logical key code
            bool repeat;         // True if auto-repeated
            bool _pad[3];
        } key;

        struct {
            int32_t x, y;        // Absolute position in window
            int32_t dx, dy;      // Relative motion since last event
        } mouse_motion;

        struct {
            uint8_t button;      // 1=left, 2=middle, 3=right, 4/5=extra
            uint8_t clicks;      // 1=single, 2=double click
            uint8_t _pad[2];
            int32_t x, y;        // Position at click
        } mouse_button;

        struct {
            int32_t dx, dy;      // Scroll amount (positive = up/right)
        } mouse_wheel;

        struct {
            uint8_t id;          // Joystick ID
            uint8_t _pad;
            int16_t axis;        // Axis index
            int16_t value;       // -32768 to 32767
        } joy_axis;

        struct {
            uint8_t id;          // Joystick ID
            uint8_t button;      // Button index
            bool pressed;        // True if pressed
            uint8_t _pad;
        } joy_button;

        struct {
            uint32_t width;      // New window width
            uint32_t height;     // New window height
        } window_resize;

        struct {
            bool focused;        // True if gained focus
            uint8_t _pad[3];
        } window_focus;
    };

    /// Default constructor - creates None event
    InputEvent() : type(InputEventType::None), host_timestamp_us(0) {
        // Zero-initialize the union
        key = {};
    }
};

/// Input source interface
///
/// Polls host input events (keyboard, mouse, joystick, window).
/// Events are translated to a platform-independent format.
class IInputSource {
public:
    virtual ~IInputSource() = default;

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    /// Initialize the input source
    /// @return Success, AlreadyInitialized
    virtual Result initialize() = 0;

    /// Shutdown the input source (safe to call if not initialized)
    virtual void shutdown() = 0;

    /// Check if input source is initialized
    virtual bool isInitialized() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Event Polling
    // ═══════════════════════════════════════════════════════════════════════

    /// Poll pending input events
    /// @param events [out] Array to receive events
    /// @param max_events Maximum number of events to retrieve
    /// @return Number of events retrieved (0 if none pending)
    virtual uint32_t poll(InputEvent* events, uint32_t max_events) = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Mouse Capture
    // ═══════════════════════════════════════════════════════════════════════

    /// Capture or release the mouse
    /// @param capture True to capture mouse to window
    /// @return Success, NotSupported
    virtual Result setMouseCapture(bool capture) = 0;

    /// Check if mouse is captured
    virtual bool isMouseCaptured() const = 0;

    /// Enable or disable relative mouse mode
    /// @param relative True for relative mode (FPS-style)
    /// @return Success, NotSupported
    virtual Result setRelativeMouseMode(bool relative) = 0;

    /// Check if relative mouse mode is enabled
    virtual bool isRelativeMouseMode() const = 0;
};

/// Convert InputEventType to string for debugging
constexpr const char* toString(InputEventType type) noexcept {
    switch (type) {
        case InputEventType::None:            return "None";
        case InputEventType::KeyDown:         return "KeyDown";
        case InputEventType::KeyUp:           return "KeyUp";
        case InputEventType::MouseMotion:     return "MouseMotion";
        case InputEventType::MouseButtonDown: return "MouseButtonDown";
        case InputEventType::MouseButtonUp:   return "MouseButtonUp";
        case InputEventType::MouseWheel:      return "MouseWheel";
        case InputEventType::JoystickAxis:    return "JoystickAxis";
        case InputEventType::JoystickButton:  return "JoystickButton";
        case InputEventType::WindowClose:     return "WindowClose";
        case InputEventType::WindowResize:    return "WindowResize";
        case InputEventType::WindowFocus:     return "WindowFocus";
        case InputEventType::WindowUnfocus:   return "WindowUnfocus";
    }
    return "Unknown";
}

} // namespace pal
