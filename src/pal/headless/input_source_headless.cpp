// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Headless Input Source Implementation

#include "pal/input_source.h"
#include <algorithm>
#include <memory>
#include <mutex>
#include <vector>

namespace pal {
namespace headless {

/// Headless input source - accepts injected events for testing
class InputSourceHeadless : public IInputSource {
public:
    InputSourceHeadless() = default;
    ~InputSourceHeadless() override { shutdown(); }

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
        std::lock_guard<std::mutex> lock(mutex_);
        event_queue_.clear();
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

        std::lock_guard<std::mutex> lock(mutex_);

        uint32_t count = std::min(max_events, static_cast<uint32_t>(event_queue_.size()));
        for (uint32_t i = 0; i < count; ++i) {
            events[i] = event_queue_[i];
        }

        // Remove polled events from queue
        if (count > 0) {
            event_queue_.erase(event_queue_.begin(), event_queue_.begin() + count);
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
        relative_mouse_ = relative;
        return Result::Success;
    }

    bool isRelativeMouseMode() const override {
        return relative_mouse_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Test API - Event Injection
    // ═══════════════════════════════════════════════════════════════════════

    /// Inject a raw event into the queue
    void injectEvent(const InputEvent& event) {
        std::lock_guard<std::mutex> lock(mutex_);
        event_queue_.push_back(event);
    }

    /// Inject a key down event
    void injectKeyDown(uint16_t scancode, uint16_t keycode = 0, bool repeat = false) {
        InputEvent event;
        event.type = InputEventType::KeyDown;
        event.host_timestamp_us = 0;  // Should be set by caller if needed
        event.key.scancode = scancode;
        event.key.keycode = keycode ? keycode : scancode;
        event.key.repeat = repeat;
        injectEvent(event);
    }

    /// Inject a key up event
    void injectKeyUp(uint16_t scancode, uint16_t keycode = 0) {
        InputEvent event;
        event.type = InputEventType::KeyUp;
        event.host_timestamp_us = 0;
        event.key.scancode = scancode;
        event.key.keycode = keycode ? keycode : scancode;
        event.key.repeat = false;
        injectEvent(event);
    }

    /// Inject a mouse motion event
    void injectMouseMotion(int32_t x, int32_t y, int32_t dx = 0, int32_t dy = 0) {
        InputEvent event;
        event.type = InputEventType::MouseMotion;
        event.host_timestamp_us = 0;
        event.mouse_motion.x = x;
        event.mouse_motion.y = y;
        event.mouse_motion.dx = dx;
        event.mouse_motion.dy = dy;
        injectEvent(event);
    }

    /// Inject a mouse button down event
    void injectMouseButtonDown(uint8_t button, int32_t x = 0, int32_t y = 0) {
        InputEvent event;
        event.type = InputEventType::MouseButtonDown;
        event.host_timestamp_us = 0;
        event.mouse_button.button = button;
        event.mouse_button.clicks = 1;
        event.mouse_button.x = x;
        event.mouse_button.y = y;
        injectEvent(event);
    }

    /// Inject a mouse button up event
    void injectMouseButtonUp(uint8_t button, int32_t x = 0, int32_t y = 0) {
        InputEvent event;
        event.type = InputEventType::MouseButtonUp;
        event.host_timestamp_us = 0;
        event.mouse_button.button = button;
        event.mouse_button.clicks = 0;
        event.mouse_button.x = x;
        event.mouse_button.y = y;
        injectEvent(event);
    }

    /// Inject a mouse wheel event
    void injectMouseWheel(int32_t dx, int32_t dy) {
        InputEvent event;
        event.type = InputEventType::MouseWheel;
        event.host_timestamp_us = 0;
        event.mouse_wheel.dx = dx;
        event.mouse_wheel.dy = dy;
        injectEvent(event);
    }

    /// Inject a window close event
    void injectWindowClose() {
        InputEvent event;
        event.type = InputEventType::WindowClose;
        event.host_timestamp_us = 0;
        injectEvent(event);
    }

    /// Inject a window resize event
    void injectWindowResize(uint32_t width, uint32_t height) {
        InputEvent event;
        event.type = InputEventType::WindowResize;
        event.host_timestamp_us = 0;
        event.window_resize.width = width;
        event.window_resize.height = height;
        injectEvent(event);
    }

    /// Clear all pending events
    void clearEventQueue() {
        std::lock_guard<std::mutex> lock(mutex_);
        event_queue_.clear();
    }

    /// Get number of pending events
    size_t getQueuedEventCount() const {
        std::lock_guard<std::mutex> lock(mutex_);
        return event_queue_.size();
    }

private:
    bool initialized_ = false;
    bool mouse_captured_ = false;
    bool relative_mouse_ = false;

    mutable std::mutex mutex_;
    std::vector<InputEvent> event_queue_;
};

} // namespace headless

// Factory function (called by platform_headless.cpp)
std::unique_ptr<IInputSource> createInputSourceHeadless() {
    return std::make_unique<headless::InputSourceHeadless>();
}

} // namespace pal
