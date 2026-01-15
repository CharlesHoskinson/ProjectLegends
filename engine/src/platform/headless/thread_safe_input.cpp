/**
 * @file thread_safe_input.cpp
 * @brief ThreadSafeInput implementation for multi-threaded input injection.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/platform/headless.h"

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// ThreadSafeInput Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void ThreadSafeInput::push_event(const InputEvent& event) {
    std::lock_guard<std::mutex> lock(mutex_);
    events_.push(event);
}

std::optional<InputEvent> ThreadSafeInput::poll_event() {
    std::lock_guard<std::mutex> lock(mutex_);

    if (events_.empty()) {
        return std::nullopt;
    }

    InputEvent event = events_.front();
    events_.pop();
    return event;
}

bool ThreadSafeInput::has_events() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return !events_.empty();
}

void ThreadSafeInput::clear() {
    std::lock_guard<std::mutex> lock(mutex_);
    while (!events_.empty()) {
        events_.pop();
    }
}

bool ThreadSafeInput::is_mouse_captured() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return mouse_captured_;
}

void ThreadSafeInput::set_mouse_captured(bool captured) {
    std::lock_guard<std::mutex> lock(mutex_);
    mouse_captured_ = captured;
}

KeyMod ThreadSafeInput::get_modifiers() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return modifiers_;
}

void ThreadSafeInput::set_modifiers(KeyMod mods) {
    std::lock_guard<std::mutex> lock(mutex_);
    modifiers_ = mods;
}

size_t ThreadSafeInput::queue_size() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return events_.size();
}

} // namespace platform
} // namespace dosbox
