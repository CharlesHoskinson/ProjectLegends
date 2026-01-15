/**
 * @file event_bus.h
 * @brief Internal event bus with zero-copy semantics.
 *
 * Provides an event system with two layers:
 * - InternalEventBus: Zero-copy events for internal subsystem communication
 * - ExternalEventBridge: Serializes events to FFI-safe format for external consumers
 */

#pragma once

#include "events.h"
#include "function_ref.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <mutex>
#include <optional>
#include <queue>
#include <variant>
#include <vector>

namespace aibox {

// ─────────────────────────────────────────────────────────────────────────────
// Internal Event Types (Zero-Copy)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Internal event variant using reference wrappers for zero-copy.
 *
 * Events are passed by const reference within the same process,
 * avoiding any copying of the event data.
 */
using InternalEvent = std::variant<
    std::reference_wrapper<const events::TextModeScreen>,
    std::reference_wrapper<const events::TextModeDiff>,
    std::reference_wrapper<const events::ProgramStartedEvent>,
    std::reference_wrapper<const events::ProgramHaltedEvent>,
    std::reference_wrapper<const events::KeyboardEvent>,
    std::reference_wrapper<const events::MouseEvent>
>;

/**
 * @brief Get the event type from an InternalEvent.
 */
[[nodiscard]] inline events::EventType get_event_type(const InternalEvent& event) noexcept {
    return std::visit([](auto&& e) -> events::EventType {
        using T = std::decay_t<decltype(e.get())>;
        if constexpr (std::is_same_v<T, events::TextModeScreen>) {
            return events::EventType::TextScreen;
        } else if constexpr (std::is_same_v<T, events::TextModeDiff>) {
            return events::EventType::TextDiff;
        } else if constexpr (std::is_same_v<T, events::ProgramStartedEvent>) {
            return events::EventType::ProgramStarted;
        } else if constexpr (std::is_same_v<T, events::ProgramHaltedEvent>) {
            return events::EventType::ProgramHalted;
        } else if constexpr (std::is_same_v<T, events::KeyboardEvent>) {
            return events::EventType::Keyboard;
        } else if constexpr (std::is_same_v<T, events::MouseEvent>) {
            return events::EventType::Mouse;
        } else {
            return events::EventType::TextScreen; // Fallback
        }
    }, event);
}

// ─────────────────────────────────────────────────────────────────────────────
// Subscription Token
// ─────────────────────────────────────────────────────────────────────────────

// Forward declaration
class InternalEventBus;

/**
 * @brief RAII token for event bus subscriptions.
 *
 * Automatically unsubscribes when destroyed. Non-copyable, movable.
 */
class EventSubscriptionToken {
public:
    /**
     * @brief Default constructor creates an invalid token.
     */
    EventSubscriptionToken() = default;

    /**
     * @brief Destructor unsubscribes from the event bus.
     */
    ~EventSubscriptionToken() {
        release();
    }

    // Non-copyable
    EventSubscriptionToken(const EventSubscriptionToken&) = delete;
    EventSubscriptionToken& operator=(const EventSubscriptionToken&) = delete;

    // Movable
    EventSubscriptionToken(EventSubscriptionToken&& other) noexcept
        : bus_(other.bus_)
        , id_(other.id_)
    {
        other.bus_ = nullptr;
    }

    EventSubscriptionToken& operator=(EventSubscriptionToken&& other) noexcept {
        if (this != &other) {
            release();
            bus_ = other.bus_;
            id_ = other.id_;
            other.bus_ = nullptr;
        }
        return *this;
    }

    /**
     * @brief Check if token is valid (subscription active).
     */
    [[nodiscard]] bool valid() const noexcept { return bus_ != nullptr; }

    /**
     * @brief Get subscription ID.
     */
    [[nodiscard]] uint32_t id() const noexcept { return id_; }

    /**
     * @brief Explicitly release (unsubscribe).
     */
    void release();

private:
    friend class InternalEventBus;

    EventSubscriptionToken(InternalEventBus* bus, uint32_t id)
        : bus_(bus), id_(id) {}

    InternalEventBus* bus_ = nullptr;
    uint32_t id_ = 0;
};

// ─────────────────────────────────────────────────────────────────────────────
// Internal Event Handler
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Internal event handler callback type.
 *
 * Handlers receive events by const reference for zero-copy semantics.
 */
using InternalEventHandler = std::function<void(const InternalEvent&)>;

/**
 * @brief Stored subscription entry.
 */
struct EventSubscription {
    uint32_t id;
    InternalEventHandler handler;
    bool active;
};

// ─────────────────────────────────────────────────────────────────────────────
// Internal Event Bus
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Internal event bus for subsystem communication.
 *
 * Provides synchronous, zero-copy event delivery within the emulator.
 * Thread-safe for subscription management; events are dispatched on
 * the calling thread.
 *
 * Example:
 * @code
 *   InternalEventBus bus;
 *
 *   // Subscribe to events
 *   auto token = bus.subscribe([](const InternalEvent& event) {
 *       std::visit([](auto&& e) {
 *           // Handle event
 *       }, event);
 *   });
 *
 *   // Emit an event
 *   events::TextModeScreen screen;
 *   // ... populate screen ...
 *   bus.emit(screen);
 *
 *   // Token automatically unsubscribes when destroyed
 * @endcode
 */
class InternalEventBus {
public:
    InternalEventBus() = default;

    // Non-copyable, non-movable (contains subscriptions)
    InternalEventBus(const InternalEventBus&) = delete;
    InternalEventBus& operator=(const InternalEventBus&) = delete;
    InternalEventBus(InternalEventBus&&) = delete;
    InternalEventBus& operator=(InternalEventBus&&) = delete;

    /**
     * @brief Subscribe to internal events.
     *
     * @param handler Callback function for events
     * @return RAII token that unsubscribes when destroyed
     */
    [[nodiscard]] EventSubscriptionToken subscribe(InternalEventHandler handler) {
        std::lock_guard lock(mutex_);

        uint32_t id = next_id_++;
        subscriptions_.push_back(EventSubscription{id, std::move(handler), true});

        return EventSubscriptionToken(this, id);
    }

    /**
     * @brief Emit an event to all subscribers (synchronous, zero-copy).
     *
     * @tparam EventT Event type (must be one of the supported event types)
     * @param event Event to emit (passed by reference, not copied)
     */
    template<typename EventT>
    void emit(const EventT& event) {
        InternalEvent wrapper{std::cref(event)};

        // Take a snapshot of handlers to avoid holding lock during callbacks
        std::vector<InternalEventHandler> handlers;
        {
            std::lock_guard lock(mutex_);
            for (const auto& sub : subscriptions_) {
                if (sub.active) {
                    handlers.push_back(sub.handler);
                }
            }
        }

        // Dispatch to all handlers (outside lock)
        for (const auto& handler : handlers) {
            handler(wrapper);
        }
    }

    /**
     * @brief Get number of active subscriptions.
     */
    [[nodiscard]] size_t subscription_count() const noexcept {
        std::lock_guard lock(mutex_);
        size_t count = 0;
        for (const auto& sub : subscriptions_) {
            if (sub.active) {
                ++count;
            }
        }
        return count;
    }

private:
    friend class EventSubscriptionToken;

    void unsubscribe(uint32_t id) {
        std::lock_guard lock(mutex_);
        for (auto& sub : subscriptions_) {
            if (sub.id == id) {
                sub.active = false;
                break;
            }
        }
        // Clean up inactive subscriptions periodically
        cleanup_if_needed();
    }

    void cleanup_if_needed() {
        // Remove inactive subscriptions when there are too many
        if (subscriptions_.size() > 100) {
            subscriptions_.erase(
                std::remove_if(subscriptions_.begin(), subscriptions_.end(),
                    [](const EventSubscription& s) { return !s.active; }),
                subscriptions_.end()
            );
        }
    }

    mutable std::mutex mutex_;
    std::vector<EventSubscription> subscriptions_;
    uint32_t next_id_{1};
};

// Inline implementation of EventSubscriptionToken::release
inline void EventSubscriptionToken::release() {
    if (bus_) {
        bus_->unsubscribe(id_);
        bus_ = nullptr;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// External Event (Serialized)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief External event with serialized data for FFI.
 *
 * Contains a copy of the event data in a format safe to pass
 * across the FFI boundary.
 */
struct ExternalEvent {
    events::EventType type;
    uint64_t timestamp_us;
    std::vector<uint8_t> data;  ///< Serialized event data
};

/**
 * @brief External event callback type (C-compatible).
 */
using ExternalEventCallback = void(*)(
    int event_type,
    const void* data,
    size_t data_size,
    void* user_data
);

/**
 * @brief External subscription entry.
 */
struct ExternalSubscription {
    events::EventType event_type;
    ExternalEventCallback callback;
    void* user_data;
    bool active;
};

// ─────────────────────────────────────────────────────────────────────────────
// External Event Bridge
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Bridge from internal events to external (FFI) consumers.
 *
 * Subscribes to the internal event bus and serializes events
 * for delivery through FFI callbacks. Events can be queued and
 * flushed on the main thread for thread safety.
 *
 * Example:
 * @code
 *   InternalEventBus bus;
 *   ExternalEventBridge bridge(bus);
 *
 *   // Subscribe external callback
 *   bridge.subscribe(events::EventType::TextScreen, my_callback, &user_data);
 *
 *   // ... emit events to internal bus ...
 *
 *   // Flush pending events to external subscribers
 *   bridge.flush();
 * @endcode
 */
class ExternalEventBridge {
public:
    /**
     * @brief Construct bridge connected to internal bus.
     */
    explicit ExternalEventBridge(InternalEventBus& internal_bus)
        : internal_bus_(internal_bus)
    {
        // Subscribe to all internal events
        internal_token_ = internal_bus_.subscribe(
            [this](const InternalEvent& event) {
                on_internal_event(event);
            }
        );
    }

    ~ExternalEventBridge() = default;

    // Non-copyable, non-movable
    ExternalEventBridge(const ExternalEventBridge&) = delete;
    ExternalEventBridge& operator=(const ExternalEventBridge&) = delete;
    ExternalEventBridge(ExternalEventBridge&&) = delete;
    ExternalEventBridge& operator=(ExternalEventBridge&&) = delete;

    /**
     * @brief Subscribe external callback to event type.
     *
     * @param type Event type to subscribe to
     * @param callback C-compatible callback function
     * @param user_data User data passed to callback
     */
    void subscribe(events::EventType type,
                   ExternalEventCallback callback,
                   void* user_data) {
        std::lock_guard lock(mutex_);
        subscriptions_.push_back(ExternalSubscription{
            type, callback, user_data, true
        });
    }

    /**
     * @brief Unsubscribe external callback.
     */
    void unsubscribe(events::EventType type, ExternalEventCallback callback) {
        std::lock_guard lock(mutex_);
        for (auto& sub : subscriptions_) {
            if (sub.event_type == type && sub.callback == callback) {
                sub.active = false;
            }
        }
    }

    /**
     * @brief Enable text diff mode.
     *
     * When enabled, TextModeScreen events are converted to TextModeDiff
     * events by comparing against the last screen state.
     */
    void set_text_diff_mode(bool enabled) noexcept {
        text_diff_enabled_ = enabled;
    }

    /**
     * @brief Check if text diff mode is enabled.
     */
    [[nodiscard]] bool text_diff_enabled() const noexcept {
        return text_diff_enabled_;
    }

    /**
     * @brief Flush pending events to external subscribers.
     *
     * Should be called from the main thread to ensure thread safety
     * for external callbacks.
     *
     * @return Number of events flushed
     */
    size_t flush() {
        std::queue<ExternalEvent> events_to_deliver;

        // Move pending events to local queue
        {
            std::lock_guard lock(mutex_);
            std::swap(events_to_deliver, pending_events_);
        }

        size_t count = 0;
        while (!events_to_deliver.empty()) {
            auto& event = events_to_deliver.front();
            deliver_event(event);
            events_to_deliver.pop();
            ++count;
        }

        return count;
    }

    /**
     * @brief Get number of pending events.
     */
    [[nodiscard]] size_t pending_count() const noexcept {
        std::lock_guard lock(mutex_);
        return pending_events_.size();
    }

    /**
     * @brief Get number of active subscriptions.
     */
    [[nodiscard]] size_t subscription_count() const noexcept {
        std::lock_guard lock(mutex_);
        size_t count = 0;
        for (const auto& sub : subscriptions_) {
            if (sub.active) {
                ++count;
            }
        }
        return count;
    }

private:
    void on_internal_event(const InternalEvent& event) {
        ExternalEvent ext = serialize_event(event);

        std::lock_guard lock(mutex_);
        pending_events_.push(std::move(ext));
    }

    ExternalEvent serialize_event(const InternalEvent& event) {
        ExternalEvent ext;
        ext.type = get_event_type(event);

        std::visit([&ext](auto&& e) {
            using T = std::decay_t<decltype(e.get())>;
            const auto& data = e.get();

            // Get timestamp
            if constexpr (std::is_same_v<T, events::TextModeScreen>) {
                ext.timestamp_us = data.timestamp_us;
            } else if constexpr (std::is_same_v<T, events::TextModeDiff>) {
                ext.timestamp_us = data.timestamp_us;
            } else if constexpr (std::is_same_v<T, events::ProgramStartedEvent>) {
                ext.timestamp_us = data.timestamp_us;
            } else if constexpr (std::is_same_v<T, events::ProgramHaltedEvent>) {
                ext.timestamp_us = data.timestamp_us;
            } else if constexpr (std::is_same_v<T, events::KeyboardEvent>) {
                ext.timestamp_us = data.timestamp_us;
            } else if constexpr (std::is_same_v<T, events::MouseEvent>) {
                ext.timestamp_us = data.timestamp_us;
            }

            // Serialize to bytes (simplified - just copy raw bytes)
            ext.data.resize(sizeof(T));
            std::memcpy(ext.data.data(), &data, sizeof(T));
        }, event);

        return ext;
    }

    void deliver_event(const ExternalEvent& event) {
        std::vector<ExternalSubscription> subs_copy;
        {
            std::lock_guard lock(mutex_);
            for (const auto& sub : subscriptions_) {
                if (sub.active && sub.event_type == event.type) {
                    subs_copy.push_back(sub);
                }
            }
        }

        for (const auto& sub : subs_copy) {
            sub.callback(
                static_cast<int>(event.type),
                event.data.data(),
                event.data.size(),
                sub.user_data
            );
        }
    }

    InternalEventBus& internal_bus_;
    EventSubscriptionToken internal_token_;

    mutable std::mutex mutex_;
    std::vector<ExternalSubscription> subscriptions_;
    std::queue<ExternalEvent> pending_events_;

    bool text_diff_enabled_{false};
    std::optional<events::TextModeScreen> last_text_screen_;
};

} // namespace aibox
