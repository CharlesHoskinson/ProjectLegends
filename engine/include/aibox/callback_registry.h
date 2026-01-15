/**
 * @file callback_registry.h
 * @brief Type-safe callback registration with RAII tokens.
 *
 * Provides zero-overhead callbacks for hot paths using raw function pointers,
 * with automatic unregistration via RAII tokens.
 */

#pragma once

#include <gsl/gsl-lite.hpp>
#include <algorithm>
#include <array>
#include <optional>
#include <ranges>
#include <string_view>
#include <cstdint>
#include <cassert>

namespace aibox {

using CallbackId = uint16_t;

/**
 * @brief Fast callback type for hot paths.
 *
 * Uses raw function pointer + userdata for zero overhead.
 * @param userdata Context pointer passed at registration
 * @return Callback result (meaning depends on callback type)
 *
 * Threading: Must be called from emulation thread only.
 */
using FastCallback = uint32_t (*)(void* userdata);

/**
 * @brief Callback entry with metadata.
 */
struct CallbackEntry {
    FastCallback handler = nullptr;
    void* userdata = nullptr;
    const char* description = "";
    bool active = false;
};

// Forward declaration
class CallbackRegistry;

/**
 * @brief RAII token for callback registration.
 *
 * Automatically unregisters callback when destroyed.
 * Non-copyable, movable. When moved, original becomes invalid.
 *
 * Example:
 * @code
 *   {
 *       auto token = registry.register_callback(my_handler, &data, "handler");
 *       // callback is registered while token exists
 *       registry.invoke(token->id());
 *   }
 *   // callback automatically unregistered when token goes out of scope
 * @endcode
 */
class CallbackToken {
public:
    /**
     * @brief Default constructor creates invalid token.
     */
    CallbackToken() = default;

    /**
     * @brief Destructor unregisters the callback.
     */
    ~CallbackToken() {
        release();
    }

    // Non-copyable
    CallbackToken(const CallbackToken&) = delete;
    CallbackToken& operator=(const CallbackToken&) = delete;

    // Movable
    CallbackToken(CallbackToken&& other) noexcept
        : registry_(other.registry_)
        , id_(other.id_)
    {
        other.registry_ = nullptr;
    }

    CallbackToken& operator=(CallbackToken&& other) noexcept {
        if (this != &other) {
            release();
            registry_ = other.registry_;
            id_ = other.id_;
            other.registry_ = nullptr;
        }
        return *this;
    }

    /**
     * @brief Check if token is valid (callback registered).
     */
    [[nodiscard]] bool valid() const noexcept { return registry_ != nullptr; }

    /**
     * @brief Get callback ID.
     * @pre valid() must be true
     */
    [[nodiscard]] CallbackId id() const noexcept {
        gsl_Expects(valid());
        return id_;
    }

    /**
     * @brief Explicitly release (unregister) the callback.
     */
    void release();

private:
    friend class CallbackRegistry;

    CallbackToken(CallbackRegistry* registry, CallbackId id)
        : registry_(registry), id_(id) {}

    CallbackRegistry* registry_ = nullptr;
    CallbackId id_ = 0;
};

/**
 * @brief Registry for managing callbacks.
 *
 * Provides RAII-based registration and fast O(1) invocation.
 * Thread-safety: NOT thread-safe. Use from emulation thread only.
 *
 * Design notes:
 * - Uses fixed-size array for O(1) lookup
 * - Linear search for registration (cold path)
 * - Direct indexing for invocation (hot path)
 */
class CallbackRegistry {
public:
    static constexpr size_t MaxCallbacks = 256;

    CallbackRegistry() = default;

    // Non-copyable (owns callback state)
    CallbackRegistry(const CallbackRegistry&) = delete;
    CallbackRegistry& operator=(const CallbackRegistry&) = delete;

    // Movable
    CallbackRegistry(CallbackRegistry&&) = default;
    CallbackRegistry& operator=(CallbackRegistry&&) = default;

    /**
     * @brief Register a callback.
     *
     * @param handler Function pointer (must not be null)
     * @param userdata Context passed to handler
     * @param description Human-readable description for debugging
     * @return RAII token that unregisters on destruction, or empty if handler is null or full
     */
    [[nodiscard]] std::optional<CallbackToken> register_callback(
        FastCallback handler,
        void* userdata = nullptr,
        const char* description = ""
    ) {
        if (!handler) {
            return std::nullopt;
        }

        // Find free slot using std::ranges
        auto it = std::ranges::find_if(entries_, [](const CallbackEntry& e) { return !e.active; });
        if (it == entries_.end()) {
            return std::nullopt; // Registry full
        }

        it->handler = handler;
        it->userdata = userdata;
        it->description = description;
        it->active = true;
        ++active_count_;

        auto id = static_cast<CallbackId>(std::distance(entries_.begin(), it));
        return CallbackToken(this, id);
    }

    /**
     * @brief Invoke a callback by ID.
     *
     * @param id Callback ID
     * @return Callback result, or 0 if invalid ID
     */
    [[nodiscard]] uint32_t invoke(CallbackId id) const noexcept {
        if (id >= MaxCallbacks || !entries_[id].active) {
            return 0;
        }
        return entries_[id].handler(entries_[id].userdata);
    }

    /**
     * @brief Check if callback ID is valid and active.
     */
    [[nodiscard]] bool is_valid(CallbackId id) const noexcept {
        return id < MaxCallbacks && entries_[id].active;
    }

    /**
     * @brief Get callback description.
     */
    [[nodiscard]] std::optional<std::string_view> description(CallbackId id) const noexcept {
        if (id >= MaxCallbacks || !entries_[id].active) {
            return std::nullopt;
        }
        return std::string_view(entries_[id].description);
    }

    /**
     * @brief Get callback entry (for debugging).
     */
    [[nodiscard]] const CallbackEntry* get_entry(CallbackId id) const noexcept {
        if (id >= MaxCallbacks || !entries_[id].active) {
            return nullptr;
        }
        return &entries_[id];
    }

    /**
     * @brief Get number of active callbacks.
     */
    [[nodiscard]] size_t active_count() const noexcept {
        return active_count_;
    }

    /**
     * @brief Get maximum number of callbacks.
     */
    [[nodiscard]] static constexpr size_t max_callbacks() noexcept {
        return MaxCallbacks;
    }

private:
    friend class CallbackToken;

    void unregister(CallbackId id) noexcept {
        if (id < MaxCallbacks && entries_[id].active) {
            entries_[id] = CallbackEntry{};
            --active_count_;
        }
    }

    std::array<CallbackEntry, MaxCallbacks> entries_{};
    size_t active_count_ = 0;
};

// Inline implementation of CallbackToken::release
inline void CallbackToken::release() {
    if (registry_) {
        registry_->unregister(id_);
        registry_ = nullptr;
    }
}

} // namespace aibox
