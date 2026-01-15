/**
 * @file handle_registry.h
 * @brief Generation-based handle validation for FFI safety.
 *
 * Provides a handle registry that uses generation counters to detect
 * use-after-free bugs. Each handle slot has a generation counter that
 * is incremented when the handle is freed, invalidating any dangling
 * references.
 */

#pragma once

#include <gsl-lite/gsl-lite.hpp>
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <mutex>
#include <optional>
#include <ranges>
#include <typeindex>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// Handle Types
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Type tag for handle validation.
 *
 * Each handle type has a unique tag to prevent type confusion attacks.
 */
enum class HandleType : uint8_t {
    Invalid = 0,        ///< Uninitialized or freed handle
    Emulator,           ///< Emulator instance (MachineContext)
    Subscription,       ///< Event subscription
    MemoryView,         ///< Memory view handle
    EventBatch          ///< Batched event data
};

/**
 * @brief Get string representation of HandleType.
 */
[[nodiscard]] constexpr const char* to_string(HandleType type) noexcept {
    switch (type) {
        case HandleType::Invalid:       return "Invalid";
        case HandleType::Emulator:      return "Emulator";
        case HandleType::Subscription:  return "Subscription";
        case HandleType::MemoryView:    return "MemoryView";
        case HandleType::EventBatch:    return "EventBatch";
    }
    return "Unknown";
}

/**
 * @brief Handle validation status codes.
 */
enum class HandleStatus : int8_t {
    Valid = 0,                  ///< Handle is valid
    Null = -1,                  ///< Handle is null
    InvalidGeneration = -2,     ///< Generation mismatch (use-after-free)
    WrongType = -3,             ///< Type tag doesn't match
    Destroyed = -4,             ///< Slot was freed
    OutOfBounds = -5            ///< Slot index out of range
};

/**
 * @brief Get string representation of HandleStatus.
 */
[[nodiscard]] constexpr const char* to_string(HandleStatus status) noexcept {
    switch (status) {
        case HandleStatus::Valid:             return "Valid";
        case HandleStatus::Null:              return "Null";
        case HandleStatus::InvalidGeneration: return "InvalidGeneration";
        case HandleStatus::WrongType:         return "WrongType";
        case HandleStatus::Destroyed:         return "Destroyed";
        case HandleStatus::OutOfBounds:       return "OutOfBounds";
    }
    return "Unknown";
}

// ─────────────────────────────────────────────────────────────────────────────
// Packed Handle
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Packed handle format for FFI.
 *
 * The handle is packed into a 32-bit value:
 * - Bits 0-19: Slot index (max 1M handles)
 * - Bits 20-31: Generation (wraps every 4096 allocations per slot)
 *
 * This allows handles to be passed as opaque values through the FFI
 * boundary while still enabling use-after-free detection.
 */
struct PackedHandle {
    uint32_t value;

    static constexpr uint32_t SlotBits = 20;
    static constexpr uint32_t GenerationBits = 12;
    static constexpr uint32_t SlotMask = (1u << SlotBits) - 1;
    static constexpr uint32_t GenerationMask = (1u << GenerationBits) - 1;
    static constexpr uint32_t MaxSlots = 1u << SlotBits;       // 1,048,576
    static constexpr uint32_t MaxGeneration = 1u << GenerationBits; // 4,096

    /**
     * @brief Create a packed handle from slot and generation.
     */
    static constexpr PackedHandle create(uint32_t slot, uint32_t generation) noexcept {
        return PackedHandle{
            (slot & SlotMask) | ((generation & GenerationMask) << SlotBits)
        };
    }

    /**
     * @brief Create from opaque pointer (FFI).
     */
    static PackedHandle from_opaque(void* opaque) noexcept {
        PackedHandle h{0};
        if (opaque) {
            std::memcpy(&h.value, &opaque, sizeof(h.value));
        }
        return h;
    }

    /**
     * @brief Convert to opaque pointer for FFI.
     */
    [[nodiscard]] void* to_opaque() const noexcept {
        void* result = nullptr;
        std::memcpy(&result, &value, sizeof(value));
        return result;
    }

    /**
     * @brief Get slot index.
     */
    [[nodiscard]] constexpr uint32_t slot() const noexcept {
        return value & SlotMask;
    }

    /**
     * @brief Get generation.
     */
    [[nodiscard]] constexpr uint32_t generation() const noexcept {
        return (value >> SlotBits) & GenerationMask;
    }

    /**
     * @brief Check if handle is null (all zeros).
     */
    [[nodiscard]] constexpr bool is_null() const noexcept {
        return value == 0;
    }

    [[nodiscard]] constexpr bool operator==(const PackedHandle& other) const noexcept {
        return value == other.value;
    }

    [[nodiscard]] constexpr bool operator!=(const PackedHandle& other) const noexcept {
        return value != other.value;
    }
};

static_assert(sizeof(PackedHandle) == 4, "PackedHandle must be 4 bytes");

// ─────────────────────────────────────────────────────────────────────────────
// Handle Slot
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Internal handle slot storage.
 *
 * Each slot contains the object pointer, type information, and
 * generation counter for use-after-free detection.
 */
struct HandleSlot {
    void*           object_ptr;     ///< Pointer to managed object
    std::type_index type_info;      ///< RTTI type for validation
    HandleType      type_tag;       ///< Handle type tag
    uint32_t        generation;     ///< Generation counter
    bool            in_use;         ///< Whether slot is currently allocated

    HandleSlot() noexcept
        : object_ptr(nullptr)
        , type_info(typeid(void))
        , type_tag(HandleType::Invalid)
        , generation(1)  // Start at 1 so null handle (gen=0) is invalid
        , in_use(false)
    {}
};

// ─────────────────────────────────────────────────────────────────────────────
// Handle Registry
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Thread-safe handle registry with generation-based validation.
 *
 * Provides allocation, validation, and retrieval of handles with
 * automatic use-after-free detection. All operations are thread-safe.
 *
 * Design notes:
 * - Uses fixed-size array for O(1) lookup
 * - Linear search for allocation (cold path)
 * - Generation counter prevents use-after-free
 * - Type tag prevents type confusion
 *
 * Example:
 * @code
 *   HandleRegistry registry;
 *
 *   // Allocate a handle
 *   auto handle = registry.allocate<MyObject>(&obj, HandleType::Emulator);
 *   if (!handle.is_null()) {
 *       // Use the handle
 *       auto obj_opt = registry.get<MyObject>(handle, HandleType::Emulator);
 *       if (obj_opt) {
 *           obj_opt.value()->do_something();
 *       }
 *
 *       // Free when done
 *       registry.free(handle);
 *   }
 * @endcode
 */
class HandleRegistry {
public:
    static constexpr size_t MaxHandles = 1024;

    HandleRegistry() = default;

    // Non-copyable (owns slot state)
    HandleRegistry(const HandleRegistry&) = delete;
    HandleRegistry& operator=(const HandleRegistry&) = delete;

    // Non-movable (contains mutex)
    HandleRegistry(HandleRegistry&&) = delete;
    HandleRegistry& operator=(HandleRegistry&&) = delete;

    /**
     * @brief Allocate a new handle for an object.
     *
     * @tparam T Object type (used for type validation)
     * @param object Pointer to object (must remain valid until freed)
     * @param type Handle type tag
     * @return Packed handle, or null handle if object is null, type is Invalid, or registry is full
     */
    template<typename T>
    [[nodiscard]] PackedHandle allocate(T* object, HandleType type) {
        if (!object || type == HandleType::Invalid) {
            return PackedHandle{0};
        }

        std::lock_guard lock(mutex_);

        auto it = std::ranges::find_if(slots_, [](const HandleSlot& s) { return !s.in_use; });
        if (it == slots_.end()) {
            return PackedHandle{0}; // Registry full
        }

        it->object_ptr = object;
        it->type_info = std::type_index(typeid(T));
        it->type_tag = type;
        it->in_use = true;
        // Note: generation was already incremented when slot was freed

        ++active_count_;

        auto i = static_cast<uint32_t>(std::distance(slots_.begin(), it));
        return PackedHandle::create(i, it->generation & PackedHandle::GenerationMask);
    }

    /**
     * @brief Free a handle (increments generation to invalidate).
     *
     * @param handle Handle to free
     * @return true if freed, false if handle was invalid
     */
    bool free(PackedHandle handle) {
        if (handle.is_null()) {
            return false;
        }

        std::lock_guard lock(mutex_);

        uint32_t slot_idx = handle.slot();
        if (slot_idx >= MaxHandles) {
            return false;
        }

        auto& slot = slots_[slot_idx];
        if (!slot.in_use) {
            return false;
        }

        // Check generation matches
        uint32_t expected_gen = slot.generation & PackedHandle::GenerationMask;
        if (handle.generation() != expected_gen) {
            return false;
        }

        // Free the slot
        slot.object_ptr = nullptr;
        slot.type_info = std::type_index(typeid(void));
        slot.type_tag = HandleType::Invalid;
        slot.in_use = false;
        slot.generation++; // Invalidate any existing handles to this slot

        --active_count_;

        return true;
    }

    /**
     * @brief Validate and retrieve object from handle.
     *
     * @tparam T Expected object type
     * @param handle Handle to validate
     * @param expected_type Expected handle type
     * @return Object pointer if valid, nullopt otherwise
     */
    template<typename T>
    [[nodiscard]] std::optional<T*> get(PackedHandle handle, HandleType expected_type) {
        auto status = validate_impl(handle, expected_type, std::type_index(typeid(T)));
        if (status != HandleStatus::Valid) {
            return std::nullopt;
        }

        std::lock_guard lock(mutex_);
        return static_cast<T*>(slots_[handle.slot()].object_ptr);
    }

    /**
     * @brief Validate and retrieve const object from handle.
     */
    template<typename T>
    [[nodiscard]] std::optional<const T*> get_const(PackedHandle handle, HandleType expected_type) const {
        auto status = const_cast<HandleRegistry*>(this)->validate_impl(
            handle, expected_type, std::type_index(typeid(T)));
        if (status != HandleStatus::Valid) {
            return std::nullopt;
        }

        std::lock_guard lock(mutex_);
        return static_cast<const T*>(slots_[handle.slot()].object_ptr);
    }

    /**
     * @brief Validate a handle without retrieving the object.
     *
     * @param handle Handle to validate
     * @param expected_type Expected handle type (or Invalid to skip type check)
     * @return Validation status
     */
    [[nodiscard]] HandleStatus validate(PackedHandle handle,
                                        HandleType expected_type = HandleType::Invalid) const {
        return const_cast<HandleRegistry*>(this)->validate_impl(
            handle, expected_type, std::type_index(typeid(void)));
    }

    /**
     * @brief Get number of active handles.
     */
    [[nodiscard]] size_t active_count() const noexcept {
        std::lock_guard lock(mutex_);
        return active_count_;
    }

    /**
     * @brief Check if registry is full.
     */
    [[nodiscard]] bool is_full() const noexcept {
        std::lock_guard lock(mutex_);
        return active_count_ >= MaxHandles;
    }

    /**
     * @brief Get maximum number of handles.
     */
    [[nodiscard]] static constexpr size_t max_handles() noexcept {
        return MaxHandles;
    }

private:
    HandleStatus validate_impl(PackedHandle handle,
                               HandleType expected_type,
                               std::type_index expected_type_info) {
        if (handle.is_null()) {
            return HandleStatus::Null;
        }

        uint32_t slot_idx = handle.slot();
        if (slot_idx >= MaxHandles) {
            return HandleStatus::OutOfBounds;
        }

        std::lock_guard lock(mutex_);

        const auto& slot = slots_[slot_idx];
        if (!slot.in_use) {
            return HandleStatus::Destroyed;
        }

        // Check generation matches
        uint32_t expected_gen = slot.generation & PackedHandle::GenerationMask;
        if (handle.generation() != expected_gen) {
            return HandleStatus::InvalidGeneration;
        }

        // Check type tag if specified
        if (expected_type != HandleType::Invalid && slot.type_tag != expected_type) {
            return HandleStatus::WrongType;
        }

        // Check RTTI type if not void
        if (expected_type_info != std::type_index(typeid(void)) &&
            slot.type_info != expected_type_info) {
            return HandleStatus::WrongType;
        }

        return HandleStatus::Valid;
    }

    mutable std::mutex mutex_;
    std::array<HandleSlot, MaxHandles> slots_{};
    size_t active_count_{0};
};

} // namespace legends
