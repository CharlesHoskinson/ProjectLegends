/**
 * @file instance_handle.h
 * @brief Misuse-resilient handle system for DOSBox instances.
 *
 * Implements PR #8 requirements:
 * - State machine: Created → Initialized → Running → Shutdown → Destroyed
 * - Explicit errors for: null handle, double destroy, wrong state
 * - Generation counters to detect use-after-free
 *
 * Usage (C API):
 *   dosbox_handle_t handle = dosbox_create(&config);
 *   if (dosbox_init(handle) == DOSBOX_OK) {
 *       dosbox_run(handle);
 *       // ... use handle ...
 *       dosbox_shutdown(handle);
 *   }
 *   dosbox_destroy(handle);
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_INSTANCE_HANDLE_H
#define DOSBOX_INSTANCE_HANDLE_H

#include <cstdint>

#ifdef __cplusplus
extern "C" {
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// Handle Types (C API)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Opaque handle to a DOSBox instance.
 *
 * The handle is packed with generation counter for use-after-free detection.
 * Never dereference directly - always use API functions.
 */
typedef void* dosbox_handle_t;

/**
 * @brief Instance lifecycle states.
 */
typedef enum dosbox_instance_state {
    DOSBOX_STATE_INVALID = 0,       ///< Handle is invalid/destroyed
    DOSBOX_STATE_CREATED = 1,       ///< Instance created, not initialized
    DOSBOX_STATE_INITIALIZED = 2,   ///< Initialized, ready to run
    DOSBOX_STATE_RUNNING = 3,       ///< Currently executing
    DOSBOX_STATE_PAUSED = 4,        ///< Paused (can resume)
    DOSBOX_STATE_SHUTDOWN = 5,      ///< Shutdown, awaiting destroy
    DOSBOX_STATE_FAILED = 6         ///< Fatal error occurred
} dosbox_instance_state;

/**
 * @brief Handle validation error codes.
 */
typedef enum dosbox_handle_error {
    DOSBOX_HANDLE_OK = 0,                   ///< Handle is valid
    DOSBOX_HANDLE_NULL = -1,                ///< Handle is null
    DOSBOX_HANDLE_INVALID_GEN = -2,         ///< Generation mismatch (use-after-free)
    DOSBOX_HANDLE_DESTROYED = -3,           ///< Handle was destroyed
    DOSBOX_HANDLE_WRONG_STATE = -4,         ///< Operation not valid in current state
    DOSBOX_HANDLE_DOUBLE_DESTROY = -5,      ///< Attempted to destroy twice
    DOSBOX_HANDLE_NOT_INITIALIZED = -6,     ///< Must initialize first
    DOSBOX_HANDLE_ALREADY_RUNNING = -7,     ///< Already in running state
    DOSBOX_HANDLE_NOT_RUNNING = -8,         ///< Must be running for this operation
    DOSBOX_HANDLE_REGISTRY_FULL = -9        ///< Cannot allocate more handles
} dosbox_handle_error;

/**
 * @brief Get string description of handle error.
 */
const char* dosbox_handle_error_str(dosbox_handle_error error);

/**
 * @brief Get string description of instance state.
 */
const char* dosbox_instance_state_str(dosbox_instance_state state);

/**
 * @brief Validate a handle without performing any operation.
 *
 * @param handle Handle to validate
 * @return DOSBOX_HANDLE_OK if valid, error code otherwise
 */
dosbox_handle_error dosbox_validate_handle(dosbox_handle_t handle);

/**
 * @brief Get current state of an instance.
 *
 * @param handle Instance handle
 * @return Current state, or DOSBOX_STATE_INVALID if handle is invalid
 */
dosbox_instance_state dosbox_get_state(dosbox_handle_t handle);

/**
 * @brief Check if a state transition is valid.
 *
 * @param from Current state
 * @param to Desired state
 * @return 1 if transition is valid, 0 otherwise
 */
int dosbox_is_valid_transition(dosbox_instance_state from, dosbox_instance_state to);

#ifdef __cplusplus
} /* extern "C" */
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C++ API
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef __cplusplus

#include "dosbox/error_model.h"
#include <array>
#include <atomic>
#include <cstring>
#include <mutex>
#include <optional>
#include <string_view>

namespace dosbox {

// ─────────────────────────────────────────────────────────────────────────────
// Instance State Machine
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Instance lifecycle state (C++ enum class wrapper).
 */
enum class InstanceState : int8_t {
    Invalid = DOSBOX_STATE_INVALID,
    Created = DOSBOX_STATE_CREATED,
    Initialized = DOSBOX_STATE_INITIALIZED,
    Running = DOSBOX_STATE_RUNNING,
    Paused = DOSBOX_STATE_PAUSED,
    Shutdown = DOSBOX_STATE_SHUTDOWN,
    Failed = DOSBOX_STATE_FAILED
};

/**
 * @brief Get string name of state.
 */
[[nodiscard]] constexpr const char* to_string(InstanceState state) noexcept {
    switch (state) {
        case InstanceState::Invalid:     return "Invalid";
        case InstanceState::Created:     return "Created";
        case InstanceState::Initialized: return "Initialized";
        case InstanceState::Running:     return "Running";
        case InstanceState::Paused:      return "Paused";
        case InstanceState::Shutdown:    return "Shutdown";
        case InstanceState::Failed:      return "Failed";
    }
    return "Unknown";
}

/**
 * @brief Check if a state transition is valid.
 *
 * Valid transitions:
 *   Created → Initialized
 *   Created → Failed
 *   Initialized → Running
 *   Initialized → Shutdown
 *   Initialized → Failed
 *   Running → Paused
 *   Running → Shutdown
 *   Running → Failed
 *   Paused → Running
 *   Paused → Shutdown
 *   Paused → Failed
 *   Shutdown → Invalid (destroy)
 *   Failed → Shutdown
 *   Failed → Invalid (destroy)
 */
[[nodiscard]] constexpr bool is_valid_transition(InstanceState from, InstanceState to) noexcept {
    switch (from) {
        case InstanceState::Created:
            return to == InstanceState::Initialized || to == InstanceState::Failed;

        case InstanceState::Initialized:
            return to == InstanceState::Running ||
                   to == InstanceState::Shutdown ||
                   to == InstanceState::Failed;

        case InstanceState::Running:
            return to == InstanceState::Paused ||
                   to == InstanceState::Shutdown ||
                   to == InstanceState::Failed;

        case InstanceState::Paused:
            return to == InstanceState::Running ||
                   to == InstanceState::Shutdown ||
                   to == InstanceState::Failed;

        case InstanceState::Shutdown:
            return to == InstanceState::Invalid;

        case InstanceState::Failed:
            return to == InstanceState::Shutdown || to == InstanceState::Invalid;

        case InstanceState::Invalid:
            return false;  // Can't transition from Invalid
    }
    return false;
}

// ─────────────────────────────────────────────────────────────────────────────
// Handle Error Codes
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Handle-specific error codes.
 */
enum class HandleError : int8_t {
    Ok = DOSBOX_HANDLE_OK,
    Null = DOSBOX_HANDLE_NULL,
    InvalidGeneration = DOSBOX_HANDLE_INVALID_GEN,
    Destroyed = DOSBOX_HANDLE_DESTROYED,
    WrongState = DOSBOX_HANDLE_WRONG_STATE,
    DoubleDestroy = DOSBOX_HANDLE_DOUBLE_DESTROY,
    NotInitialized = DOSBOX_HANDLE_NOT_INITIALIZED,
    AlreadyRunning = DOSBOX_HANDLE_ALREADY_RUNNING,
    NotRunning = DOSBOX_HANDLE_NOT_RUNNING,
    RegistryFull = DOSBOX_HANDLE_REGISTRY_FULL
};

/**
 * @brief Get string name of handle error.
 */
[[nodiscard]] constexpr const char* to_string(HandleError error) noexcept {
    switch (error) {
        case HandleError::Ok:                return "Ok";
        case HandleError::Null:              return "Null";
        case HandleError::InvalidGeneration: return "InvalidGeneration";
        case HandleError::Destroyed:         return "Destroyed";
        case HandleError::WrongState:        return "WrongState";
        case HandleError::DoubleDestroy:     return "DoubleDestroy";
        case HandleError::NotInitialized:    return "NotInitialized";
        case HandleError::AlreadyRunning:    return "AlreadyRunning";
        case HandleError::NotRunning:        return "NotRunning";
        case HandleError::RegistryFull:      return "RegistryFull";
    }
    return "Unknown";
}

// ─────────────────────────────────────────────────────────────────────────────
// Packed Handle
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Packed handle with generation counter.
 *
 * Layout (32 bits):
 * - Bits 0-15:  Slot index (max 65536 handles)
 * - Bits 16-31: Generation counter
 */
struct InstanceHandle {
    uint32_t value;

    static constexpr uint32_t SlotBits = 16;
    static constexpr uint32_t GenerationBits = 16;
    static constexpr uint32_t SlotMask = (1u << SlotBits) - 1;
    static constexpr uint32_t GenerationMask = (1u << GenerationBits) - 1;
    static constexpr uint32_t MaxSlots = 1u << SlotBits;

    /**
     * @brief Create handle from slot and generation.
     */
    [[nodiscard]] static constexpr InstanceHandle create(uint32_t slot, uint32_t gen) noexcept {
        return InstanceHandle{(slot & SlotMask) | ((gen & GenerationMask) << SlotBits)};
    }

    /**
     * @brief Create from opaque C handle.
     */
    [[nodiscard]] static InstanceHandle from_opaque(dosbox_handle_t opaque) noexcept {
        InstanceHandle h{0};
        if (opaque) {
            std::memcpy(&h.value, &opaque, sizeof(h.value));
        }
        return h;
    }

    /**
     * @brief Convert to opaque C handle.
     */
    [[nodiscard]] void* to_opaque() const noexcept {
        void* result = nullptr;
        std::memcpy(&result, &value, sizeof(value));
        return result;
    }

    [[nodiscard]] constexpr uint32_t slot() const noexcept {
        return value & SlotMask;
    }

    [[nodiscard]] constexpr uint32_t generation() const noexcept {
        return (value >> SlotBits) & GenerationMask;
    }

    [[nodiscard]] constexpr bool is_null() const noexcept {
        return value == 0;
    }

    [[nodiscard]] constexpr bool operator==(const InstanceHandle& other) const noexcept {
        return value == other.value;
    }

    [[nodiscard]] constexpr bool operator!=(const InstanceHandle& other) const noexcept {
        return value != other.value;
    }
};

static_assert(sizeof(InstanceHandle) == 4, "InstanceHandle must be 4 bytes");

// ─────────────────────────────────────────────────────────────────────────────
// Instance Slot
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Internal slot storing instance state.
 */
struct InstanceSlot {
    void*         context_ptr;    ///< Pointer to DOSBoxContext (opaque)
    InstanceState state;          ///< Current lifecycle state
    uint16_t      generation;     ///< Generation counter
    bool          in_use;         ///< Whether slot is allocated

    InstanceSlot() noexcept
        : context_ptr(nullptr)
        , state(InstanceState::Invalid)
        , generation(1)  // Start at 1 so null handle (gen=0) is invalid
        , in_use(false)
    {}
};

// ─────────────────────────────────────────────────────────────────────────────
// Instance Registry
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Thread-safe registry for DOSBox instances with state machine.
 *
 * Provides:
 * - Generation-based use-after-free detection
 * - State machine enforcement
 * - Explicit errors for all misuse cases
 */
class InstanceRegistry {
public:
    static constexpr size_t MaxInstances = 256;

    InstanceRegistry() = default;

    // Non-copyable, non-movable (contains mutex)
    InstanceRegistry(const InstanceRegistry&) = delete;
    InstanceRegistry& operator=(const InstanceRegistry&) = delete;
    InstanceRegistry(InstanceRegistry&&) = delete;
    InstanceRegistry& operator=(InstanceRegistry&&) = delete;

    /**
     * @brief Allocate a new instance slot.
     *
     * @param context Pointer to DOSBoxContext (can be null, set later)
     * @return Handle or error if registry full
     */
    [[nodiscard]] Result<InstanceHandle> allocate(void* context = nullptr);

    /**
     * @brief Free an instance slot (must be in Shutdown or Failed state).
     *
     * @param handle Handle to free
     * @return Ok on success, error code otherwise
     */
    [[nodiscard]] Result<void> destroy(InstanceHandle handle);

    /**
     * @brief Validate a handle.
     *
     * @param handle Handle to validate
     * @return HandleError::Ok if valid
     */
    [[nodiscard]] HandleError validate(InstanceHandle handle) const;

    /**
     * @brief Get current state of an instance.
     *
     * @param handle Instance handle
     * @return State if handle valid, nullopt otherwise
     */
    [[nodiscard]] std::optional<InstanceState> get_state(InstanceHandle handle) const;

    /**
     * @brief Attempt state transition.
     *
     * @param handle Instance handle
     * @param new_state Desired new state
     * @return Ok if transition succeeded, error otherwise
     */
    [[nodiscard]] Result<void> transition(InstanceHandle handle, InstanceState new_state);

    /**
     * @brief Require instance to be in specific state(s).
     *
     * @param handle Instance handle
     * @param required_states Allowed states (any match succeeds)
     * @return Ok if in required state, WrongState error otherwise
     */
    template<typename... States>
    [[nodiscard]] Result<void> require_state(InstanceHandle handle, States... required_states) {
        auto state_opt = get_state(handle);
        if (!state_opt) {
            return Err(Error(ErrorCode::InvalidHandle, "Invalid handle"));
        }

        InstanceState current = state_opt.value();
        bool matches = ((current == required_states) || ...);

        if (!matches) {
            return Err(Error(ErrorCode::InvalidState,
                std::string("Wrong state: ") + to_string(current)));
        }

        return Ok();
    }

    /**
     * @brief Get context pointer from handle.
     *
     * @param handle Instance handle
     * @return Context pointer if valid, nullopt otherwise
     */
    [[nodiscard]] std::optional<void*> get_context(InstanceHandle handle) const;

    /**
     * @brief Set context pointer for handle.
     *
     * @param handle Instance handle
     * @param context New context pointer
     * @return Ok on success
     */
    [[nodiscard]] Result<void> set_context(InstanceHandle handle, void* context);

    /**
     * @brief Get number of active instances.
     */
    [[nodiscard]] size_t active_count() const noexcept;

    /**
     * @brief Check if registry is full.
     */
    [[nodiscard]] bool is_full() const noexcept;

private:
    mutable std::mutex mutex_;
    std::array<InstanceSlot, MaxInstances> slots_{};
    size_t active_count_{0};
};

// ─────────────────────────────────────────────────────────────────────────────
// Global Instance Registry
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Get the global instance registry.
 *
 * In library mode, all DOSBox instances are tracked here.
 */
InstanceRegistry& get_instance_registry();

} // namespace dosbox

#endif /* __cplusplus */

#endif /* DOSBOX_INSTANCE_HANDLE_H */
