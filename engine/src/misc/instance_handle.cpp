/**
 * @file instance_handle.cpp
 * @brief Implementation of misuse-resilient handle system.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/instance_handle.h"

#include <algorithm>
#include <ranges>

// ═══════════════════════════════════════════════════════════════════════════════
// C API Implementation
// ═══════════════════════════════════════════════════════════════════════════════

extern "C" {

const char* dosbox_handle_error_str(dosbox_handle_error error) {
    switch (error) {
        case DOSBOX_HANDLE_OK:              return "Ok";
        case DOSBOX_HANDLE_NULL:            return "Handle is null";
        case DOSBOX_HANDLE_INVALID_GEN:     return "Handle generation mismatch (use-after-free)";
        case DOSBOX_HANDLE_DESTROYED:       return "Handle was destroyed";
        case DOSBOX_HANDLE_WRONG_STATE:     return "Operation not valid in current state";
        case DOSBOX_HANDLE_DOUBLE_DESTROY:  return "Handle already destroyed";
        case DOSBOX_HANDLE_NOT_INITIALIZED: return "Instance not initialized";
        case DOSBOX_HANDLE_ALREADY_RUNNING: return "Instance already running";
        case DOSBOX_HANDLE_NOT_RUNNING:     return "Instance not running";
        case DOSBOX_HANDLE_REGISTRY_FULL:   return "Instance registry full";
    }
    return "Unknown error";
}

const char* dosbox_instance_state_str(dosbox_instance_state state) {
    return dosbox::to_string(static_cast<dosbox::InstanceState>(state));
}

dosbox_handle_error dosbox_validate_handle(dosbox_handle_t handle) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    return static_cast<dosbox_handle_error>(
        dosbox::get_instance_registry().validate(h));
}

dosbox_instance_state dosbox_get_state(dosbox_handle_t handle) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    auto state = dosbox::get_instance_registry().get_state(h);
    if (!state) {
        return DOSBOX_STATE_INVALID;
    }
    return static_cast<dosbox_instance_state>(state.value());
}

int dosbox_is_valid_transition(dosbox_instance_state from, dosbox_instance_state to) {
    return dosbox::is_valid_transition(
        static_cast<dosbox::InstanceState>(from),
        static_cast<dosbox::InstanceState>(to)) ? 1 : 0;
}

} // extern "C"

// ═══════════════════════════════════════════════════════════════════════════════
// C++ Implementation
// ═══════════════════════════════════════════════════════════════════════════════

namespace dosbox {

// ─────────────────────────────────────────────────────────────────────────────
// InstanceRegistry Implementation
// ─────────────────────────────────────────────────────────────────────────────

Result<InstanceHandle> InstanceRegistry::allocate(void* context) {
    std::lock_guard lock(mutex_);

    // Find free slot
    auto it = std::ranges::find_if(slots_, [](const InstanceSlot& s) {
        return !s.in_use;
    });

    if (it == slots_.end()) {
        return Err(Error(ErrorCode::ResourceExhausted, "Instance registry full"));
    }

    // Initialize slot
    it->context_ptr = context;
    it->state = InstanceState::Created;
    it->in_use = true;
    // Note: generation was already incremented when slot was freed

    ++active_count_;

    auto slot_idx = static_cast<uint32_t>(std::distance(slots_.begin(), it));
    return Ok(InstanceHandle::create(slot_idx, it->generation));
}

Result<void> InstanceRegistry::destroy(InstanceHandle handle) {
    if (handle.is_null()) {
        return Err(Error(ErrorCode::InvalidHandle, "Null handle"));
    }

    std::lock_guard lock(mutex_);

    uint32_t slot_idx = handle.slot();
    if (slot_idx >= MaxInstances) {
        return Err(Error(ErrorCode::InvalidHandle, "Handle out of bounds"));
    }

    auto& slot = slots_[slot_idx];

    // Check if slot is in use
    if (!slot.in_use) {
        return Err(Error(ErrorCode::InvalidHandle, "Double destroy attempt"));
    }

    // Check generation matches
    if (handle.generation() != slot.generation) {
        return Err(Error(ErrorCode::InvalidHandle, "Generation mismatch (use-after-free)"));
    }

    // Check state allows destruction
    if (slot.state != InstanceState::Shutdown &&
        slot.state != InstanceState::Failed &&
        slot.state != InstanceState::Created) {
        return Err(Error(ErrorCode::InvalidState,
            std::string("Cannot destroy in state: ") + to_string(slot.state) +
            ". Must shutdown first."));
    }

    // Free the slot
    slot.context_ptr = nullptr;
    slot.state = InstanceState::Invalid;
    slot.in_use = false;
    slot.generation++;  // Invalidate any existing handles

    --active_count_;

    return Ok();
}

HandleError InstanceRegistry::validate(InstanceHandle handle) const {
    if (handle.is_null()) {
        return HandleError::Null;
    }

    uint32_t slot_idx = handle.slot();
    if (slot_idx >= MaxInstances) {
        return HandleError::Destroyed;
    }

    std::lock_guard lock(mutex_);

    const auto& slot = slots_[slot_idx];
    if (!slot.in_use) {
        return HandleError::Destroyed;
    }

    if (handle.generation() != slot.generation) {
        return HandleError::InvalidGeneration;
    }

    return HandleError::Ok;
}

std::optional<InstanceState> InstanceRegistry::get_state(InstanceHandle handle) const {
    if (validate(handle) != HandleError::Ok) {
        return std::nullopt;
    }

    std::lock_guard lock(mutex_);
    return slots_[handle.slot()].state;
}

Result<void> InstanceRegistry::transition(InstanceHandle handle, InstanceState new_state) {
    auto error = validate(handle);
    if (error != HandleError::Ok) {
        return Err(Error(ErrorCode::InvalidHandle, to_string(error)));
    }

    std::lock_guard lock(mutex_);

    auto& slot = slots_[handle.slot()];
    InstanceState current = slot.state;

    if (!is_valid_transition(current, new_state)) {
        return Err(Error(ErrorCode::InvalidState,
            std::string("Invalid transition: ") + to_string(current) +
            " -> " + to_string(new_state)));
    }

    slot.state = new_state;
    return Ok();
}

std::optional<void*> InstanceRegistry::get_context(InstanceHandle handle) const {
    if (validate(handle) != HandleError::Ok) {
        return std::nullopt;
    }

    std::lock_guard lock(mutex_);
    return slots_[handle.slot()].context_ptr;
}

Result<void> InstanceRegistry::set_context(InstanceHandle handle, void* context) {
    auto error = validate(handle);
    if (error != HandleError::Ok) {
        return Err(Error(ErrorCode::InvalidHandle, to_string(error)));
    }

    std::lock_guard lock(mutex_);
    slots_[handle.slot()].context_ptr = context;
    return Ok();
}

size_t InstanceRegistry::active_count() const noexcept {
    std::lock_guard lock(mutex_);
    return active_count_;
}

bool InstanceRegistry::is_full() const noexcept {
    std::lock_guard lock(mutex_);
    return active_count_ >= MaxInstances;
}

// ─────────────────────────────────────────────────────────────────────────────
// Global Registry
// ─────────────────────────────────────────────────────────────────────────────

InstanceRegistry& get_instance_registry() {
    static InstanceRegistry registry;
    return registry;
}

} // namespace dosbox
