/**
 * @file engine_services.h
 * @brief Formal service contract between legends_core and aibox_core
 *
 * This header provides:
 * 1. Re-export of the public C API from dosbox_library.h
 * 2. C++ service interface types for dependency injection
 * 3. ServiceTable struct for testing and mocking
 *
 * Module: aibox_core (public API)
 *
 * DESIGN DECISIONS (Sprint 3):
 * - Single integration point for legends_core → aibox_core dependency
 * - Pure virtual interfaces allow for test doubles/mocks
 * - ServiceTable enables dependency injection pattern
 * - C API remains the stable ABI boundary
 *
 * USAGE:
 *   // Production: use default services
 *   #include "dosbox/engine_services.h"
 *   auto result = dosbox_lib_create(&config, &handle);
 *
 *   // Testing: inject mock services
 *   dosbox::EngineServiceTable services;
 *   services.create = [](auto*, auto*) { return DOSBOX_LIB_OK; };
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_ENGINE_SERVICES_H
#define DOSBOX_ENGINE_SERVICES_H

// Re-export the C API
#include "dosbox_library.h"

// Additional public headers from aibox_core
#include "error_mapping.h"
#include "state_hash.h"

#ifdef __cplusplus

#include <functional>
#include <memory>
#include <string>

namespace dosbox {

/**
 * @brief C++ function types matching the C API.
 *
 * These allow for type-safe function pointers and std::function usage.
 */
namespace api {

using GetVersionFn = dosbox_lib_error_t (*)(uint32_t*, uint32_t*, uint32_t*);
using CreateFn = dosbox_lib_error_t (*)(const dosbox_lib_config_t*, dosbox_lib_handle_t*);
using InitFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t);
using DestroyFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t);
using ResetFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t);
using StepMsFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, uint32_t, dosbox_lib_step_result_t*);
using StepCyclesFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, uint64_t, dosbox_lib_step_result_t*);
using GetEmuTimeFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, uint64_t*);
using GetTotalCyclesFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, uint64_t*);
using GetStateHashFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, uint8_t[32]);
using SaveStateFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, void*, size_t, size_t*);
using LoadStateFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, const void*, size_t);
using GetLastErrorFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, char*, size_t, size_t*);
using SetLogCallbackFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, dosbox_lib_log_callback_t, void*);
using InjectKeyFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, uint8_t, int, int);
using InjectMouseFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, int16_t, int16_t, uint8_t);
using GetPicStateFn = dosbox_lib_error_t (*)(dosbox_lib_handle_t, dosbox_lib_pic_state_t*);

} // namespace api

/**
 * @brief Service table for dependency injection.
 *
 * This table holds function pointers to all engine services.
 * By default, it points to the real implementations.
 * For testing, individual functions can be replaced with mocks.
 *
 * Example:
 *   EngineServiceTable services = EngineServiceTable::defaults();
 *   services.step_ms = mock_step_ms;  // Inject mock
 */
struct EngineServiceTable {
    // Lifecycle
    api::GetVersionFn get_version;
    api::CreateFn create;
    api::InitFn init;
    api::DestroyFn destroy;
    api::ResetFn reset;

    // Stepping
    api::StepMsFn step_ms;
    api::StepCyclesFn step_cycles;
    api::GetEmuTimeFn get_emu_time;
    api::GetTotalCyclesFn get_total_cycles;

    // State
    api::GetStateHashFn get_state_hash;
    api::SaveStateFn save_state;
    api::LoadStateFn load_state;

    // Error handling
    api::GetLastErrorFn get_last_error;
    api::SetLogCallbackFn set_log_callback;

    // Input injection
    api::InjectKeyFn inject_key;
    api::InjectMouseFn inject_mouse;

    // Hardware state
    api::GetPicStateFn get_pic_state;

    /**
     * @brief Create a service table with default (real) implementations.
     */
    static EngineServiceTable defaults() noexcept {
        return EngineServiceTable{
            // Lifecycle
            dosbox_lib_get_version,
            dosbox_lib_create,
            dosbox_lib_init,
            dosbox_lib_destroy,
            dosbox_lib_reset,
            // Stepping
            dosbox_lib_step_ms,
            dosbox_lib_step_cycles,
            dosbox_lib_get_emu_time,
            dosbox_lib_get_total_cycles,
            // State
            dosbox_lib_get_state_hash,
            dosbox_lib_save_state,
            dosbox_lib_load_state,
            // Error handling
            dosbox_lib_get_last_error,
            dosbox_lib_set_log_callback,
            // Input injection
            dosbox_lib_inject_key,
            dosbox_lib_inject_mouse,
            // Hardware state
            dosbox_lib_get_pic_state
        };
    }

    /**
     * @brief Create a null service table (all functions are nullptr).
     *
     * Useful for testing when you only want to implement specific functions.
     */
    static EngineServiceTable null_table() noexcept {
        return EngineServiceTable{
            nullptr, nullptr, nullptr, nullptr, nullptr,
            nullptr, nullptr, nullptr, nullptr,
            nullptr, nullptr, nullptr,
            nullptr, nullptr,
            nullptr, nullptr,
            nullptr
        };
    }
};

/**
 * @brief RAII wrapper for engine handle.
 *
 * Automatically destroys the handle when going out of scope.
 * Provides a clean C++ interface to the engine.
 */
class EngineHandle {
public:
    EngineHandle() noexcept = default;

    explicit EngineHandle(dosbox_lib_handle_t h) noexcept : handle_(h) {}

    ~EngineHandle() {
        if (handle_) {
            dosbox_lib_destroy(handle_);
        }
    }

    // Move-only
    EngineHandle(EngineHandle&& other) noexcept : handle_(other.handle_) {
        other.handle_ = nullptr;
    }

    EngineHandle& operator=(EngineHandle&& other) noexcept {
        if (this != &other) {
            if (handle_) {
                dosbox_lib_destroy(handle_);
            }
            handle_ = other.handle_;
            other.handle_ = nullptr;
        }
        return *this;
    }

    // Non-copyable
    EngineHandle(const EngineHandle&) = delete;
    EngineHandle& operator=(const EngineHandle&) = delete;

    /** Get the raw handle */
    dosbox_lib_handle_t get() const noexcept { return handle_; }

    /** Check if handle is valid */
    explicit operator bool() const noexcept { return handle_ != nullptr; }

    /** Release ownership of the handle */
    dosbox_lib_handle_t release() noexcept {
        auto h = handle_;
        handle_ = nullptr;
        return h;
    }

    /** Reset with a new handle */
    void reset(dosbox_lib_handle_t h = nullptr) noexcept {
        if (handle_) {
            dosbox_lib_destroy(handle_);
        }
        handle_ = h;
    }

private:
    dosbox_lib_handle_t handle_ = nullptr;
};

/**
 * @brief Create an engine instance with RAII management.
 *
 * @param config Configuration (nullptr for defaults)
 * @param error_out Optional error code output
 * @return EngineHandle (check bool conversion for validity)
 */
inline EngineHandle create_engine(
    const dosbox_lib_config_t* config = nullptr,
    dosbox_lib_error_t* error_out = nullptr
) {
    dosbox_lib_handle_t handle = nullptr;
    auto err = dosbox_lib_create(config, &handle);
    if (error_out) *error_out = err;
    return EngineHandle(err == DOSBOX_LIB_OK ? handle : nullptr);
}

} // namespace dosbox

#endif // __cplusplus

#endif /* DOSBOX_ENGINE_SERVICES_H */
