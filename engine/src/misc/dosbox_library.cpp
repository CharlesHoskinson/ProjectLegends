/**
 * @file dosbox_library.cpp
 * @brief DOSBox-X Embeddable Library Implementation (PR #22)
 *
 * Implements the stable C ABI defined in dosbox_library.h by bridging
 * to the internal DOSBoxContext infrastructure.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/dosbox_library.h"
#include "dosbox/dosbox_context.h"
#include "dosbox/error_model.h"
#include "dosbox/state_hash.h"
#include "aibox/headless_stub.h"

#include <atomic>
#include <memory>
#include <string>
#include <thread>
#include <mutex>

namespace {

// ═══════════════════════════════════════════════════════════════════════════════
// Instance State
// ═══════════════════════════════════════════════════════════════════════════════

// Single instance enforcement
std::atomic<bool> g_instance_exists{false};

// Owner thread ID for thread safety
std::thread::id g_owner_thread_id{};

// The DOSBox context instance
std::unique_ptr<dosbox::DOSBoxContext> g_context;

// Configuration stored from create
dosbox_lib_config_t g_config;

// Last error message
std::string g_last_error;

// ═══════════════════════════════════════════════════════════════════════════════
// Logging State
// ═══════════════════════════════════════════════════════════════════════════════

struct LogState {
    dosbox_lib_log_callback_t callback = nullptr;
    void* userdata = nullptr;

    void reset() {
        callback = nullptr;
        userdata = nullptr;
    }

    void log(int level, const char* message) const {
        if (callback && message) {
            callback(level, message, userdata);
        }
    }
};

LogState g_log_state;

// ═══════════════════════════════════════════════════════════════════════════════
// Time State (canonical for determinism)
// ═══════════════════════════════════════════════════════════════════════════════

struct TimeState {
    uint64_t total_cycles = 0;
    uint64_t emu_time_us = 0;
    uint32_t cycles_per_ms = 3000;

    void reset() {
        total_cycles = 0;
        emu_time_us = 0;
    }

    uint64_t cycles_to_us(uint64_t cycles) const {
        return (cycles * 1000) / cycles_per_ms;
    }

    uint64_t ms_to_cycles(uint32_t ms) const {
        return static_cast<uint64_t>(ms) * cycles_per_ms;
    }
};

TimeState g_time_state;

// ═══════════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════════

#define LIB_REQUIRE(cond, err) \
    do { if (!(cond)) return (err); } while(0)

#define LIB_CHECK_THREAD() \
    do { \
        if (g_owner_thread_id != std::this_thread::get_id()) { \
            g_last_error = "Called from non-owner thread"; \
            return DOSBOX_LIB_ERR_WRONG_THREAD; \
        } \
    } while(0)

#define LIB_LOG_INFO(msg) \
    g_log_state.log(2, msg)

#define LIB_LOG_ERROR(msg) \
    do { g_last_error = (msg); g_log_state.log(0, msg); } while(0)

} // anonymous namespace

// ═══════════════════════════════════════════════════════════════════════════════
// API Implementation
// ═══════════════════════════════════════════════════════════════════════════════

extern "C" {

dosbox_lib_error_t dosbox_lib_get_version(
    uint32_t* major,
    uint32_t* minor,
    uint32_t* patch
) {
    if (major) *major = DOSBOX_LIB_VERSION_MAJOR;
    if (minor) *minor = DOSBOX_LIB_VERSION_MINOR;
    if (patch) *patch = DOSBOX_LIB_VERSION_PATCH;
    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_create(
    const dosbox_lib_config_t* config,
    dosbox_lib_handle_t* handle_out
) {
    LIB_REQUIRE(handle_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    *handle_out = nullptr;

    // Single instance enforcement
    bool expected = false;
    if (!g_instance_exists.compare_exchange_strong(expected, true)) {
        LIB_LOG_ERROR("Instance already exists - only one per process");
        return DOSBOX_LIB_ERR_ALREADY_CREATED;
    }

    // Store owner thread
    g_owner_thread_id = std::this_thread::get_id();

    // Validate and store config
    if (config) {
        if (config->struct_size != sizeof(dosbox_lib_config_t)) {
            g_instance_exists = false;
            LIB_LOG_ERROR("Invalid config struct size");
            return DOSBOX_LIB_ERR_INVALID_CONFIG;
        }
        if (config->api_version != DOSBOX_LIB_VERSION) {
            g_instance_exists = false;
            LIB_LOG_ERROR("API version mismatch");
            return DOSBOX_LIB_ERR_VERSION_MISMATCH;
        }
        g_config = *config;
    } else {
        // Defaults
        g_config = dosbox_lib_config_t{};
        g_config.struct_size = sizeof(dosbox_lib_config_t);
        g_config.api_version = DOSBOX_LIB_VERSION;
        g_config.memory_kb = 640;
        g_config.cpu_cycles = 3000;
        g_config.deterministic = 1;
    }

    try {
        // Create DOSBox context
        g_context = std::make_unique<dosbox::DOSBoxContext>();

        // Initialize time state
        g_time_state.reset();
        g_time_state.cycles_per_ms = g_config.cpu_cycles > 0 ? g_config.cpu_cycles : 3000;

        // Return sentinel handle (actual pointer not exposed)
        *handle_out = reinterpret_cast<dosbox_lib_handle_t>(static_cast<uintptr_t>(1));
        g_last_error.clear();

        LIB_LOG_INFO("DOSBox-X library instance created");
        return DOSBOX_LIB_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        g_context.reset();
        g_instance_exists = false;
        return DOSBOX_LIB_ERR_INTERNAL;
    }
}

dosbox_lib_error_t dosbox_lib_init(dosbox_lib_handle_t handle) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    try {
        // Initialize the context
        g_context->initialize();

        // Sprint 2 Phase 1: No longer set thread-local context
        // Platform providers are wired directly through the context

        LIB_LOG_INFO("DOSBox-X library instance initialized");
        return DOSBOX_LIB_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        return DOSBOX_LIB_ERR_INTERNAL;
    }
}

dosbox_lib_error_t dosbox_lib_destroy(dosbox_lib_handle_t handle) {
    // Allow destroying null handle (no-op)
    if (handle == nullptr) {
        return DOSBOX_LIB_OK;
    }

    LIB_LOG_INFO("Destroying DOSBox-X library instance");

    // Sprint 2 Phase 1: No thread-local context to clear
    // Shutdown and destroy context directly
    if (g_context) {
        g_context->shutdown();
        g_context.reset();
    }

    // Reset state
    g_time_state.reset();
    g_instance_exists = false;
    g_owner_thread_id = std::thread::id{};
    g_last_error.clear();
    g_log_state.reset();

    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_reset(dosbox_lib_handle_t handle) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    try {
        g_context->reset();
        g_time_state.reset();
        g_last_error.clear();
        return DOSBOX_LIB_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        return DOSBOX_LIB_ERR_INTERNAL;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Stepping API
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_step_cycles(
    dosbox_lib_handle_t handle,
    uint64_t cycles,
    dosbox_lib_step_result_t* result_out
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    try {
        // Sprint 2 Phase 1: Operate directly on context without thread-local state
        // No ContextGuard needed - platform providers accessed via context directly
        auto* ctx = g_context.get();

        uint64_t cycles_executed = 0;
        uint32_t events_processed = 0;
        uint32_t stop_reason = DOSBOX_LIB_STOP_COMPLETED;

        // Execute in batches
        const uint64_t batch_size = g_time_state.cycles_per_ms;

        while (cycles_executed < cycles) {
            uint64_t remaining = cycles - cycles_executed;
            uint64_t batch = remaining < batch_size ? remaining : batch_size;

            // Check for stop conditions
            if (ctx->cpu_state.halted) {
                stop_reason = DOSBOX_LIB_STOP_HALT;
                break;
            }

            if (ctx->stop_requested()) {
                stop_reason = DOSBOX_LIB_STOP_COMPLETED;
                break;
            }

            // Execute the batch
            // Note: In full implementation, this calls into the actual CPU core
            // For now, we just track cycles
            cycles_executed += batch;

            // Simulate event processing
            if (cycles_executed % (batch_size * 10) == 0) {
                events_processed++;
            }
        }

        // Update canonical time state
        g_time_state.total_cycles += cycles_executed;
        g_time_state.emu_time_us += g_time_state.cycles_to_us(cycles_executed);

        // Fill result
        if (result_out) {
            result_out->cycles_executed = cycles_executed;
            result_out->emu_time_us = g_time_state.emu_time_us;
            result_out->stop_reason = stop_reason;
            result_out->events_processed = events_processed;
        }

        g_last_error.clear();
        return DOSBOX_LIB_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        if (result_out) {
            result_out->stop_reason = DOSBOX_LIB_STOP_ERROR;
        }
        return DOSBOX_LIB_ERR_INTERNAL;
    }
}

dosbox_lib_error_t dosbox_lib_step_ms(
    dosbox_lib_handle_t handle,
    uint32_t ms,
    dosbox_lib_step_result_t* result_out
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Convert milliseconds to cycles
    uint64_t target_cycles = g_time_state.ms_to_cycles(ms);

    // Delegate to cycle-based stepping
    return dosbox_lib_step_cycles(handle, target_cycles, result_out);
}

dosbox_lib_error_t dosbox_lib_get_emu_time(
    dosbox_lib_handle_t handle,
    uint64_t* time_us_out
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(time_us_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    *time_us_out = g_time_state.emu_time_us;
    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_get_total_cycles(
    dosbox_lib_handle_t handle,
    uint64_t* cycles_out
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(cycles_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    *cycles_out = g_time_state.total_cycles;
    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// State API
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_state_hash(
    dosbox_lib_handle_t handle,
    uint8_t hash_out[32]
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(hash_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    try {
        // Sprint 2 Phase 1: Use explicit context API
        auto result = dosbox::get_state_hash(g_context.get(), dosbox::HashMode::Fast);
        if (!result.has_value()) {
            g_last_error = result.error().message();
            return DOSBOX_LIB_ERR_INTERNAL;
        }
        std::copy(result.value().begin(), result.value().end(), hash_out);
        return DOSBOX_LIB_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        return DOSBOX_LIB_ERR_INTERNAL;
    }
}

dosbox_lib_error_t dosbox_lib_save_state(
    dosbox_lib_handle_t handle,
    void* buffer,
    size_t buffer_size,
    size_t* size_out
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(size_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // TODO: Implement full state serialization
    // For now, return minimal size
    *size_out = sizeof(TimeState);

    if (buffer == nullptr) {
        return DOSBOX_LIB_OK;  // Query size only
    }

    if (buffer_size < *size_out) {
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    std::memcpy(buffer, &g_time_state, sizeof(TimeState));
    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_load_state(
    dosbox_lib_handle_t handle,
    const void* buffer,
    size_t buffer_size
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(buffer != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    if (buffer_size < sizeof(TimeState)) {
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    std::memcpy(&g_time_state, buffer, sizeof(TimeState));
    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// Error Handling
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_last_error(
    dosbox_lib_handle_t /*handle*/,
    char* buffer,
    size_t buffer_size,
    size_t* length_out
) {
    LIB_REQUIRE(length_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);

    *length_out = g_last_error.length() + 1;

    if (buffer == nullptr) {
        return DOSBOX_LIB_OK;  // Query size only
    }

    if (buffer_size < *length_out) {
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    std::copy(g_last_error.begin(), g_last_error.end(), buffer);
    buffer[g_last_error.length()] = '\0';
    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_set_log_callback(
    dosbox_lib_handle_t handle,
    dosbox_lib_log_callback_t callback,
    void* userdata
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    g_log_state.callback = callback;
    g_log_state.userdata = userdata;
    return DOSBOX_LIB_OK;
}

} // extern "C"
