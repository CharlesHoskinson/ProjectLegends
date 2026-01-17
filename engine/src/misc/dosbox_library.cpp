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
#include "dosbox/cpu_bridge.h"
#include "dosbox/engine_state.h"
#include "dosbox/error_model.h"
#include "dosbox/state_hash.h"
#include "aibox/headless_stub.h"

#include <cstring>
#include <algorithm>

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
// CRC32 Implementation (dosbox namespace)
// ═══════════════════════════════════════════════════════════════════════════════

namespace dosbox {

uint32_t compute_crc32(const void* data, size_t size) {
    // Standard CRC32 lookup table (polynomial 0xEDB88320)
    static const uint32_t table[256] = {
        0x00000000, 0x77073096, 0xee0e612c, 0x990951ba, 0x076dc419, 0x706af48f, 0xe963a535, 0x9e6495a3,
        0x0edb8832, 0x79dcb8a4, 0xe0d5e91e, 0x97d2d988, 0x09b64c2b, 0x7eb17cbd, 0xe7b82d07, 0x90bf1d91,
        0x1db71064, 0x6ab020f2, 0xf3b97148, 0x84be41de, 0x1adad47d, 0x6ddde4eb, 0xf4d4b551, 0x83d385c7,
        0x136c9856, 0x646ba8c0, 0xfd62f97a, 0x8a65c9ec, 0x14015c4f, 0x63066cd9, 0xfa0f3d63, 0x8d080df5,
        0x3b6e20c8, 0x4c69105e, 0xd56041e4, 0xa2677172, 0x3c03e4d1, 0x4b04d447, 0xd20d85fd, 0xa50ab56b,
        0x35b5a8fa, 0x42b2986c, 0xdbbbc9d6, 0xacbcf940, 0x32d86ce3, 0x45df5c75, 0xdcd60dcf, 0xabd13d59,
        0x26d930ac, 0x51de003a, 0xc8d75180, 0xbfd06116, 0x21b4f4b5, 0x56b3c423, 0xcfba9599, 0xb8bda50f,
        0x2802b89e, 0x5f058808, 0xc60cd9b2, 0xb10be924, 0x2f6f7c87, 0x58684c11, 0xc1611dab, 0xb6662d3d,
        0x76dc4190, 0x01db7106, 0x98d220bc, 0xefd5102a, 0x71b18589, 0x06b6b51f, 0x9fbfe4a5, 0xe8b8d433,
        0x7807c9a2, 0x0f00f934, 0x9609a88e, 0xe10e9818, 0x7f6a0dbb, 0x086d3d2d, 0x91646c97, 0xe6635c01,
        0x6b6b51f4, 0x1c6c6162, 0x856530d8, 0xf262004e, 0x6c0695ed, 0x1b01a57b, 0x8208f4c1, 0xf50fc457,
        0x65b0d9c6, 0x12b7e950, 0x8bbeb8ea, 0xfcb9887c, 0x62dd1ddf, 0x15da2d49, 0x8cd37cf3, 0xfbd44c65,
        0x4db26158, 0x3ab551ce, 0xa3bc0074, 0xd4bb30e2, 0x4adfa541, 0x3dd895d7, 0xa4d1c46d, 0xd3d6f4fb,
        0x4369e96a, 0x346ed9fc, 0xad678846, 0xda60b8d0, 0x44042d73, 0x33031de5, 0xaa0a4c5f, 0xdd0d7a9b,
        0x5005713c, 0x270241aa, 0xbe0b1010, 0xc90c2086, 0x5768b525, 0x206f85b3, 0xb966d409, 0xce61e49f,
        0x5edef90e, 0x29d9c998, 0xb0d09822, 0xc7d7a8b4, 0x59b33d17, 0x2eb40d81, 0xb7bd5c3b, 0xc0ba6cad,
        0xedb88320, 0x9abfb3b6, 0x03b6e20c, 0x74b1d29a, 0xead54739, 0x9dd277af, 0x04db2615, 0x73dc1683,
        0xe3630b12, 0x94643b84, 0x0d6d6a3e, 0x7a6a5aa8, 0xe40ecf0b, 0x9309ff9d, 0x0a00ae27, 0x7d079eb1,
        0xf00f9344, 0x8708a3d2, 0x1e01f268, 0x6906c2fe, 0xf762575d, 0x806567cb, 0x196c3671, 0x6e6b06e7,
        0xfed41b76, 0x89d32be0, 0x10da7a5a, 0x67dd4acc, 0xf9b9df6f, 0x8ebeeff9, 0x17b7be43, 0x60b08ed5,
        0xd6d6a3e8, 0xa1d1937e, 0x38d8c2c4, 0x4fdff252, 0xd1bb67f1, 0xa6bc5767, 0x3fb506dd, 0x48b2364b,
        0xd80d2bda, 0xaf0a1b4c, 0x36034af6, 0x41047a60, 0xdf60efc3, 0xa867df55, 0x316e8eef, 0x4669be79,
        0xcb61b38c, 0xbc66831a, 0x256fd2a0, 0x5268e236, 0xcc0c7795, 0xbb0b4703, 0x220216b9, 0x5505262f,
        0xc5ba3bbe, 0xb2bd0b28, 0x2bb45a92, 0x5cb36a04, 0xc2d7ffa7, 0xb5d0cf31, 0x2cd99e8b, 0x5bdeae1d,
        0x9b64c2b0, 0xec63f226, 0x756aa39c, 0x026d930a, 0x9c0906a9, 0xeb0e363f, 0x72076785, 0x05005713,
        0x95bf4a82, 0xe2b87a14, 0x7bb12bae, 0x0cb61b38, 0x92d28e9b, 0xe5d5be0d, 0x7cdcefb7, 0x0bdbdf21,
        0x86d3d2d4, 0xf1d4e242, 0x68ddb3f8, 0x1fda836e, 0x81be16cd, 0xf6b9265b, 0x6fb077e1, 0x18b74777,
        0x88085ae6, 0xff0f6a70, 0x66063bca, 0x11010b5c, 0x8f659eff, 0xf862ae69, 0x616bffd3, 0x166ccf45,
        0xa00ae278, 0xd70dd2ee, 0x4e048354, 0x3903b3c2, 0xa7672661, 0xd06016f7, 0x4969474d, 0x3e6e77db,
        0xaed16a4a, 0xd9d65adc, 0x40df0b66, 0x37d83bf0, 0xa9bcae53, 0xdebb9ec5, 0x47b2cf7f, 0x30b5ffe9,
        0xbdbdf21c, 0xcabac28a, 0x53b39330, 0x24b4a3a6, 0xbad03605, 0xcdd706b9, 0x54de5729, 0x23d967bf,
        0xb3667a2e, 0xc4614ab8, 0x5d681b02, 0x2a6f2b94, 0xb40bbe37, 0xc30c8ea1, 0x5a05df1b, 0x2d02ef8d
    };

    const uint8_t* ptr = static_cast<const uint8_t*>(data);
    uint32_t crc = 0xFFFFFFFF;
    for (size_t i = 0; i < size; ++i) {
        crc = table[(crc ^ ptr[i]) & 0xFF] ^ (crc >> 8);
    }
    return crc ^ 0xFFFFFFFF;
}

} // namespace dosbox

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
        auto init_result = g_context->initialize();
        if (!init_result.has_value()) {
            g_last_error = init_result.error().message();
            return DOSBOX_LIB_ERR_INTERNAL;
        }

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
        auto reset_result = g_context->reset();
        if (!reset_result.has_value()) {
            g_last_error = reset_result.error().message();
            return DOSBOX_LIB_ERR_INTERNAL;
        }
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
        auto* ctx = g_context.get();

        // Use the CPU bridge to execute actual CPU instructions
        auto bridge_result = dosbox::execute_cycles(ctx, cycles);

        // Map bridge stop reason to library stop reason
        uint32_t stop_reason = DOSBOX_LIB_STOP_COMPLETED;
        switch (bridge_result.stop_reason) {
            case dosbox::CpuStopReason::Completed:
                stop_reason = DOSBOX_LIB_STOP_COMPLETED;
                break;
            case dosbox::CpuStopReason::Halt:
                stop_reason = DOSBOX_LIB_STOP_HALT;
                break;
            case dosbox::CpuStopReason::Breakpoint:
                stop_reason = DOSBOX_LIB_STOP_BREAKPOINT;
                break;
            case dosbox::CpuStopReason::Error:
                stop_reason = DOSBOX_LIB_STOP_ERROR;
                break;
            case dosbox::CpuStopReason::UserRequest:
                stop_reason = DOSBOX_LIB_STOP_USER_REQUEST;
                break;
            case dosbox::CpuStopReason::Callback:
                stop_reason = DOSBOX_LIB_STOP_CALLBACK;
                break;
        }

        // Update canonical time state (bridge already updated context timing)
        g_time_state.total_cycles += bridge_result.cycles_executed;
        // Compute emu_time from total_cycles to avoid accumulating rounding errors
        // This ensures determinism: 10000 cycles in one call = 5000+5000 in two calls
        g_time_state.emu_time_us = g_time_state.cycles_to_us(g_time_state.total_cycles);

        // Fill result
        if (result_out) {
            result_out->cycles_executed = bridge_result.cycles_executed;
            result_out->emu_time_us = g_time_state.emu_time_us;
            result_out->stop_reason = stop_reason;
            result_out->events_processed = bridge_result.events_processed;
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
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Calculate total size needed
    *size_out = dosbox::ENGINE_STATE_SIZE;

    if (buffer == nullptr) {
        return DOSBOX_LIB_OK;  // Query size only
    }

    if (buffer_size < *size_out) {
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    auto* ctx = g_context.get();
    uint8_t* ptr = static_cast<uint8_t*>(buffer);

    // Initialize header
    auto* header = reinterpret_cast<dosbox::EngineStateHeader*>(ptr);
    std::memset(header, 0, sizeof(dosbox::EngineStateHeader));
    header->magic = dosbox::ENGINE_STATE_MAGIC;
    header->version = dosbox::ENGINE_STATE_VERSION;
    header->total_size = static_cast<uint32_t>(*size_out);

    // Calculate section offsets
    size_t offset = sizeof(dosbox::EngineStateHeader);

    header->timing_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateTiming);

    header->pic_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStatePic);

    header->keyboard_offset = static_cast<uint32_t>(offset);

    // Serialize timing state
    auto* timing = reinterpret_cast<dosbox::EngineStateTiming*>(ptr + header->timing_offset);
    std::memset(timing, 0, sizeof(dosbox::EngineStateTiming));
    timing->total_cycles = ctx->timing.total_cycles;
    timing->virtual_ticks_ms = ctx->timing.virtual_ticks_ms;
    timing->ticks_done = ctx->timing.ticks_done;
    timing->ticks_scheduled = ctx->timing.ticks_scheduled;
    timing->ticks_remain = ctx->timing.ticks_remain;
    timing->ticks_added = ctx->timing.ticks_added;
    timing->frame_ticks = ctx->timing.frame_ticks;
    timing->locked = ctx->timing.locked ? 1 : 0;

    // Serialize PIC state
    auto* pic = reinterpret_cast<dosbox::EngineStatePic*>(ptr + header->pic_offset);
    std::memset(pic, 0, sizeof(dosbox::EngineStatePic));
    pic->ticks = ctx->pic.ticks;
    pic->irq_check = ctx->pic.irq_check;
    pic->irq_check_pending = ctx->pic.irq_check_pending;
    pic->master_cascade_irq = ctx->pic.master_cascade_irq;
    pic->master_imr = ctx->pic.master_imr;
    pic->slave_imr = ctx->pic.slave_imr;
    pic->master_isr = ctx->pic.master_isr;
    pic->slave_isr = ctx->pic.slave_isr;
    pic->auto_eoi = ctx->pic.auto_eoi ? 1 : 0;
    pic->in_event_service = ctx->pic.in_event_service ? 1 : 0;

    // Serialize keyboard state
    auto* kbd = reinterpret_cast<dosbox::EngineStateKeyboard*>(ptr + header->keyboard_offset);
    std::memset(kbd, 0, sizeof(dosbox::EngineStateKeyboard));
    kbd->scanset = ctx->keyboard.scanset;
    kbd->enabled = ctx->keyboard.enabled ? 1 : 0;
    kbd->active = ctx->keyboard.active ? 1 : 0;
    kbd->command = ctx->keyboard.command;
    kbd->p60data = ctx->keyboard.p60data;
    kbd->p60changed = ctx->keyboard.p60changed ? 1 : 0;
    kbd->scanning = ctx->keyboard.scanning ? 1 : 0;
    kbd->scheduled = ctx->keyboard.scheduled ? 1 : 0;
    kbd->buffer_used = ctx->keyboard.buffer_used;
    kbd->buffer_pos = ctx->keyboard.buffer_pos;
    kbd->led_state = ctx->keyboard.led_state;
    kbd->num_lock = ctx->keyboard.num_lock ? 1 : 0;
    kbd->caps_lock = ctx->keyboard.caps_lock ? 1 : 0;
    kbd->scroll_lock = ctx->keyboard.scroll_lock ? 1 : 0;
    kbd->cb_xlat = ctx->keyboard.cb_xlat ? 1 : 0;

    // Compute checksum (over data after header)
    const uint8_t* data_start = ptr + sizeof(dosbox::EngineStateHeader);
    size_t data_size = *size_out - sizeof(dosbox::EngineStateHeader);
    header->checksum = dosbox::compute_crc32(data_start, data_size);

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
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Validate minimum size
    if (buffer_size < sizeof(dosbox::EngineStateHeader)) {
        g_last_error = "Buffer too small for header";
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    const uint8_t* ptr = static_cast<const uint8_t*>(buffer);
    const auto* header = reinterpret_cast<const dosbox::EngineStateHeader*>(ptr);

    // Validate magic
    if (header->magic != dosbox::ENGINE_STATE_MAGIC) {
        g_last_error = "Invalid state magic number";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    // Validate version
    if (header->version != dosbox::ENGINE_STATE_VERSION) {
        g_last_error = "Incompatible state version";
        return DOSBOX_LIB_ERR_VERSION_MISMATCH;
    }

    // Validate total size - must be at least header size to prevent underflow
    if (header->total_size < sizeof(dosbox::EngineStateHeader)) {
        g_last_error = "State size smaller than header";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    if (buffer_size < header->total_size) {
        g_last_error = "Buffer smaller than stated total size";
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    // Verify checksum (safe now that we validated total_size >= header size)
    const uint8_t* data_start = ptr + sizeof(dosbox::EngineStateHeader);
    size_t data_size = header->total_size - sizeof(dosbox::EngineStateHeader);
    uint32_t computed_crc = dosbox::compute_crc32(data_start, data_size);
    if (computed_crc != header->checksum) {
        g_last_error = "Checksum mismatch - state corrupted";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    // Validate section offsets are within bounds
    auto validate_offset = [&](uint32_t offset, size_t section_size) -> bool {
        return offset >= sizeof(dosbox::EngineStateHeader) &&
               offset + section_size <= header->total_size;
    };

    if (!validate_offset(header->timing_offset, sizeof(dosbox::EngineStateTiming)) ||
        !validate_offset(header->pic_offset, sizeof(dosbox::EngineStatePic)) ||
        !validate_offset(header->keyboard_offset, sizeof(dosbox::EngineStateKeyboard))) {
        g_last_error = "Invalid section offset";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    auto* ctx = g_context.get();

    // Deserialize timing state
    const auto* timing = reinterpret_cast<const dosbox::EngineStateTiming*>(ptr + header->timing_offset);
    ctx->timing.total_cycles = timing->total_cycles;
    ctx->timing.virtual_ticks_ms = timing->virtual_ticks_ms;
    ctx->timing.ticks_done = timing->ticks_done;
    ctx->timing.ticks_scheduled = timing->ticks_scheduled;
    ctx->timing.ticks_remain = timing->ticks_remain;
    ctx->timing.ticks_added = timing->ticks_added;
    ctx->timing.frame_ticks = timing->frame_ticks;
    ctx->timing.locked = timing->locked != 0;

    // Deserialize PIC state
    const auto* pic = reinterpret_cast<const dosbox::EngineStatePic*>(ptr + header->pic_offset);
    ctx->pic.ticks = pic->ticks;
    ctx->pic.irq_check = pic->irq_check;
    ctx->pic.irq_check_pending = pic->irq_check_pending;
    ctx->pic.master_cascade_irq = pic->master_cascade_irq;
    ctx->pic.master_imr = pic->master_imr;
    ctx->pic.slave_imr = pic->slave_imr;
    ctx->pic.master_isr = pic->master_isr;
    ctx->pic.slave_isr = pic->slave_isr;
    ctx->pic.auto_eoi = pic->auto_eoi != 0;
    ctx->pic.in_event_service = pic->in_event_service != 0;

    // Deserialize keyboard state
    const auto* kbd = reinterpret_cast<const dosbox::EngineStateKeyboard*>(ptr + header->keyboard_offset);
    ctx->keyboard.scanset = kbd->scanset;
    ctx->keyboard.enabled = kbd->enabled != 0;
    ctx->keyboard.active = kbd->active != 0;
    ctx->keyboard.command = kbd->command;
    ctx->keyboard.p60data = kbd->p60data;
    ctx->keyboard.p60changed = kbd->p60changed != 0;
    ctx->keyboard.scanning = kbd->scanning != 0;
    ctx->keyboard.scheduled = kbd->scheduled != 0;
    ctx->keyboard.buffer_used = kbd->buffer_used;
    ctx->keyboard.buffer_pos = kbd->buffer_pos;
    ctx->keyboard.led_state = kbd->led_state;
    ctx->keyboard.num_lock = kbd->num_lock != 0;
    ctx->keyboard.caps_lock = kbd->caps_lock != 0;
    ctx->keyboard.scroll_lock = kbd->scroll_lock != 0;
    ctx->keyboard.cb_xlat = kbd->cb_xlat != 0;

    // Also update g_time_state for consistency with library API
    g_time_state.total_cycles = timing->total_cycles;
    g_time_state.emu_time_us = g_time_state.cycles_to_us(timing->total_cycles);

    g_last_error.clear();
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

// ═══════════════════════════════════════════════════════════════════════════════
// Input Injection API
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_inject_key(
    dosbox_lib_handle_t handle,
    uint8_t scancode,
    int pressed,
    int extended
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Notify headless input provider (optional telemetry)
    uint16_t keycode = scancode;
    if (extended) {
        keycode |= 0x100;  // Mark as E0-prefixed
    }
    static_cast<void>(aibox::headless::PushKeyEvent(keycode, pressed != 0));

    auto& kb = g_context->keyboard;
    auto push_byte = [&](uint16_t data) {
        if (kb.buffer_used >= kb.BUFFER_SIZE) {
            kb.buffer_pos = (kb.buffer_pos + 1) % kb.BUFFER_SIZE;
            kb.buffer_used = kb.BUFFER_SIZE - 1;
        }
        size_t idx = (kb.buffer_pos + kb.buffer_used) % kb.BUFFER_SIZE;
        kb.buffer[idx] = data;
        kb.buffer_used++;
        kb.p60data = static_cast<uint8_t>(data & 0xFF);
        kb.p60changed = true;
        kb.auxchanged = ((data & 0x100) != 0);
    };

    if (extended) {
        push_byte(0xE0);
    }
    uint8_t code = pressed ? scancode : (scancode | 0x80);
    push_byte(code);

    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_inject_mouse(
    dosbox_lib_handle_t handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Use the headless stub input functions which integrate with the PAL input system
    // Push motion and button events separately
    if (delta_x != 0 || delta_y != 0) {
        static_cast<void>(aibox::headless::PushMouseMotion(delta_x, delta_y));
    }

    // Handle button state changes (provider notification only)
    static uint8_t last_buttons = 0;
    const bool buttons_changed = (buttons != last_buttons);
    if ((buttons & 0x01) != (last_buttons & 0x01)) {
        static_cast<void>(aibox::headless::PushMouseButton(0, (buttons & 0x01) != 0));  // Left button
    }
    if ((buttons & 0x02) != (last_buttons & 0x02)) {
        static_cast<void>(aibox::headless::PushMouseButton(1, (buttons & 0x02) != 0));  // Right button
    }
    if ((buttons & 0x04) != (last_buttons & 0x04)) {
        static_cast<void>(aibox::headless::PushMouseButton(2, (buttons & 0x04) != 0));  // Middle button
    }

    const bool has_motion = (delta_x != 0 || delta_y != 0);
    if (has_motion || buttons_changed) {
        auto& kb = g_context->keyboard;
        int x = static_cast<int>(delta_x);
        int y = -static_cast<int>(delta_y);
        if (x < -256) x = -256;
        else if (x > 255) x = 255;
        if (y < -256) y = -256;
        else if (y > 255) y = 255;

        uint8_t status = 0x08;
        if (x == -256 || x == 255) status |= 0x40;
        if (y == -256 || y == 255) status |= 0x80;
        if (x & 0x100) status |= 0x10;
        if (y & 0x100) status |= 0x20;
        if (buttons & 0x01) status |= 0x01;
        if (buttons & 0x02) status |= 0x02;
        if (buttons & 0x04) status |= 0x04;

        auto push_aux = [&](uint8_t byte) {
            if (kb.buffer_used >= kb.BUFFER_SIZE) {
                kb.buffer_pos = (kb.buffer_pos + 1) % kb.BUFFER_SIZE;
                kb.buffer_used = kb.BUFFER_SIZE - 1;
            }
            size_t idx = (kb.buffer_pos + kb.buffer_used) % kb.BUFFER_SIZE;
            kb.buffer[idx] = static_cast<uint16_t>(0x100 | byte);
            kb.buffer_used++;
            kb.p60data = byte;
            kb.p60changed = true;
            kb.auxchanged = true;
        };

        push_aux(status);
        push_aux(static_cast<uint8_t>(x & 0xFF));
        push_aux(static_cast<uint8_t>(y & 0xFF));
    }

    last_buttons = buttons;

    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// PIC State API
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_pic_state(
    dosbox_lib_handle_t handle,
    dosbox_lib_pic_state_t* state_out
) {
    LIB_REQUIRE(handle != nullptr, DOSBOX_LIB_ERR_NULL_HANDLE);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(state_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Read PIC state from engine context
    // Note: irq_check contains the pending IRQ bitmap (similar to IRR)
    state_out->master_irr = static_cast<uint8_t>(g_context->pic.irq_check & 0xFF);
    state_out->master_imr = g_context->pic.master_imr;
    state_out->master_isr = g_context->pic.master_isr;
    state_out->slave_irr = static_cast<uint8_t>((g_context->pic.irq_check >> 8) & 0xFF);
    state_out->slave_imr = g_context->pic.slave_imr;
    state_out->slave_isr = g_context->pic.slave_isr;

    return DOSBOX_LIB_OK;
}

} // extern "C"
