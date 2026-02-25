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

// Handle sentinel — a recognizable non-null constant that is unlikely to be
// a valid heap or stack pointer. Validation checks for this value instead of
// just != nullptr, which catches stale/random pointers. (M8)
constexpr uintptr_t HANDLE_SENTINEL = 0x444F5358; // "DOSX"

// Single instance enforcement
std::atomic<bool> g_instance_exists{false};

// Owner thread ID for thread safety
std::thread::id g_owner_thread_id{};

// The DOSBox context instance
std::unique_ptr<dosbox::DOSBoxContext> g_context;

// Configuration stored from create
dosbox_lib_config_t g_config;

// Deep copies of config strings (M9) — g_config.config_path and
// g_config.working_dir point into these owned buffers after deep-copy.
std::string g_config_path_owned;
std::string g_working_dir_owned;

// Audio enable flag (Phase -1: set before create, read during create)
bool g_audio_enabled = false;

// Last error message
std::string g_last_error;

// Mouse button state (M5: moved from function-scope static to file-scope
// so it can be reset on new instance creation)
uint8_t g_mouse_last_buttons = 0;

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
// Timing Config (reads g_config.cpu_cycles; timing state lives in g_context)
// ═══════════════════════════════════════════════════════════════════════════════

inline uint32_t cycles_per_ms() {
    return g_config.cpu_cycles > 0 ? g_config.cpu_cycles : 3000;
}

inline uint64_t cycles_to_us(uint64_t cycles) {
    return (cycles * 1000) / cycles_per_ms();
}

inline uint64_t ms_to_cycles(uint32_t ms) {
    return static_cast<uint64_t>(ms) * cycles_per_ms();
}

// ═══════════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════════

#define LIB_REQUIRE(cond, err) \
    do { if (!(cond)) return (err); } while(0)

// Validate handle matches the sentinel value (M8)
#define LIB_VALIDATE_HANDLE(h) \
    LIB_REQUIRE((h) == reinterpret_cast<dosbox_lib_handle_t>(HANDLE_SENTINEL), \
                DOSBOX_LIB_ERR_INVALID_HANDLE)

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

        // Deep-copy string fields so caller can free originals (M9)
        if (g_config.config_path) {
            g_config_path_owned = g_config.config_path;
            g_config.config_path = g_config_path_owned.c_str();
        } else {
            g_config_path_owned.clear();
        }
        if (g_config.working_dir) {
            g_working_dir_owned = g_config.working_dir;
            g_config.working_dir = g_working_dir_owned.c_str();
        } else {
            g_working_dir_owned.clear();
        }
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
        // Create DOSBox context with translated config (F5 fix)
        auto ctx_config = [&]() {
            dosbox::ContextConfig c;
            c.memory_size = static_cast<size_t>(g_config.memory_kb) * 1024;
            c.cpu_cycles = g_config.cpu_cycles > 0 ? g_config.cpu_cycles : 3000;
            c.deterministic = (g_config.deterministic != 0);
            c.sound_enabled = g_audio_enabled;
            return c;
        }();
        g_context = std::make_unique<dosbox::DOSBoxContext>(ctx_config);

        // Reset mouse state (M5: prevent leaking between instances)
        g_mouse_last_buttons = 0;

        // Return sentinel handle (actual pointer not exposed) (M8)
        *handle_out = reinterpret_cast<dosbox_lib_handle_t>(HANDLE_SENTINEL);
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
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    try {
        // Set thread-local context so memory access (MemBase) works during init
        dosbox::ContextGuard ctx_guard(*g_context);

        // Initialize the context (allocates memory, etc.)
        auto init_result = g_context->initialize();
        if (!init_result.has_value()) {
            g_last_error = init_result.error().message();
            return DOSBOX_LIB_ERR_INTERNAL;
        }

        // Initialize CPU bridge (decoder, registers).
        // Must happen after memory is allocated so MemBase is valid.
        // init_cpu_bridge() is idempotent for decoder setup but we also
        // need CPU_LibraryInit() to reset registers for each new instance
        // (EIP etc. persist as globals across instance create/destroy).
        dosbox::init_cpu_bridge();
        dosbox::reset_cpu_bridge();

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
    // Validate sentinel (M8) — reject random non-null pointers
    if (handle != reinterpret_cast<dosbox_lib_handle_t>(HANDLE_SENTINEL)) {
        return DOSBOX_LIB_ERR_INVALID_HANDLE;
    }

    // M6: Check thread affinity (same pattern as other thread-checked functions)
    LIB_CHECK_THREAD();

    LIB_LOG_INFO("Destroying DOSBox-X library instance");

    // Shutdown and destroy context
    if (g_context) {
        g_context->shutdown();
        g_context.reset();
    }

    // Reset state
    aibox::headless::ResetState();
    g_instance_exists = false;
    g_owner_thread_id = std::thread::id{};
    g_last_error.clear();
    g_log_state.reset();
    g_config_path_owned.clear();
    g_working_dir_owned.clear();

    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_reset(dosbox_lib_handle_t handle) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    try {
        auto reset_result = g_context->reset();
        if (!reset_result.has_value()) {
            g_last_error = reset_result.error().message();
            return DOSBOX_LIB_ERR_INTERNAL;
        }

        // Reset real CPU registers to power-on defaults for determinism
        dosbox::reset_cpu_bridge();

        // Zero guest memory so execution starts from a clean state,
        // then refill guard region with HLT (0xF4) so CPU halts on overrun
        if (g_context->memory.base && g_context->memory.size > 0) {
            std::memset(g_context->memory.base, 0, g_context->memory.size);
            // Guard region sits immediately after the main memory allocation
            constexpr size_t GUARD_REGION_SIZE = 65536;
            std::memset(g_context->memory.base + g_context->memory.size,
                        0xF4, GUARD_REGION_SIZE);
        }

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
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    try {
        auto* ctx = g_context.get();

        // Set thread-local context so CPU core memory access (MemBase) works
        dosbox::ContextGuard ctx_guard(*ctx);

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

        // Context timing already updated by bridge (total_cycles incremented)
        // Compute emu_time from total_cycles to avoid accumulating rounding errors
        uint64_t emu_us = cycles_to_us(g_context->timing.total_cycles);

        // Fill result
        if (result_out) {
            result_out->cycles_executed = bridge_result.cycles_executed;
            result_out->emu_time_us = emu_us;
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
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Convert milliseconds to cycles
    uint64_t target_cycles = ms_to_cycles(ms);

    // Delegate to cycle-based stepping
    return dosbox_lib_step_cycles(handle, target_cycles, result_out);
}

dosbox_lib_error_t dosbox_lib_get_emu_time(
    dosbox_lib_handle_t handle,
    uint64_t* time_us_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(time_us_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    *time_us_out = cycles_to_us(g_context->timing.total_cycles);
    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_get_total_cycles(
    dosbox_lib_handle_t handle,
    uint64_t* cycles_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(cycles_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);

    *cycles_out = g_context->timing.total_cycles;
    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context Access API
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_context_ptr(
    dosbox_lib_handle_t handle,
    void** ctx_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(ctx_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    *ctx_out = static_cast<void*>(g_context.get());
    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// State API
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_state_hash(
    dosbox_lib_handle_t handle,
    uint8_t hash_out[32]
) {
    LIB_VALIDATE_HANDLE(handle);
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
    LIB_VALIDATE_HANDLE(handle);
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

    // Initialize header (H2: use memcpy, not reinterpret_cast)
    dosbox::EngineStateHeader header{};
    header.magic = dosbox::ENGINE_STATE_MAGIC;
    header.version = dosbox::ENGINE_STATE_VERSION;
    header.total_size = static_cast<uint32_t>(*size_out);

    // Calculate section offsets
    size_t offset = sizeof(dosbox::EngineStateHeader);

    header.timing_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateTiming);

    header.pic_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStatePic);

    header.keyboard_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateKeyboard);

    header.cpu_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateCpu);

    header.memory_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateMemory);

    header.mixer_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateMixer);

    header.vga_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateVga);

    header.dos_offset = static_cast<uint32_t>(offset);

    // Serialize timing state (H2: local struct + memcpy)
    dosbox::EngineStateTiming timing{};
    timing.total_cycles = ctx->timing.total_cycles;
    timing.virtual_ticks_ms = ctx->timing.virtual_ticks_ms;
    timing.ticks_done = ctx->timing.ticks_done;
    timing.ticks_scheduled = ctx->timing.ticks_scheduled;
    timing.ticks_remain = ctx->timing.ticks_remain;
    timing.ticks_added = ctx->timing.ticks_added;
    timing.frame_ticks = ctx->timing.frame_ticks;
    timing.locked = ctx->timing.locked ? 1 : 0;
    std::memcpy(ptr + header.timing_offset, &timing, sizeof(timing));

    // Serialize PIC state (V4: full controller registers)
    dosbox::EngineStatePic pic{};
    pic.ticks = ctx->pic.ticks;
    pic.irq_check = ctx->pic.irq_check;
    pic.irq_check_pending = ctx->pic.irq_check_pending;
    pic.master_cascade_irq = ctx->pic.master_cascade_irq;
    pic.in_event_service = ctx->pic.in_event_service ? 1 : 0;
    pic.enable_slave_pic = ctx->pic.enable_slave_pic ? 1 : 0;
    for (int c = 0; c < 2; ++c) {
        auto& src = ctx->pic.controllers[c];
        auto& dst = pic.controllers[c];
        dst.icw_words = src.icw_words;
        dst.icw_index = src.icw_index;
        dst.special = src.special ? 1 : 0;
        dst.auto_eoi = src.auto_eoi ? 1 : 0;
        dst.rotate_on_auto_eoi = src.rotate_on_auto_eoi ? 1 : 0;
        dst.single = src.single ? 1 : 0;
        dst.request_issr = src.request_issr ? 1 : 0;
        dst.vector_base = src.vector_base;
        dst.input = src.input;
        dst.edge = src.edge;
        dst.irr = src.irr;
        dst.imr = src.imr;
        dst.imrr = src.imrr;
        dst.isr = src.isr;
        dst.isrr = src.isrr;
        dst.isr_ignore = src.isr_ignore;
        dst.active_irq = src.active_irq;
        dst.controller_index = src.controller_index;
    }
    std::memcpy(ptr + header.pic_offset, &pic, sizeof(pic));

    // Serialize keyboard state (H2: local struct + memcpy; V3: 96 entries)
    dosbox::EngineStateKeyboard kbd{};
    for (size_t i = 0; i < 96; ++i) {
        kbd.buffer[i] = ctx->keyboard.buffer[i];
    }
    kbd.buffer_used = ctx->keyboard.buffer_used;
    kbd.buffer_pos = ctx->keyboard.buffer_pos;
    kbd.pending_key = ctx->keyboard.pending_key;
    kbd.repeat_key = ctx->keyboard.repeat.key;
    kbd.repeat_wait = ctx->keyboard.repeat.wait;
    kbd.repeat_pause = ctx->keyboard.repeat.pause;
    kbd.repeat_rate = ctx->keyboard.repeat.rate;
    kbd.led_state = ctx->keyboard.led_state;
    std::memcpy(kbd.buf8042, ctx->keyboard.buf8042, 8);
    kbd.buf8042_len = ctx->keyboard.buf8042_len;
    kbd.buf8042_pos = ctx->keyboard.buf8042_pos;
    kbd.scanset = ctx->keyboard.scanset;
    kbd.enabled = ctx->keyboard.enabled ? 1 : 0;
    kbd.active = ctx->keyboard.active ? 1 : 0;
    kbd.p60data = ctx->keyboard.p60data;
    kbd.p60changed = ctx->keyboard.p60changed ? 1 : 0;
    kbd.num_lock = ctx->keyboard.num_lock ? 1 : 0;
    kbd.caps_lock = ctx->keyboard.caps_lock ? 1 : 0;
    kbd.scroll_lock = ctx->keyboard.scroll_lock ? 1 : 0;
    kbd.command = ctx->keyboard.command;
    kbd.expecting_data = ctx->keyboard.expecting_data ? 1 : 0;
    kbd.scanning = ctx->keyboard.scanning ? 1 : 0;
    kbd.auxactive = ctx->keyboard.auxactive ? 1 : 0;
    kbd.scheduled = ctx->keyboard.scheduled ? 1 : 0;
    kbd.auxchanged = ctx->keyboard.auxchanged ? 1 : 0;
    kbd.pending_key_state = ctx->keyboard.pending_key_state ? 1 : 0;
    kbd.cb_override_inhibit = ctx->keyboard.cb_override_inhibit ? 1 : 0;
    kbd.cb_irq12 = ctx->keyboard.cb_irq12 ? 1 : 0;
    kbd.cb_irq1 = ctx->keyboard.cb_irq1 ? 1 : 0;
    kbd.cb_xlat = ctx->keyboard.cb_xlat ? 1 : 0;
    kbd.cb_sys = ctx->keyboard.cb_sys ? 1 : 0;
    kbd.ps2_mouse_enabled = ctx->keyboard.ps2_mouse_enabled ? 1 : 0;
    kbd.a20_gate = ctx->keyboard.a20_gate ? 1 : 0;
    kbd.leftalt_pressed = ctx->keyboard.leftalt_pressed ? 1 : 0;
    kbd.rightalt_pressed = ctx->keyboard.rightalt_pressed ? 1 : 0;
    kbd.leftctrl_pressed = ctx->keyboard.leftctrl_pressed ? 1 : 0;
    kbd.rightctrl_pressed = ctx->keyboard.rightctrl_pressed ? 1 : 0;
    kbd.leftshift_pressed = ctx->keyboard.leftshift_pressed ? 1 : 0;
    kbd.rightshift_pressed = ctx->keyboard.rightshift_pressed ? 1 : 0;
    std::memcpy(ptr + header.keyboard_offset, &kbd, sizeof(kbd));

    // Serialize CPU state (H2: local struct + memcpy)
    dosbox::EngineStateCpu cpu{};
    cpu.cycles = ctx->cpu_state.cycles;
    cpu.cycle_left = ctx->cpu_state.cycle_left;
    cpu.cycle_max = ctx->cpu_state.cycle_max;
    cpu.cycle_old_max = ctx->cpu_state.cycle_old_max;
    cpu.cycle_percent_used = ctx->cpu_state.cycle_percent_used;
    cpu.cycle_limit = ctx->cpu_state.cycle_limit;
    cpu.cycle_up = ctx->cpu_state.cycle_up;
    cpu.cycle_down = ctx->cpu_state.cycle_down;
    cpu.cycles_set = ctx->cpu_state.cycles_set;
    cpu.io_delay_removed = ctx->cpu_state.io_delay_removed;
    cpu.extflags_toggle = ctx->cpu_state.extflags_toggle;
    cpu.cycle_auto_adjust = ctx->cpu_state.cycle_auto_adjust ? 1 : 0;
    cpu.skip_cycle_auto_adjust = ctx->cpu_state.skip_cycle_auto_adjust ? 1 : 0;
    cpu.nmi_gate = ctx->cpu_state.nmi_gate ? 1 : 0;
    cpu.nmi_active = ctx->cpu_state.nmi_active ? 1 : 0;
    cpu.nmi_pending = ctx->cpu_state.nmi_pending ? 1 : 0;
    cpu.halted = ctx->cpu_state.halted ? 1 : 0;
    std::memcpy(ptr + header.cpu_offset, &cpu, sizeof(cpu));

    // Serialize Memory state (H2: local struct + memcpy)
    dosbox::EngineStateMemory mem{};
    mem.size = ctx->memory.size;
    mem.pages = ctx->memory.pages;
    mem.handler_pages = ctx->memory.handler_pages;
    mem.reported_pages = ctx->memory.reported_pages;
    mem.reported_pages_4gb = ctx->memory.reported_pages_4gb;
    mem.lfb_start_page = ctx->memory.lfb.start_page;
    mem.lfb_end_page = ctx->memory.lfb.end_page;
    mem.lfb_pages = ctx->memory.lfb.pages;
    mem.lfb_mmio_start_page = ctx->memory.lfb_mmio.start_page;
    mem.lfb_mmio_end_page = ctx->memory.lfb_mmio.end_page;
    mem.lfb_mmio_pages = ctx->memory.lfb_mmio.pages;
    mem.mem_alias_pagemask = ctx->memory.mem_alias_pagemask;
    mem.mem_alias_pagemask_active = ctx->memory.mem_alias_pagemask_active;
    mem.address_bits = ctx->memory.address_bits;
    mem.hw_next_assign = ctx->memory.hw_next_assign;
    mem.a20_enabled = ctx->memory.a20.enabled ? 1 : 0;
    mem.a20_controlport = ctx->memory.a20.controlport;
    std::memcpy(ptr + header.memory_offset, &mem, sizeof(mem));

    // Serialize Mixer state [V4]
    dosbox::EngineStateMixer mixer{};
    mixer.freq = ctx->mixer.freq;
    mixer.blocksize = ctx->mixer.blocksize;
    mixer.master_vol[0] = ctx->mixer.mastervol[0];
    mixer.master_vol[1] = ctx->mixer.mastervol[1];
    mixer.record_vol[0] = ctx->mixer.recordvol[0];
    mixer.record_vol[1] = ctx->mixer.recordvol[1];
    mixer.samples = ctx->mixer.prebuffer_samples;
    mixer.enabled = ctx->mixer.enabled ? 1 : 0;
    mixer.nosound = ctx->mixer.nosound ? 1 : 0;
    mixer.swapstereo = ctx->mixer.swapstereo ? 1 : 0;
    mixer.mute = ctx->mixer.mute ? 1 : 0;
    mixer.sampleaccurate = ctx->mixer.sampleaccurate ? 1 : 0;
    std::memcpy(ptr + header.mixer_offset, &mixer, sizeof(mixer));

    // Serialize VGA state [V4]
    dosbox::EngineStateVga vga{};
    vga.width = ctx->vga.width;
    vga.height = ctx->vga.height;
    vga.bpp = ctx->vga.bpp;
    vga.mode = static_cast<uint8_t>(ctx->vga.mode);
    vga.svga_chip = static_cast<uint8_t>(ctx->vga.svga_chip);
    vga.render_on_demand = ctx->vga.render_on_demand ? 1 : 0;
    vga.refresh_rate = ctx->vga.refresh_rate;
    vga.frame_counter = ctx->vga.frame_counter;
    vga.dac_8bit = ctx->vga.dac_8bit ? 1 : 0;
    vga.vbe_enabled = ctx->vga.vbe_enabled ? 1 : 0;
    vga.text_mode = ctx->vga.text_mode ? 1 : 0;
    vga.cga_snow = ctx->vga.cga_snow ? 1 : 0;
    vga.vesa_flags = static_cast<uint8_t>(
        (ctx->vga.vesa_32bpp ? 0x01 : 0) |
        (ctx->vga.vesa_24bpp ? 0x02 : 0) |
        (ctx->vga.vesa_16bpp ? 0x04 : 0) |
        (ctx->vga.vesa_15bpp ? 0x08 : 0) |
        (ctx->vga.vesa_8bpp  ? 0x10 : 0) |
        (ctx->vga.vesa_4bpp  ? 0x20 : 0) |
        (ctx->vga.vesa_lowres ? 0x40 : 0) |
        (ctx->vga.vesa_hd    ? 0x80 : 0));
    std::memcpy(ptr + header.vga_offset, &vga, sizeof(vga));

    // Serialize DOS state [V4]
    dosbox::EngineStateDos dos{};
    dos.psp_segment = ctx->dos.psp_segment;
    dos.dta_segment = ctx->dos.dta_segment;
    dos.dta_offset = ctx->dos.dta_offset;
    dos.version_major = ctx->dos.version.major;
    dos.version_minor = ctx->dos.version.minor;
    dos.current_drive = ctx->dos.current_drive;
    dos.verify = ctx->dos.verify;
    dos.return_code = ctx->dos.return_code;
    dos.return_mode = ctx->dos.return_mode ? 1 : 0;
    dos.country = ctx->dos.country;
    dos.codepage = ctx->dos.codepage;
    dos.kernel_disabled = ctx->dos.kernel_disabled ? 1 : 0;
    dos.kernel_running = ctx->dos.kernel_running ? 1 : 0;
    std::memcpy(ptr + header.dos_offset, &dos, sizeof(dos));

    // Compute checksum over data after header
    const uint8_t* data_start = ptr + sizeof(dosbox::EngineStateHeader);
    size_t data_size = *size_out - sizeof(dosbox::EngineStateHeader);
    header.checksum = dosbox::compute_crc32(data_start, data_size);

    // Write header last (includes checksum)
    std::memcpy(ptr, &header, sizeof(header));

    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_load_state(
    dosbox_lib_handle_t handle,
    const void* buffer,
    size_t buffer_size
) {
    LIB_VALIDATE_HANDLE(handle);
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

    // Read header via memcpy (H2: avoid reinterpret_cast)
    dosbox::EngineStateHeader header{};
    std::memcpy(&header, ptr, sizeof(header));

    // Validate magic
    if (header.magic != dosbox::ENGINE_STATE_MAGIC) {
        g_last_error = "Invalid state magic number";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    // Forward-compatible version check (3.8):
    // reject future versions, accept current or older
    if (header.version > dosbox::ENGINE_STATE_VERSION) {
        g_last_error = "State version newer than supported";
        return DOSBOX_LIB_ERR_VERSION_MISMATCH;
    }

    // Validate total size - must be at least header size to prevent underflow
    if (header.total_size < sizeof(dosbox::EngineStateHeader)) {
        g_last_error = "State size smaller than header";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    if (buffer_size < header.total_size) {
        g_last_error = "Buffer smaller than stated total size";
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    // Verify checksum (safe now that we validated total_size >= header size)
    const uint8_t* data_start = ptr + sizeof(dosbox::EngineStateHeader);
    size_t data_size = header.total_size - sizeof(dosbox::EngineStateHeader);
    uint32_t computed_crc = dosbox::compute_crc32(data_start, data_size);
    if (computed_crc != header.checksum) {
        g_last_error = "Checksum mismatch - state corrupted";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    // Validate section offsets are within bounds
    auto validate_offset = [&](uint32_t off, size_t section_size) -> bool {
        return off >= sizeof(dosbox::EngineStateHeader) &&
               off + section_size <= header.total_size;
    };

    // V3: PIC section was 24 bytes; V4: expanded to 68 bytes
    size_t pic_section_size = (header.version <= 3)
        ? sizeof(dosbox::EngineStatePicV3)
        : sizeof(dosbox::EngineStatePic);

    if (!validate_offset(header.timing_offset, sizeof(dosbox::EngineStateTiming)) ||
        !validate_offset(header.pic_offset, pic_section_size) ||
        !validate_offset(header.keyboard_offset, sizeof(dosbox::EngineStateKeyboard)) ||
        !validate_offset(header.cpu_offset, sizeof(dosbox::EngineStateCpu)) ||
        !validate_offset(header.memory_offset, sizeof(dosbox::EngineStateMemory))) {
        g_last_error = "Invalid section offset";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    // V4 sections are optional for V3 loading
    bool has_v4_sections = header.version >= 4;
    if (has_v4_sections) {
        if (!validate_offset(header.mixer_offset, sizeof(dosbox::EngineStateMixer)) ||
            !validate_offset(header.vga_offset, sizeof(dosbox::EngineStateVga)) ||
            !validate_offset(header.dos_offset, sizeof(dosbox::EngineStateDos))) {
            g_last_error = "Invalid V4 section offset";
            return DOSBOX_LIB_ERR_INVALID_STATE;
        }
    }

    auto* ctx = g_context.get();

    // Deserialize timing state (H2: memcpy into local struct)
    dosbox::EngineStateTiming timing{};
    std::memcpy(&timing, ptr + header.timing_offset, sizeof(timing));
    ctx->timing.total_cycles = timing.total_cycles;
    ctx->timing.virtual_ticks_ms = timing.virtual_ticks_ms;
    ctx->timing.ticks_done = timing.ticks_done;
    ctx->timing.ticks_scheduled = timing.ticks_scheduled;
    ctx->timing.ticks_remain = timing.ticks_remain;
    ctx->timing.ticks_added = timing.ticks_added;
    ctx->timing.frame_ticks = timing.frame_ticks;
    ctx->timing.locked = timing.locked != 0;

    // Deserialize PIC state
    if (header.version <= 3) {
        // V3 backward compat: load abbreviated format
        dosbox::EngineStatePicV3 pic_v3{};
        std::memcpy(&pic_v3, ptr + header.pic_offset, sizeof(pic_v3));
        ctx->pic.ticks = pic_v3.ticks;
        ctx->pic.irq_check = pic_v3.irq_check;
        ctx->pic.irq_check_pending = pic_v3.irq_check_pending;
        ctx->pic.master_cascade_irq = pic_v3.master_cascade_irq;
        ctx->pic.controllers[0].imr = pic_v3.master_imr;
        ctx->pic.controllers[1].imr = pic_v3.slave_imr;
        ctx->pic.controllers[0].isr = pic_v3.master_isr;
        ctx->pic.controllers[1].isr = pic_v3.slave_isr;
        ctx->pic.controllers[0].auto_eoi = pic_v3.auto_eoi != 0;
        ctx->pic.in_event_service = pic_v3.in_event_service != 0;
    } else {
        // V4: full controller state
        dosbox::EngineStatePic pic{};
        std::memcpy(&pic, ptr + header.pic_offset, sizeof(pic));
        ctx->pic.ticks = pic.ticks;
        ctx->pic.irq_check = pic.irq_check;
        ctx->pic.irq_check_pending = pic.irq_check_pending;
        ctx->pic.master_cascade_irq = pic.master_cascade_irq;
        ctx->pic.in_event_service = pic.in_event_service != 0;
        ctx->pic.enable_slave_pic = pic.enable_slave_pic != 0;
        for (int c = 0; c < 2; ++c) {
            auto& src = pic.controllers[c];
            auto& dst = ctx->pic.controllers[c];
            dst.icw_words = src.icw_words;
            dst.icw_index = src.icw_index;
            dst.special = src.special != 0;
            dst.auto_eoi = src.auto_eoi != 0;
            dst.rotate_on_auto_eoi = src.rotate_on_auto_eoi != 0;
            dst.single = src.single != 0;
            dst.request_issr = src.request_issr != 0;
            dst.vector_base = src.vector_base;
            dst.input = src.input;
            dst.edge = src.edge;
            dst.irr = src.irr;
            dst.imr = src.imr;
            dst.imrr = src.imrr;
            dst.isr = src.isr;
            dst.isrr = src.isrr;
            dst.isr_ignore = src.isr_ignore;
            dst.active_irq = src.active_irq;
            dst.controller_index = src.controller_index;
        }
    }

    // Deserialize keyboard state (H2: memcpy; V3: 96 entries)
    dosbox::EngineStateKeyboard kbd{};
    std::memcpy(&kbd, ptr + header.keyboard_offset, sizeof(kbd));
    for (size_t i = 0; i < 96; ++i) {
        ctx->keyboard.buffer[i] = kbd.buffer[i];
    }
    ctx->keyboard.buffer_used = kbd.buffer_used;
    ctx->keyboard.buffer_pos = kbd.buffer_pos;
    ctx->keyboard.pending_key = kbd.pending_key;
    ctx->keyboard.repeat.key = kbd.repeat_key;
    ctx->keyboard.repeat.wait = kbd.repeat_wait;
    ctx->keyboard.repeat.pause = kbd.repeat_pause;
    ctx->keyboard.repeat.rate = kbd.repeat_rate;
    ctx->keyboard.led_state = kbd.led_state;
    std::memcpy(ctx->keyboard.buf8042, kbd.buf8042, 8);
    ctx->keyboard.buf8042_len = kbd.buf8042_len;
    ctx->keyboard.buf8042_pos = kbd.buf8042_pos;
    ctx->keyboard.scanset = kbd.scanset;
    ctx->keyboard.enabled = kbd.enabled != 0;
    ctx->keyboard.active = kbd.active != 0;
    ctx->keyboard.p60data = kbd.p60data;
    ctx->keyboard.p60changed = kbd.p60changed != 0;
    ctx->keyboard.num_lock = kbd.num_lock != 0;
    ctx->keyboard.caps_lock = kbd.caps_lock != 0;
    ctx->keyboard.scroll_lock = kbd.scroll_lock != 0;
    ctx->keyboard.command = kbd.command;
    ctx->keyboard.expecting_data = kbd.expecting_data != 0;
    ctx->keyboard.scanning = kbd.scanning != 0;
    ctx->keyboard.auxactive = kbd.auxactive != 0;
    ctx->keyboard.scheduled = kbd.scheduled != 0;
    ctx->keyboard.auxchanged = kbd.auxchanged != 0;
    ctx->keyboard.pending_key_state = kbd.pending_key_state != 0;
    ctx->keyboard.cb_override_inhibit = kbd.cb_override_inhibit != 0;
    ctx->keyboard.cb_irq12 = kbd.cb_irq12 != 0;
    ctx->keyboard.cb_irq1 = kbd.cb_irq1 != 0;
    ctx->keyboard.cb_xlat = kbd.cb_xlat != 0;
    ctx->keyboard.cb_sys = kbd.cb_sys != 0;
    ctx->keyboard.ps2_mouse_enabled = kbd.ps2_mouse_enabled != 0;
    ctx->keyboard.a20_gate = kbd.a20_gate != 0;
    ctx->keyboard.leftalt_pressed = kbd.leftalt_pressed != 0;
    ctx->keyboard.rightalt_pressed = kbd.rightalt_pressed != 0;
    ctx->keyboard.leftctrl_pressed = kbd.leftctrl_pressed != 0;
    ctx->keyboard.rightctrl_pressed = kbd.rightctrl_pressed != 0;
    ctx->keyboard.leftshift_pressed = kbd.leftshift_pressed != 0;
    ctx->keyboard.rightshift_pressed = kbd.rightshift_pressed != 0;

    // Deserialize CPU state (H2: memcpy into local struct)
    dosbox::EngineStateCpu cpu{};
    std::memcpy(&cpu, ptr + header.cpu_offset, sizeof(cpu));
    ctx->cpu_state.cycles = cpu.cycles;
    ctx->cpu_state.cycle_left = cpu.cycle_left;
    ctx->cpu_state.cycle_max = cpu.cycle_max;
    ctx->cpu_state.cycle_old_max = cpu.cycle_old_max;
    ctx->cpu_state.cycle_percent_used = cpu.cycle_percent_used;
    ctx->cpu_state.cycle_limit = cpu.cycle_limit;
    ctx->cpu_state.cycle_up = cpu.cycle_up;
    ctx->cpu_state.cycle_down = cpu.cycle_down;
    ctx->cpu_state.cycles_set = cpu.cycles_set;
    ctx->cpu_state.io_delay_removed = cpu.io_delay_removed;
    ctx->cpu_state.extflags_toggle = cpu.extflags_toggle;
    ctx->cpu_state.cycle_auto_adjust = cpu.cycle_auto_adjust != 0;
    ctx->cpu_state.skip_cycle_auto_adjust = cpu.skip_cycle_auto_adjust != 0;
    ctx->cpu_state.nmi_gate = cpu.nmi_gate != 0;
    ctx->cpu_state.nmi_active = cpu.nmi_active != 0;
    ctx->cpu_state.nmi_pending = cpu.nmi_pending != 0;
    ctx->cpu_state.halted = cpu.halted != 0;

    // Deserialize Memory state (H2: memcpy into local struct)
    dosbox::EngineStateMemory mem{};
    std::memcpy(&mem, ptr + header.memory_offset, sizeof(mem));
    ctx->memory.size = static_cast<size_t>(mem.size);
    ctx->memory.pages = mem.pages;
    ctx->memory.handler_pages = mem.handler_pages;
    ctx->memory.reported_pages = mem.reported_pages;
    ctx->memory.reported_pages_4gb = mem.reported_pages_4gb;
    ctx->memory.lfb.start_page = mem.lfb_start_page;
    ctx->memory.lfb.end_page = mem.lfb_end_page;
    ctx->memory.lfb.pages = mem.lfb_pages;
    ctx->memory.lfb_mmio.start_page = mem.lfb_mmio_start_page;
    ctx->memory.lfb_mmio.end_page = mem.lfb_mmio_end_page;
    ctx->memory.lfb_mmio.pages = mem.lfb_mmio_pages;
    ctx->memory.mem_alias_pagemask = mem.mem_alias_pagemask;
    ctx->memory.mem_alias_pagemask_active = mem.mem_alias_pagemask_active;
    ctx->memory.address_bits = mem.address_bits;
    ctx->memory.hw_next_assign = mem.hw_next_assign;
    ctx->memory.a20.enabled = mem.a20_enabled != 0;
    ctx->memory.a20.controlport = mem.a20_controlport;

    // Deserialize V4 sections (mixer, VGA, DOS)
    if (has_v4_sections) {
        // Mixer state
        dosbox::EngineStateMixer mixer{};
        std::memcpy(&mixer, ptr + header.mixer_offset, sizeof(mixer));
        ctx->mixer.freq = mixer.freq;
        ctx->mixer.blocksize = mixer.blocksize;
        ctx->mixer.mastervol[0] = mixer.master_vol[0];
        ctx->mixer.mastervol[1] = mixer.master_vol[1];
        ctx->mixer.recordvol[0] = mixer.record_vol[0];
        ctx->mixer.recordvol[1] = mixer.record_vol[1];
        ctx->mixer.prebuffer_samples = mixer.samples;
        ctx->mixer.enabled = mixer.enabled != 0;
        ctx->mixer.nosound = mixer.nosound != 0;
        ctx->mixer.swapstereo = mixer.swapstereo != 0;
        ctx->mixer.mute = mixer.mute != 0;
        ctx->mixer.sampleaccurate = mixer.sampleaccurate != 0;

        // VGA state
        dosbox::EngineStateVga vga{};
        std::memcpy(&vga, ptr + header.vga_offset, sizeof(vga));
        ctx->vga.width = vga.width;
        ctx->vga.height = vga.height;
        ctx->vga.bpp = vga.bpp;
        ctx->vga.mode = static_cast<dosbox::VgaMode>(vga.mode);
        ctx->vga.svga_chip = static_cast<dosbox::SvgaChip>(vga.svga_chip);
        ctx->vga.render_on_demand = vga.render_on_demand != 0;
        ctx->vga.refresh_rate = vga.refresh_rate;
        ctx->vga.frame_counter = vga.frame_counter;
        ctx->vga.dac_8bit = vga.dac_8bit != 0;
        ctx->vga.vbe_enabled = vga.vbe_enabled != 0;
        ctx->vga.text_mode = vga.text_mode != 0;
        ctx->vga.cga_snow = vga.cga_snow != 0;
        ctx->vga.vesa_32bpp = (vga.vesa_flags & 0x01) != 0;
        ctx->vga.vesa_24bpp = (vga.vesa_flags & 0x02) != 0;
        ctx->vga.vesa_16bpp = (vga.vesa_flags & 0x04) != 0;
        ctx->vga.vesa_15bpp = (vga.vesa_flags & 0x08) != 0;
        ctx->vga.vesa_8bpp  = (vga.vesa_flags & 0x10) != 0;
        ctx->vga.vesa_4bpp  = (vga.vesa_flags & 0x20) != 0;
        ctx->vga.vesa_lowres = (vga.vesa_flags & 0x40) != 0;
        ctx->vga.vesa_hd    = (vga.vesa_flags & 0x80) != 0;

        // DOS state
        dosbox::EngineStateDos dos{};
        std::memcpy(&dos, ptr + header.dos_offset, sizeof(dos));
        ctx->dos.psp_segment = dos.psp_segment;
        ctx->dos.dta_segment = dos.dta_segment;
        ctx->dos.dta_offset = dos.dta_offset;
        ctx->dos.version.major = dos.version_major;
        ctx->dos.version.minor = dos.version_minor;
        ctx->dos.current_drive = dos.current_drive;
        ctx->dos.verify = dos.verify;
        ctx->dos.return_code = dos.return_code;
        ctx->dos.return_mode = dos.return_mode != 0;
        ctx->dos.country = dos.country;
        ctx->dos.codepage = dos.codepage;
        ctx->dos.kernel_disabled = dos.kernel_disabled != 0;
        ctx->dos.kernel_running = dos.kernel_running != 0;
    } else {
        // V3 backward compat: initialize new sections to defaults
        ctx->mixer.reset();
        ctx->vga.reset();
        ctx->dos.reset();
    }

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
    LIB_VALIDATE_HANDLE(handle);
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
    LIB_VALIDATE_HANDLE(handle);
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
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Use the headless stub input functions which integrate with the PAL input system
    // Push motion and button events separately
    if (delta_x != 0 || delta_y != 0) {
        static_cast<void>(aibox::headless::PushMouseMotion(delta_x, delta_y));
    }

    // Handle button state changes (provider notification only)
    const bool buttons_changed = (buttons != g_mouse_last_buttons);
    if ((buttons & 0x01) != (g_mouse_last_buttons & 0x01)) {
        static_cast<void>(aibox::headless::PushMouseButton(0, (buttons & 0x01) != 0));  // Left button
    }
    if ((buttons & 0x02) != (g_mouse_last_buttons & 0x02)) {
        static_cast<void>(aibox::headless::PushMouseButton(1, (buttons & 0x02) != 0));  // Right button
    }
    if ((buttons & 0x04) != (g_mouse_last_buttons & 0x04)) {
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

    g_mouse_last_buttons = buttons;

    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// PIC State API
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_pic_state(
    dosbox_lib_handle_t handle,
    dosbox_lib_pic_state_t* state_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(state_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Read PIC state from engine context
    // Note: irq_check contains the pending IRQ bitmap (similar to IRR)
    state_out->master_irr = static_cast<uint8_t>(g_context->pic.irq_check & 0xFF);
    state_out->master_imr = g_context->pic.master_imr();
    state_out->master_isr = g_context->pic.master_isr();
    state_out->slave_irr = static_cast<uint8_t>((g_context->pic.irq_check >> 8) & 0xFF);
    state_out->slave_imr = g_context->pic.slave_imr();
    state_out->slave_isr = g_context->pic.slave_isr();

    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// VGA/Display State API (H8)
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_display_info(
    dosbox_lib_handle_t handle,
    dosbox_lib_display_info_t* info_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(info_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    const auto& vga = g_context->vga;
    info_out->width = vga.width;
    info_out->height = vga.height;
    info_out->bpp = vga.bpp;
    info_out->is_text_mode = vga.text_mode ? 1 : 0;
    // Default text dimensions — DOSBox-X text mode is 80x25 unless changed
    info_out->text_columns = 80;
    info_out->text_rows = 25;

    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// Memory Access API (Phase A)
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_read_memory(
    dosbox_lib_handle_t handle,
    uint32_t address,
    void* buffer,
    size_t size
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(buffer != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Bounds check against context memory
    if (g_context->memory.base == nullptr || size == 0) {
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }
    if (size > g_context->memory.size || address > g_context->memory.size - size) {
        g_last_error = "Memory read out of bounds";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    std::memcpy(buffer, g_context->memory.base + address, size);
    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_write_memory(
    dosbox_lib_handle_t handle,
    const void* buffer,
    uint32_t address,
    size_t size
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(buffer != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    if (g_context->memory.base == nullptr || size == 0) {
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }
    if (size > g_context->memory.size || address > g_context->memory.size - size) {
        g_last_error = "Memory write out of bounds";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    std::memcpy(g_context->memory.base + address, buffer, size);
    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// VGA Data Access API (Phase -1: Engine I/O Plumbing)
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_text_buffer(
    dosbox_lib_handle_t handle,
    uint16_t* buffer,
    size_t buffer_count,
    size_t* count_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(count_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Text mode: 80 columns × 25 rows = 2000 cells
    const size_t text_columns = 80;
    const size_t text_rows = 25;
    const size_t cell_count = text_columns * text_rows;
    *count_out = cell_count;

    if (buffer == nullptr) {
        return DOSBOX_LIB_OK;  // Query count only
    }

    if (buffer_count < cell_count) {
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    // Read VGA text memory at B8000h: each cell is 2 bytes (char + attr)
    // In the guest address space, text video memory starts at 0xB8000
    constexpr uint32_t TEXT_MEM_BASE = 0xB8000;
    const size_t byte_count = cell_count * 2;

    if (g_context->memory.base == nullptr ||
        TEXT_MEM_BASE + byte_count > g_context->memory.size) {
        g_last_error = "Text memory region not accessible";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    const uint8_t* text_mem = g_context->memory.base + TEXT_MEM_BASE;
    for (size_t i = 0; i < cell_count; ++i) {
        uint8_t ch = text_mem[i * 2];
        uint8_t attr = text_mem[i * 2 + 1];
        buffer[i] = static_cast<uint16_t>(ch) | (static_cast<uint16_t>(attr) << 8);
    }

    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_get_indexed_pixels(
    dosbox_lib_handle_t handle,
    uint8_t* buffer,
    size_t buffer_size,
    size_t* size_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(size_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    const auto& vga = g_context->vga;

    // Only support linear 8bpp modes (Mode 13h)
    if (!vga.is_linear_8bpp_mode()) {
        return DOSBOX_LIB_ERR_NOT_SUPPORTED;
    }

    const size_t pixel_count = static_cast<size_t>(vga.width) * vga.height;
    *size_out = pixel_count;

    if (buffer == nullptr) {
        return DOSBOX_LIB_OK;  // Query size only
    }

    if (buffer_size < pixel_count) {
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    size_t copied = vga.get_indexed_pixels(buffer, buffer_size);
    if (copied == 0) {
        g_last_error = "VGA linear memory not available";
        return DOSBOX_LIB_ERR_INVALID_STATE;
    }

    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_get_palette(
    dosbox_lib_handle_t handle,
    uint8_t rgb_out[768]
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(rgb_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    if (!g_context->vga.get_dac_palette(rgb_out)) {
        // VGA hardware not available (headless mode) — return default
        return DOSBOX_LIB_ERR_NOT_SUPPORTED;
    }

    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_get_font_data(
    dosbox_lib_handle_t handle,
    uint8_t* buffer,
    size_t buffer_size,
    size_t* size_out,
    uint8_t* char_height_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(size_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    // Query font size (also sets char_height_out)
    uint8_t ch_height = 16;
    size_t font_size = g_context->vga.get_font_data(nullptr, 0, &ch_height);

    if (font_size == 0) {
        // VGA hardware not available (headless mode)
        // Return default size so callers know the expected dimensions
        ch_height = 16;
        font_size = 256 * 16;
        *size_out = font_size;
        if (char_height_out != nullptr) *char_height_out = ch_height;
        return DOSBOX_LIB_ERR_NOT_SUPPORTED;
    }

    *size_out = font_size;
    if (char_height_out != nullptr) *char_height_out = ch_height;

    if (buffer == nullptr) {
        return DOSBOX_LIB_OK;  // Query size only
    }

    if (buffer_size < font_size) {
        return DOSBOX_LIB_ERR_BUFFER_TOO_SMALL;
    }

    g_context->vga.get_font_data(buffer, buffer_size, &ch_height);
    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// Audio API (Phase -1: Engine I/O Plumbing)
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_set_audio_enabled(
    dosbox_lib_handle_t /* handle */,
    int enabled
) {
    // This is a pre-create global setting; handle may be NULL
    g_audio_enabled = (enabled != 0);
    return DOSBOX_LIB_OK;
}

dosbox_lib_error_t dosbox_lib_get_audio_samples(
    dosbox_lib_handle_t handle,
    int16_t* buffer,
    size_t buffer_count,
    size_t* count_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(count_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    auto& audio = g_context->buffer_audio();

    if (buffer == nullptr) {
        // Query available sample count
        auto all = audio.get_all_samples();
        *count_out = all.size();
        return DOSBOX_LIB_OK;
    }

    // Pop requested number of samples from the ring buffer
    size_t to_pop = buffer_count;
    auto samples = audio.pop_samples(to_pop);
    *count_out = samples.size();

    if (!samples.empty()) {
        std::memcpy(buffer, samples.data(), samples.size() * sizeof(int16_t));
    }

    return DOSBOX_LIB_OK;
}

// ═══════════════════════════════════════════════════════════════════════════════
// Display API — Cursor
// ═══════════════════════════════════════════════════════════════════════════════

dosbox_lib_error_t dosbox_lib_get_cursor_info(
    dosbox_lib_handle_t handle,
    dosbox_lib_cursor_info_t* info_out
) {
    LIB_VALIDATE_HANDLE(handle);
    LIB_CHECK_THREAD();
    LIB_REQUIRE(info_out != nullptr, DOSBOX_LIB_ERR_NULL_POINTER);
    LIB_REQUIRE(g_instance_exists.load(), DOSBOX_LIB_ERR_NOT_INITIALIZED);
    LIB_REQUIRE(g_context != nullptr, DOSBOX_LIB_ERR_NOT_INITIALIZED);

    auto* mem_base = g_context->memory.base;
    if (mem_base == nullptr || g_context->memory.size < 0x500) {
        LIB_LOG_ERROR("Memory not initialized for BDA read");
        return DOSBOX_LIB_ERR_NOT_INITIALIZED;
    }

    // BDA segment 0x40 => physical offset 0x400
    constexpr uint32_t BDA_BASE = 0x400;

    // Active page: BDA offset 0x62
    uint8_t active_page = mem_base[BDA_BASE + 0x62];

    // Cursor position: BDA offset 0x50, 2 bytes per page (col, row)
    uint8_t col = mem_base[BDA_BASE + 0x50 + active_page * 2u];
    uint8_t row = mem_base[BDA_BASE + 0x50 + active_page * 2u + 1u];

    // Cursor type: BDA offset 0x60 (end scanline), 0x61 (start scanline)
    uint8_t cursor_end   = mem_base[BDA_BASE + 0x60];
    uint8_t cursor_start = mem_base[BDA_BASE + 0x61];

    // Hidden if start_line bit 5 is set
    uint8_t visible = (cursor_start & 0x20) ? 0 : 1;

    info_out->col = col;
    info_out->row = row;
    info_out->active_page = active_page;
    info_out->visible = visible;
    info_out->start_line = cursor_start & 0x1F;
    info_out->end_line = cursor_end;

    return DOSBOX_LIB_OK;
}

} // extern "C"
