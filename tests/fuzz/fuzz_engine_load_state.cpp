/**
 * @file fuzz_engine_load_state.cpp
 * @brief libFuzzer target for dosbox_lib_load_state().
 *
 * Fuzzes the engine state deserialization directly to find:
 * - Buffer overflows in engine state parsing
 * - Integer overflows in section offset calculations
 * - CRC validation bypass attempts
 * - Memory corruption
 *
 * Build with:
 *   cmake -B build -DENABLE_FUZZING=ON -DCMAKE_CXX_COMPILER=clang++
 *   cmake --build build --target fuzz_engine_load_state
 *
 * Run with:
 *   ./build/tests/fuzz/fuzz_engine_load_state corpus/ -max_len=1024
 */

#include "dosbox/dosbox_library.h"
#include "dosbox/engine_state.h"
#include <cstdint>
#include <cstddef>

// Persistent handle for faster fuzzing
static dosbox_lib_handle_t g_handle = nullptr;
static bool g_initialized = false;

static void ensure_initialized() {
    if (!g_initialized) {
        // Destroy any existing instance
        dosbox_lib_destroy(g_handle);

        auto err = dosbox_lib_create(nullptr, &g_handle);
        if (err != DOSBOX_LIB_OK) {
            __builtin_trap();
        }

        err = dosbox_lib_init(g_handle);
        if (err != DOSBOX_LIB_OK) {
            __builtin_trap();
        }

        g_initialized = true;
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    ensure_initialized();

    // Fuzz the engine load_state parser
    dosbox_lib_load_state(g_handle, data, size);

    // Reset for next iteration
    dosbox_lib_reset(g_handle);

    return 0;
}

// Custom mutator that understands engine state format
extern "C" size_t LLVMFuzzerCustomMutator(
    uint8_t* data, size_t size, size_t max_size, unsigned int seed) {

    extern size_t LLVMFuzzerMutate(uint8_t* data, size_t size, size_t max_size);
    size_t new_size = LLVMFuzzerMutate(data, size, max_size);

    // Occasionally fix up magic to explore deeper paths
    if ((seed % 10) == 0 && new_size >= 4) {
        // DBXE magic: 0x45584244
        data[0] = 0x44;  // 'D'
        data[1] = 0x42;  // 'B'
        data[2] = 0x58;  // 'X'
        data[3] = 0x45;  // 'E'
    }

    // Occasionally set correct version
    if ((seed % 20) == 0 && new_size >= 8) {
        data[4] = dosbox::ENGINE_STATE_VERSION;
        data[5] = 0;
        data[6] = 0;
        data[7] = 0;
    }

    // Occasionally set plausible total_size
    if ((seed % 15) == 0 && new_size >= 12) {
        uint32_t total = static_cast<uint32_t>(new_size);
        data[8] = total & 0xFF;
        data[9] = (total >> 8) & 0xFF;
        data[10] = (total >> 16) & 0xFF;
        data[11] = (total >> 24) & 0xFF;
    }

    return new_size;
}
