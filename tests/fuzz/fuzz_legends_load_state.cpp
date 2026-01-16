/**
 * @file fuzz_legends_load_state.cpp
 * @brief libFuzzer target for legends_load_state().
 *
 * Fuzzes the save state deserialization to find:
 * - Buffer overflows
 * - Integer overflows in offset calculations
 * - Null pointer dereferences
 * - Undefined behavior
 *
 * Build with:
 *   cmake -B build -DENABLE_FUZZING=ON -DCMAKE_CXX_COMPILER=clang++
 *   cmake --build build --target fuzz_legends_load_state
 *
 * Run with:
 *   ./build/tests/fuzz/fuzz_legends_load_state corpus/ -max_len=8192
 */

#include <legends/legends_embed.h>
#include <cstdint>
#include <cstddef>

// Persistent handle for faster fuzzing (avoid create/destroy overhead)
static legends_handle g_handle = nullptr;
static bool g_initialized = false;

static void ensure_initialized() {
    if (!g_initialized) {
        // First destroy any existing instance
        legends_destroy(reinterpret_cast<legends_handle>(1));

        auto err = legends_create(nullptr, &g_handle);
        if (err != LEGENDS_OK) {
            // Can't fuzz without a valid handle
            __builtin_trap();
        }
        g_initialized = true;
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    ensure_initialized();

    // Fuzz the load_state parser with arbitrary data
    // This should never crash - only return error codes
    legends_load_state(g_handle, data, size);

    // Reset state for next iteration to avoid state accumulation
    legends_reset(g_handle);

    return 0;
}

// Optional: Custom mutator that understands the save state format
// This can help find bugs faster by generating semi-valid inputs
extern "C" size_t LLVMFuzzerCustomMutator(
    uint8_t* data, size_t size, size_t max_size, unsigned int seed) {

    // Use default mutator most of the time
    extern size_t LLVMFuzzerMutate(uint8_t* data, size_t size, size_t max_size);
    size_t new_size = LLVMFuzzerMutate(data, size, max_size);

    // Occasionally fix up the magic number to get past initial validation
    // This helps explore deeper code paths
    if ((seed % 10) == 0 && new_size >= 4) {
        // LEGS magic: 0x4C454753
        data[0] = 0x53;  // 'S'
        data[1] = 0x47;  // 'G'
        data[2] = 0x45;  // 'E'
        data[3] = 0x4C;  // 'L'
    }

    // Occasionally fix up version to explore version-specific paths
    if ((seed % 20) == 0 && new_size >= 8) {
        data[4] = 2;  // Version 2
        data[5] = 0;
        data[6] = 0;
        data[7] = 0;
    }

    return new_size;
}
