/**
 * @file state_hash.h
 * @brief State hashing API for DOSBox-X determinism verification.
 *
 * This implements the state hash API defined in LIBRARY_CONTRACT.md:
 * - dosbox_get_state_hash() returns SHA-256 of observable state
 * - Two modes: fast (key structs only) and full (comprehensive)
 * - Used to verify deterministic execution across runs
 *
 * Usage:
 *   uint8_t hash[32];
 *   dosbox_get_state_hash(handle, hash, DOSBOX_HASH_FAST);
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_STATE_HASH_H
#define DOSBOX_STATE_HASH_H

#include <cstdint>
#include <cstddef>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Hash mode for state hashing.
 */
typedef enum dosbox_hash_mode {
    /**
     * @brief Fast mode - hash key determinism-relevant state only.
     *
     * Includes: CPU registers, cycle counters, PIC state, timing.
     * Use for: Local development, quick verification.
     * Speed: ~1ms typical
     */
    DOSBOX_HASH_FAST = 0,

    /**
     * @brief Full mode - comprehensive state hash.
     *
     * Includes: All of fast mode plus memory, VGA state, device state.
     * Use for: CI verification, save/load round-trip tests.
     * Speed: ~10-100ms depending on memory size
     */
    DOSBOX_HASH_FULL = 1
} dosbox_hash_mode;

/**
 * @brief Size of the state hash output (SHA-256 = 32 bytes).
 */
#define DOSBOX_HASH_SIZE 32

/**
 * @brief Compute hash of current emulator state.
 *
 * The hash is deterministic: same state produces same hash.
 * Use this to verify deterministic execution.
 *
 * @param out       Output buffer for hash (must be DOSBOX_HASH_SIZE bytes)
 * @param mode      Hash mode (DOSBOX_HASH_FAST or DOSBOX_HASH_FULL)
 * @return          DOSBOX_OK on success, error code on failure
 *
 * @note In V1 (single instance), the handle parameter is reserved.
 *       Pass NULL or any value; it is ignored.
 */
int dosbox_get_state_hash(uint8_t out[DOSBOX_HASH_SIZE], dosbox_hash_mode mode);

/**
 * @brief Get human-readable hex string of hash.
 *
 * @param hash      Hash bytes (DOSBOX_HASH_SIZE)
 * @param out       Output buffer (must be at least 65 bytes for hex + null)
 * @param out_size  Size of output buffer
 * @return          DOSBOX_OK on success, error code on failure
 */
int dosbox_hash_to_hex(const uint8_t hash[DOSBOX_HASH_SIZE],
                       char* out, size_t out_size);

/**
 * @brief Compare two hashes for equality.
 *
 * @param hash1     First hash
 * @param hash2     Second hash
 * @return          1 if equal, 0 if different
 */
int dosbox_hash_equal(const uint8_t hash1[DOSBOX_HASH_SIZE],
                      const uint8_t hash2[DOSBOX_HASH_SIZE]);

#ifdef __cplusplus
} /* extern "C" */
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C++ API
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef __cplusplus

#include "dosbox/error_model.h"
#include <array>
#include <string>
#include <span>

namespace dosbox {

/**
 * @brief Hash mode enum (C++ wrapper).
 */
enum class HashMode {
    Fast = DOSBOX_HASH_FAST,
    Full = DOSBOX_HASH_FULL
};

/**
 * @brief State hash type (32-byte array).
 */
using StateHash = std::array<uint8_t, DOSBOX_HASH_SIZE>;

// Forward declaration
class DOSBoxContext;

/**
 * @brief Compute hash of emulator state from explicit context.
 *
 * This is the preferred API - takes context explicitly rather than
 * using thread-local current_context().
 *
 * @param ctx   DOSBox context to hash (must not be null)
 * @param mode  Hash mode
 * @return      Result containing hash or error
 */
[[nodiscard]] Result<StateHash> get_state_hash(DOSBoxContext* ctx, HashMode mode = HashMode::Fast);

/**
 * @brief Compute hash of current emulator state (transitional API).
 *
 * Uses thread-local current_context(). Prefer get_state_hash(ctx, mode)
 * for new code. This overload is retained for test compatibility.
 *
 * @param mode  Hash mode
 * @return      Result containing hash or error
 *
 * @deprecated Use get_state_hash(DOSBoxContext*, HashMode) instead
 */
[[nodiscard]] Result<StateHash> get_state_hash(HashMode mode = HashMode::Fast);

/**
 * @brief Convert hash to hex string.
 */
[[nodiscard]] std::string hash_to_hex(const StateHash& hash);

/**
 * @brief Compare two hashes for equality.
 */
[[nodiscard]] inline bool hash_equal(const StateHash& a, const StateHash& b) {
    return a == b;
}

// ─────────────────────────────────────────────────────────────────────────────
// Hash Builder (for internal use and testing)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Incremental hash builder using SHA-256.
 *
 * Used internally to build state hashes incrementally.
 * Also useful for testing.
 */
class HashBuilder {
public:
    HashBuilder();
    ~HashBuilder() = default;

    HashBuilder(const HashBuilder&) = delete;
    HashBuilder& operator=(const HashBuilder&) = delete;
    HashBuilder(HashBuilder&&) = default;
    HashBuilder& operator=(HashBuilder&&) = default;

    /**
     * @brief Add data to the hash.
     */
    void update(const void* data, size_t size);

    /**
     * @brief Add typed value to the hash.
     */
    template<typename T>
    void update(const T& value) {
        static_assert(std::is_trivially_copyable_v<T>,
            "HashBuilder::update requires trivially copyable type");
        update(&value, sizeof(T));
    }

    /**
     * @brief Add span of data to the hash.
     */
    void update(std::span<const uint8_t> data) {
        update(data.data(), data.size());
    }

    /**
     * @brief Finalize and get the hash.
     *
     * After calling finalize(), the builder is reset.
     */
    [[nodiscard]] StateHash finalize();

    /**
     * @brief Reset to initial state.
     */
    void reset();

private:
    // SHA-256 state (8 x 32-bit words)
    uint32_t state_[8];
    // Pending data buffer
    uint8_t buffer_[64];
    // Bytes in buffer
    size_t buffer_len_;
    // Total bytes processed
    uint64_t total_len_;

    void process_block(const uint8_t block[64]);
};

} // namespace dosbox

#endif /* __cplusplus */

#endif /* DOSBOX_STATE_HASH_H */
