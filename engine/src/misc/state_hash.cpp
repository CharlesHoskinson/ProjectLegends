/**
 * @file state_hash.cpp
 * @brief Implementation of state hashing for determinism verification.
 *
 * Contains:
 * - SHA-256 implementation (self-contained, no external dependencies)
 * - State hash computation for fast and full modes
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/state_hash.h"
#include "dosbox/error_model.h"
#include "dosbox/dosbox_context.h"

#include <cstring>
#include <cstdio>

// ═══════════════════════════════════════════════════════════════════════════════
// SHA-256 Constants
// ═══════════════════════════════════════════════════════════════════════════════

namespace {

// SHA-256 round constants
constexpr uint32_t K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

// SHA-256 initial hash values
constexpr uint32_t H_INIT[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

// Utility functions
inline uint32_t rotr(uint32_t x, int n) {
    return (x >> n) | (x << (32 - n));
}

inline uint32_t ch(uint32_t x, uint32_t y, uint32_t z) {
    return (x & y) ^ (~x & z);
}

inline uint32_t maj(uint32_t x, uint32_t y, uint32_t z) {
    return (x & y) ^ (x & z) ^ (y & z);
}

inline uint32_t sigma0(uint32_t x) {
    return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22);
}

inline uint32_t sigma1(uint32_t x) {
    return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25);
}

inline uint32_t gamma0(uint32_t x) {
    return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3);
}

inline uint32_t gamma1(uint32_t x) {
    return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10);
}

// Big-endian load/store
inline uint32_t load_be32(const uint8_t* p) {
    return (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) |
           (uint32_t(p[2]) << 8) | uint32_t(p[3]);
}

inline void store_be32(uint8_t* p, uint32_t v) {
    p[0] = uint8_t(v >> 24);
    p[1] = uint8_t(v >> 16);
    p[2] = uint8_t(v >> 8);
    p[3] = uint8_t(v);
}

inline void store_be64(uint8_t* p, uint64_t v) {
    store_be32(p, uint32_t(v >> 32));
    store_be32(p + 4, uint32_t(v));
}

} // anonymous namespace

// ═══════════════════════════════════════════════════════════════════════════════
// HashBuilder Implementation
// ═══════════════════════════════════════════════════════════════════════════════

namespace dosbox {

HashBuilder::HashBuilder() {
    reset();
}

void HashBuilder::reset() {
    for (int i = 0; i < 8; ++i) {
        state_[i] = H_INIT[i];
    }
    buffer_len_ = 0;
    total_len_ = 0;
}

void HashBuilder::process_block(const uint8_t block[64]) {
    uint32_t W[64];

    // Prepare message schedule
    for (int i = 0; i < 16; ++i) {
        W[i] = load_be32(block + i * 4);
    }
    for (int i = 16; i < 64; ++i) {
        W[i] = gamma1(W[i-2]) + W[i-7] + gamma0(W[i-15]) + W[i-16];
    }

    // Initialize working variables
    uint32_t a = state_[0];
    uint32_t b = state_[1];
    uint32_t c = state_[2];
    uint32_t d = state_[3];
    uint32_t e = state_[4];
    uint32_t f = state_[5];
    uint32_t g = state_[6];
    uint32_t h = state_[7];

    // Main loop
    for (int i = 0; i < 64; ++i) {
        uint32_t t1 = h + sigma1(e) + ch(e, f, g) + K[i] + W[i];
        uint32_t t2 = sigma0(a) + maj(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d + t1;
        d = c;
        c = b;
        b = a;
        a = t1 + t2;
    }

    // Update state
    state_[0] += a;
    state_[1] += b;
    state_[2] += c;
    state_[3] += d;
    state_[4] += e;
    state_[5] += f;
    state_[6] += g;
    state_[7] += h;
}

void HashBuilder::update(const void* data, size_t size) {
    const uint8_t* bytes = static_cast<const uint8_t*>(data);
    total_len_ += size;

    // Fill buffer and process
    while (size > 0) {
        size_t to_copy = std::min(size, size_t(64) - buffer_len_);
        std::memcpy(buffer_ + buffer_len_, bytes, to_copy);
        buffer_len_ += to_copy;
        bytes += to_copy;
        size -= to_copy;

        if (buffer_len_ == 64) {
            process_block(buffer_);
            buffer_len_ = 0;
        }
    }
}

StateHash HashBuilder::finalize() {
    // Padding
    uint64_t bit_len = total_len_ * 8;

    // Append 1 bit
    buffer_[buffer_len_++] = 0x80;

    // Pad to 56 bytes (mod 64)
    if (buffer_len_ > 56) {
        while (buffer_len_ < 64) {
            buffer_[buffer_len_++] = 0;
        }
        process_block(buffer_);
        buffer_len_ = 0;
    }
    while (buffer_len_ < 56) {
        buffer_[buffer_len_++] = 0;
    }

    // Append length
    store_be64(buffer_ + 56, bit_len);
    process_block(buffer_);

    // Output hash
    StateHash result;
    for (int i = 0; i < 8; ++i) {
        store_be32(&result[i * 4], state_[i]);
    }

    reset();
    return result;
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hashing Functions
// ═══════════════════════════════════════════════════════════════════════════════

// ─────────────────────────────────────────────────────────────────────────────
// Primary API: Explicit context parameter (Sprint 2 Phase 1)
// ─────────────────────────────────────────────────────────────────────────────

Result<StateHash> get_state_hash(DOSBoxContext* ctx, HashMode mode) {
    // Validate context
    if (!ctx) {
        return Err(Error(ErrorCode::InvalidArgument, "get_state_hash: null context"));
    }

    HashBuilder builder;

    // Version marker for hash stability
    // Increment when hash structure changes
    const uint32_t hash_version = 7;  // V7: Added Memory state (Sprint 2 Phase 2)
    builder.update(hash_version);

    // Mode marker
    const uint32_t mode_marker = static_cast<uint32_t>(mode);
    builder.update(mode_marker);

    // Hash context state
    // ─────────────────────────────────────────────────────────────────────
    // Timing State (PR #10)
    // ─────────────────────────────────────────────────────────────────────
    ctx->timing.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // CPU State (PR #11)
    // ─────────────────────────────────────────────────────────────────────
    ctx->cpu_state.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // Mixer State (PR #12)
    // ─────────────────────────────────────────────────────────────────────
    ctx->mixer.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // VGA State (PR #13)
    // ─────────────────────────────────────────────────────────────────────
    ctx->vga.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // PIC State (PR #14)
    // ─────────────────────────────────────────────────────────────────────
    ctx->pic.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // Keyboard State (PR #14)
    // ─────────────────────────────────────────────────────────────────────
    ctx->keyboard.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // Input Capture State (PR #14)
    // ─────────────────────────────────────────────────────────────────────
    ctx->input.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // Memory State (Sprint 2 Phase 2)
    // ─────────────────────────────────────────────────────────────────────
    ctx->memory.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────
    // DMA State (Sprint 2 Phase 3)
    // ─────────────────────────────────────────────────────────────────────
    ctx->dma.hash_into(builder);

    // ─────────────────────────────────────────────────────────────────────────
    // Placeholder for Future State (DOS, etc.)
    // ─────────────────────────────────────────────────────────────────────────

    // Fast mode will hash (future PRs):
    // - DOS state

    // Placeholder marker for state not yet migrated
    const char* placeholder = "STATE_HASH_V8";
    builder.update(placeholder, std::strlen(placeholder));

    // Full mode adds (future PRs):
    // - All conventional memory
    // - VGA registers and VRAM
    // - All device states
    if (mode == HashMode::Full) {
        const char* full_marker = "FULL_MODE";
        builder.update(full_marker, std::strlen(full_marker));
    }

    return Ok(builder.finalize());
}

// ─────────────────────────────────────────────────────────────────────────────
// Transitional API: Uses thread-local current_context() (deprecated)
// Retained for test compatibility during migration
// ─────────────────────────────────────────────────────────────────────────────

Result<StateHash> get_state_hash(HashMode mode) {
    // Use current context if available
    if (has_current_context()) {
        return get_state_hash(&current_context(), mode);
    }

    // No context - return placeholder hash for backward compatibility
    HashBuilder builder;

    const uint32_t hash_version = 7;  // V7: Added Memory state (Sprint 2 Phase 2)
    builder.update(hash_version);

    const uint32_t mode_marker = static_cast<uint32_t>(mode);
    builder.update(mode_marker);

    // No context available - use placeholder
    const char* no_ctx = "NO_CONTEXT";
    builder.update(no_ctx, std::strlen(no_ctx));

    const char* placeholder = "STATE_HASH_V6";
    builder.update(placeholder, std::strlen(placeholder));

    if (mode == HashMode::Full) {
        const char* full_marker = "FULL_MODE";
        builder.update(full_marker, std::strlen(full_marker));
    }

    return Ok(builder.finalize());
}

std::string hash_to_hex(const StateHash& hash) {
    static const char hex_chars[] = "0123456789abcdef";
    std::string result;
    result.reserve(64);

    for (uint8_t byte : hash) {
        result.push_back(hex_chars[byte >> 4]);
        result.push_back(hex_chars[byte & 0x0f]);
    }

    return result;
}

} // namespace dosbox

// ═══════════════════════════════════════════════════════════════════════════════
// C API Implementation
// ═══════════════════════════════════════════════════════════════════════════════

extern "C" {

int dosbox_get_state_hash(uint8_t out[DOSBOX_HASH_SIZE], dosbox_hash_mode mode) {
    if (!out) {
        return DOSBOX_ERR_INVALID_ARGUMENT;
    }

    auto result = dosbox::get_state_hash(static_cast<dosbox::HashMode>(mode));
    if (!result.has_value()) {
        return static_cast<int>(result.error().code());
    }

    std::memcpy(out, result.value().data(), DOSBOX_HASH_SIZE);
    return DOSBOX_OK;
}

int dosbox_hash_to_hex(const uint8_t hash[DOSBOX_HASH_SIZE],
                       char* out, size_t out_size) {
    if (!hash || !out) {
        return DOSBOX_ERR_INVALID_ARGUMENT;
    }
    if (out_size < 65) {  // 64 hex chars + null
        return DOSBOX_ERR_BUFFER_TOO_SMALL;
    }

    dosbox::StateHash arr;
    std::memcpy(arr.data(), hash, DOSBOX_HASH_SIZE);

    std::string hex = dosbox::hash_to_hex(arr);
    std::memcpy(out, hex.c_str(), 65);

    return DOSBOX_OK;
}

int dosbox_hash_equal(const uint8_t hash1[DOSBOX_HASH_SIZE],
                      const uint8_t hash2[DOSBOX_HASH_SIZE]) {
    if (!hash1 || !hash2) {
        return 0;
    }
    return std::memcmp(hash1, hash2, DOSBOX_HASH_SIZE) == 0 ? 1 : 0;
}

} // extern "C"
