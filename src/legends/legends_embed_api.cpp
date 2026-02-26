/**
 * @file legends_embed_api.cpp
 * @brief Embeddable DOSBox-X API - Implementation
 *
 * Phase 1: Core lifecycle functions (version, create, destroy)
 * Phase 2: Deterministic stepping (step_ms, step_cycles, time queries)
 * Phase 3: Frame capture (text, RGB, dirty tracking, cursor)
 * Phase 4+: Input, save/load (stubs)
 *
 * Sprint 2: All per-instance state lives in struct legends_instance.
 * The single remaining global is g_active_instance (atomic pointer).
 *
 * NOTE: This implementation bridges to the DOSBox-X engine library
 * (engine/include/dosbox/dosbox_library.h) for core emulation.
 * The legends_* functions delegate to dosbox_lib_* functions.
 */

#include "legends/legends_embed.h"
#include "legends/machine_context.h"
#include "legends/vision_framebuffer.h"
#include "legends/safe_arithmetic.h"

// Sprint 2: Per-instance state
#include "internal/legends_instance.h"

// DOSBox-X Engine Bridge (PR #22)
#include "dosbox/dosbox_library.h"
#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4244) // C4244 from STL templates in dosbox_context.h inlines
#endif
#include "dosbox/dosbox_context.h"
#ifdef _MSC_VER
#pragma warning(pop)
#endif
#include "dosbox/error_mapping.h"

#include <atomic>
#include <cstring>
#include <memory>
#include <string>
#include <array>
#include <vector>
#include <cstdint>
#include <thread>

// Import internal types into file scope for use in anonymous namespace and API functions
using legends::internal::LogState;
using legends::internal::TimeState;
using legends::internal::FrameState;
using legends::internal::InputEventType;
using legends::internal::InputEvent;
using legends::internal::InputState;
using legends::internal::EventKind;
using legends::internal::ScheduledEvent;
using legends::internal::PICState;
using legends::internal::DMAChannelState;
using legends::internal::EventQueueState;
using legends::internal::WIRE_INPUT_EVENT_SIZE;
using legends::internal::WIRE_DMA_CHANNEL_SIZE;
using legends::internal::serialize_input_event;
using legends::internal::deserialize_input_event;

// ─────────────────────────────────────────────────────────────────────────────
// Single Global: Active instance pointer
// ─────────────────────────────────────────────────────────────────────────────
static std::atomic<legends_instance*> g_active_instance{nullptr};

// Thread-local error for pre-creation error reporting
static thread_local std::string g_pre_creation_error;

/**
 * @brief Validate handle and return the active instance.
 *
 * Returns the instance pointer if handle is valid and matches the active
 * instance. Returns nullptr otherwise.
 */
static legends_instance* get_instance(legends_handle handle) noexcept {
    auto* inst = g_active_instance.load(std::memory_order_acquire);
    return (inst && handle == inst) ? inst : nullptr;
}

namespace {

// ─────────────────────────────────────────────────────────────────────────────
// Save State Format - Versioned, determinism-preserving
// Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
// ─────────────────────────────────────────────────────────────────────────────

// Magic number: "DBXS" (DOSBox-X Save)
constexpr uint32_t SAVESTATE_MAGIC = 0x53584244;  // "DBXS" in little-endian
constexpr uint32_t SAVESTATE_VERSION = 3;  // Version 3: Unified input queue, portable serialization

// ─────────────────────────────────────────────────────────────────────────────
// Portable Serialization Helpers (little-endian, cross-platform)
// Uses little-endian byte shifts - fully portable across platforms
// ─────────────────────────────────────────────────────────────────────────────

// Little-endian write helpers (using byte shifts - fully portable)
inline void write_u8(uint8_t* dst, uint8_t v) { *dst = v; }
inline void write_u16_le(uint8_t* dst, uint16_t v) {
    dst[0] = static_cast<uint8_t>(v & 0xFF);
    dst[1] = static_cast<uint8_t>((v >> 8) & 0xFF);
}
inline void write_u32_le(uint8_t* dst, uint32_t v) {
    dst[0] = static_cast<uint8_t>(v & 0xFF);
    dst[1] = static_cast<uint8_t>((v >> 8) & 0xFF);
    dst[2] = static_cast<uint8_t>((v >> 16) & 0xFF);
    dst[3] = static_cast<uint8_t>((v >> 24) & 0xFF);
}
inline void write_u64_le(uint8_t* dst, uint64_t v) {
    for (int i = 0; i < 8; ++i) {
        dst[i] = static_cast<uint8_t>((v >> (i * 8)) & 0xFF);
    }
}
inline void write_i16_le(uint8_t* dst, int16_t v) { write_u16_le(dst, static_cast<uint16_t>(v)); }
inline void write_bool(uint8_t* dst, bool v) { *dst = v ? 1 : 0; }

// Little-endian read helpers
inline uint8_t read_u8(const uint8_t* src) { return *src; }
inline uint16_t read_u16_le(const uint8_t* src) {
    return static_cast<uint16_t>(src[0]) | (static_cast<uint16_t>(src[1]) << 8);
}
inline uint32_t read_u32_le(const uint8_t* src) {
    return static_cast<uint32_t>(src[0]) |
           (static_cast<uint32_t>(src[1]) << 8) |
           (static_cast<uint32_t>(src[2]) << 16) |
           (static_cast<uint32_t>(src[3]) << 24);
}
inline uint64_t read_u64_le(const uint8_t* src) {
    uint64_t v = 0;
    for (int i = 0; i < 8; ++i) {
        v |= static_cast<uint64_t>(src[i]) << (i * 8);
    }
    return v;
}
inline int16_t read_i16_le(const uint8_t* src) { return static_cast<int16_t>(read_u16_le(src)); }
inline bool read_bool(const uint8_t* src) { return *src != 0; }

} // anonymous namespace (temporarily close for externally-visible serialization)

// Portable serialization for unified InputEvent
// Defined in legends::internal namespace to match declaration in instance_state.h
namespace legends::internal {

void serialize_input_event(uint8_t* dst, const InputEvent& evt) {
    write_u8(dst + 0, static_cast<uint8_t>(evt.type));
    std::memset(dst + 1, 0, 7);  // padding for alignment
    write_u64_le(dst + 8, evt.sequence);

    if (evt.type == InputEventType::Key) {
        write_u8(dst + 16, evt.key.scancode);
        write_bool(dst + 17, evt.key.is_down);
        write_bool(dst + 18, evt.key.is_extended);
        std::memset(dst + 19, 0, 5);  // remaining padding
    } else if (evt.type == InputEventType::Mouse) {
        write_i16_le(dst + 16, evt.mouse.delta_x);
        write_i16_le(dst + 18, evt.mouse.delta_y);
        write_u8(dst + 20, evt.mouse.buttons);
        std::memset(dst + 21, 0, 3);  // remaining padding
    } else {
        std::memset(dst + 16, 0, 8);  // zero padding for unknown types
    }
}

InputEvent deserialize_input_event(const uint8_t* src) {
    InputEvent evt{};
    evt.type = static_cast<InputEventType>(read_u8(src + 0));
    evt.sequence = read_u64_le(src + 8);

    if (evt.type == InputEventType::Key) {
        evt.key.scancode = read_u8(src + 16);
        evt.key.is_down = read_bool(src + 17);
        evt.key.is_extended = read_bool(src + 18);
    } else if (evt.type == InputEventType::Mouse) {
        evt.mouse.delta_x = read_i16_le(src + 16);
        evt.mouse.delta_y = read_i16_le(src + 18);
        evt.mouse.buttons = read_u8(src + 20);
    }
    return evt;
}

} // namespace legends::internal

namespace { // re-open anonymous namespace

// Portable serialization for DMAChannelState
void serialize_dma_channel(uint8_t* dst, const DMAChannelState& ch) {
    write_u16_le(dst + 0, ch.count);
    uint8_t flags = (ch.enabled ? 0x01 : 0) | (ch.masked ? 0x02 : 0) |
                    (ch.request ? 0x04 : 0) | (ch.tc_reached ? 0x08 : 0) |
                    (ch.autoinit ? 0x10 : 0);
    write_u8(dst + 2, flags);
    write_u8(dst + 3, 0);  // padding
}

DMAChannelState deserialize_dma_channel(const uint8_t* src) {
    DMAChannelState ch{};
    ch.count = read_u16_le(src);
    uint8_t flags = read_u8(src + 2);
    ch.enabled = (flags & 0x01) != 0;
    ch.masked = (flags & 0x02) != 0;
    ch.request = (flags & 0x04) != 0;
    ch.tc_reached = (flags & 0x08) != 0;
    ch.autoinit = (flags & 0x10) != 0;
    return ch;
}

// Save state header (fixed size, at start of buffer)
struct SaveStateHeader {
    uint32_t magic;            // SAVESTATE_MAGIC
    uint32_t version;          // SAVESTATE_VERSION
    uint32_t total_size;       // Total size including header
    uint32_t checksum;         // CRC32 of data after header

    // Section offsets (from start of buffer)
    uint32_t time_offset;
    uint32_t cpu_offset;
    uint32_t pic_offset;
    uint32_t dma_offset;
    uint32_t event_queue_offset;
    uint32_t input_offset;
    uint32_t frame_offset;
    uint32_t engine_offset;    // Engine state offset (0 if not present)
    uint32_t engine_size;      // Engine state size in bytes
    uint32_t _reserved[3];
};
static_assert(sizeof(SaveStateHeader) == 64, "SaveStateHeader must be 64 bytes");

// Time state section
struct SaveStateTime {
    uint64_t total_cycles;
    uint64_t emu_time_us;
    uint32_t cycles_per_ms;
    uint32_t _pad;
};
static_assert(sizeof(SaveStateTime) == 24, "SaveStateTime must be 24 bytes");

// CPU state section - matches TLA+ CPU fields
struct SaveStateCPU {
    uint8_t interrupt_flag;    // CPU.IF
    uint8_t halted;            // CPU.halted
    uint8_t mode;              // CPU.mode (0=Real, 1=Protected, 2=V86)
    uint8_t _pad;
    uint32_t _reserved[3];
};
static_assert(sizeof(SaveStateCPU) == 16, "SaveStateCPU must be 16 bytes");

// PIC state section (for both PICs)
struct SaveStatePIC {
    PICState pics[2];
};
static_assert(sizeof(SaveStatePIC) == 16, "SaveStatePIC must be 16 bytes");

// DMA state section
struct SaveStateDMA {
    DMAChannelState channels[8];
};
static_assert(sizeof(SaveStateDMA) == 32, "SaveStateDMA must be 32 bytes");

// Event queue section header
struct SaveStateEventQueueHeader {
    uint32_t event_count;
    uint32_t next_event_id;
    // Followed by event_count * sizeof(ScheduledEvent) bytes
};

// Input state section header (V3: unified queue)
struct SaveStateInputHeader {
    uint32_t event_count;       // Total events in unified queue
    uint32_t next_sequence_lo;  // Lower 32 bits of next_sequence
    uint32_t next_sequence_hi;  // Upper 32 bits of next_sequence
    uint32_t _reserved;         // Padding for alignment
    // Followed by event_count * WIRE_INPUT_EVENT_SIZE bytes
};

// ─────────────────────────────────────────────────────────────────────────────
// V2 Legacy Structures (for backward compatibility)
// WARNING: These use raw memcpy and are NOT portable across platforms/compilers
// ─────────────────────────────────────────────────────────────────────────────

struct SaveStateInputHeader_V2 {
    uint32_t key_queue_size;
    uint32_t mouse_queue_size;
    // Followed by key events then mouse events
};

// V2 used separate event types with implementation-defined sizes
struct KeyEvent_V2 {
    uint8_t scancode;
    bool is_down;
    bool is_extended;
};

struct MouseEvent_V2 {
    int16_t delta_x;
    int16_t delta_y;
    uint8_t buttons;
};

// V2 queue limits (used for validation)
constexpr size_t V2_MAX_KEY_EVENTS = 256;
constexpr size_t V2_MAX_MOUSE_EVENTS = 64;

// Frame state section header
struct SaveStateFrameHeader {
    uint8_t is_text_mode;
    uint8_t columns;
    uint8_t rows;
    uint8_t cursor_x;
    uint8_t cursor_y;
    uint8_t cursor_visible;
    uint8_t active_page;
    uint8_t _pad;
    uint16_t gfx_width;
    uint16_t gfx_height;
    uint32_t text_buffer_size;   // In bytes
    uint32_t indexed_pixels_size; // In bytes
    // Followed by text_buffer and indexed_pixels data
};

// ─────────────────────────────────────────────────────────────────────────────
// SHA-256 Implementation (minimal, for state hashing)
// ─────────────────────────────────────────────────────────────────────────────

class SHA256 {
public:
    static constexpr size_t DIGEST_SIZE = 32;
    static constexpr size_t BLOCK_SIZE = 64;

    SHA256() { reset(); }

    void reset() {
        state_[0] = 0x6a09e667;
        state_[1] = 0xbb67ae85;
        state_[2] = 0x3c6ef372;
        state_[3] = 0xa54ff53a;
        state_[4] = 0x510e527f;
        state_[5] = 0x9b05688c;
        state_[6] = 0x1f83d9ab;
        state_[7] = 0x5be0cd19;
        count_ = 0;
        buffer_len_ = 0;
    }

    void update(const void* data, size_t len) {
        const uint8_t* ptr = static_cast<const uint8_t*>(data);
        count_ += len;

        // Process buffered data
        if (buffer_len_ > 0) {
            size_t fill = BLOCK_SIZE - buffer_len_;
            if (len < fill) {
                std::memcpy(buffer_ + buffer_len_, ptr, len);
                buffer_len_ += len;
                return;
            }
            std::memcpy(buffer_ + buffer_len_, ptr, fill);
            transform(buffer_);
            ptr += fill;
            len -= fill;
            buffer_len_ = 0;
        }

        // Process full blocks
        while (len >= BLOCK_SIZE) {
            transform(ptr);
            ptr += BLOCK_SIZE;
            len -= BLOCK_SIZE;
        }

        // Buffer remaining
        if (len > 0) {
            std::memcpy(buffer_, ptr, len);
            buffer_len_ = len;
        }
    }

    void finalize(uint8_t digest[DIGEST_SIZE]) {
        // Pad message
        uint8_t pad[BLOCK_SIZE];
        size_t pad_len = (buffer_len_ < 56) ? (56 - buffer_len_) : (120 - buffer_len_);

        pad[0] = 0x80;
        std::memset(pad + 1, 0, pad_len - 1);

        // Append length in bits (big-endian)
        uint64_t bits = count_ * 8;
        uint8_t len_bytes[8];
        for (int i = 0; i < 8; ++i) {
            len_bytes[7 - i] = static_cast<uint8_t>(bits >> (i * 8));
        }

        update(pad, pad_len);
        update(len_bytes, 8);

        // Output digest (big-endian)
        for (int i = 0; i < 8; ++i) {
            digest[i * 4 + 0] = static_cast<uint8_t>(state_[i] >> 24);
            digest[i * 4 + 1] = static_cast<uint8_t>(state_[i] >> 16);
            digest[i * 4 + 2] = static_cast<uint8_t>(state_[i] >> 8);
            digest[i * 4 + 3] = static_cast<uint8_t>(state_[i]);
        }
    }

private:
    uint32_t state_[8];
    uint64_t count_;
    uint8_t buffer_[BLOCK_SIZE];
    size_t buffer_len_;

    static constexpr uint32_t K[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    };

    static uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
    static uint32_t ch(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ (~x & z); }
    static uint32_t maj(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ (x & z) ^ (y & z); }
    static uint32_t sigma0(uint32_t x) { return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22); }
    static uint32_t sigma1(uint32_t x) { return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25); }
    static uint32_t gamma0(uint32_t x) { return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3); }
    static uint32_t gamma1(uint32_t x) { return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10); }

    void transform(const uint8_t* block) {
        uint32_t w[64];

        // Load block (big-endian)
        for (int i = 0; i < 16; ++i) {
            w[i] = (static_cast<uint32_t>(block[i * 4]) << 24) |
                   (static_cast<uint32_t>(block[i * 4 + 1]) << 16) |
                   (static_cast<uint32_t>(block[i * 4 + 2]) << 8) |
                   static_cast<uint32_t>(block[i * 4 + 3]);
        }

        // Expand
        for (int i = 16; i < 64; ++i) {
            w[i] = gamma1(w[i - 2]) + w[i - 7] + gamma0(w[i - 15]) + w[i - 16];
        }

        // Initialize working variables
        uint32_t a = state_[0], b = state_[1], c = state_[2], d = state_[3];
        uint32_t e = state_[4], f = state_[5], g = state_[6], h = state_[7];

        // Main loop
        for (int i = 0; i < 64; ++i) {
            uint32_t t1 = h + sigma1(e) + ch(e, f, g) + K[i] + w[i];
            uint32_t t2 = sigma0(a) + maj(a, b, c);
            h = g; g = f; f = e; e = d + t1;
            d = c; c = b; b = a; a = t1 + t2;
        }

        // Update state
        state_[0] += a; state_[1] += b; state_[2] += c; state_[3] += d;
        state_[4] += e; state_[5] += f; state_[6] += g; state_[7] += h;
    }
};

constexpr uint32_t SHA256::K[64];

// ─────────────────────────────────────────────────────────────────────────────
// CRC32 for checksum (simple implementation)
// ─────────────────────────────────────────────────────────────────────────────

uint32_t crc32(const void* data, size_t len) {
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
    for (size_t i = 0; i < len; ++i) {
        crc = table[(crc ^ ptr[i]) & 0xFF] ^ (crc >> 8);
    }
    return crc ^ 0xFFFFFFFF;
}

// ─────────────────────────────────────────────────────────────────────────────
// ASCII to Scancode Mapping (US keyboard layout)
// ─────────────────────────────────────────────────────────────────────────────

// Scancode mapping for ASCII characters
// Format: {scancode, needs_shift}
struct ScancodeMapping {
    uint8_t scancode;
    bool needs_shift;
};

// US QWERTY keyboard layout scancode table
// Index by ASCII code (0-127)
constexpr ScancodeMapping ASCII_TO_SCANCODE[128] = {
    // 0x00-0x0F: Control characters
    {0x00, false}, {0x00, false}, {0x00, false}, {0x00, false},  // NUL, SOH, STX, ETX
    {0x00, false}, {0x00, false}, {0x00, false}, {0x00, false},  // EOT, ENQ, ACK, BEL
    {0x0E, false}, {0x0F, false}, {0x1C, false}, {0x00, false},  // BS=0x0E, TAB=0x0F, LF->Enter
    {0x00, false}, {0x1C, false}, {0x00, false}, {0x00, false},  // FF, CR->Enter, SO, SI
    // 0x10-0x1F: More control characters
    {0x00, false}, {0x00, false}, {0x00, false}, {0x00, false},
    {0x00, false}, {0x00, false}, {0x00, false}, {0x00, false},
    {0x00, false}, {0x00, false}, {0x00, false}, {0x01, false},  // ESC = 0x01
    {0x00, false}, {0x00, false}, {0x00, false}, {0x00, false},
    // 0x20-0x2F: Space and punctuation
    {0x39, false}, // ' ' Space
    {0x02, true},  // '!' Shift+1
    {0x28, true},  // '"' Shift+'
    {0x04, true},  // '#' Shift+3
    {0x05, true},  // '$' Shift+4
    {0x06, true},  // '%' Shift+5
    {0x08, true},  // '&' Shift+7
    {0x28, false}, // '\'' apostrophe
    {0x0A, true},  // '(' Shift+9
    {0x0B, true},  // ')' Shift+0
    {0x09, true},  // '*' Shift+8
    {0x0D, true},  // '+' Shift+=
    {0x33, false}, // ',' comma
    {0x0C, false}, // '-' minus
    {0x34, false}, // '.' period
    {0x35, false}, // '/' slash
    // 0x30-0x39: Digits 0-9
    {0x0B, false}, // '0'
    {0x02, false}, // '1'
    {0x03, false}, // '2'
    {0x04, false}, // '3'
    {0x05, false}, // '4'
    {0x06, false}, // '5'
    {0x07, false}, // '6'
    {0x08, false}, // '7'
    {0x09, false}, // '8'
    {0x0A, false}, // '9'
    // 0x3A-0x40: More punctuation
    {0x27, true},  // ':' Shift+;
    {0x27, false}, // ';' semicolon
    {0x33, true},  // '<' Shift+,
    {0x0D, false}, // '=' equals
    {0x34, true},  // '>' Shift+.
    {0x35, true},  // '?' Shift+/
    {0x03, true},  // '@' Shift+2
    // 0x41-0x5A: Uppercase A-Z (need shift)
    {0x1E, true},  // 'A'
    {0x30, true},  // 'B'
    {0x2E, true},  // 'C'
    {0x20, true},  // 'D'
    {0x12, true},  // 'E'
    {0x21, true},  // 'F'
    {0x22, true},  // 'G'
    {0x23, true},  // 'H'
    {0x17, true},  // 'I'
    {0x24, true},  // 'J'
    {0x25, true},  // 'K'
    {0x26, true},  // 'L'
    {0x32, true},  // 'M'
    {0x31, true},  // 'N'
    {0x18, true},  // 'O'
    {0x19, true},  // 'P'
    {0x10, true},  // 'Q'
    {0x13, true},  // 'R'
    {0x1F, true},  // 'S'
    {0x14, true},  // 'T'
    {0x16, true},  // 'U'
    {0x2F, true},  // 'V'
    {0x11, true},  // 'W'
    {0x2D, true},  // 'X'
    {0x15, true},  // 'Y'
    {0x2C, true},  // 'Z'
    // 0x5B-0x60: Brackets and backquote
    {0x1A, false}, // '[' left bracket
    {0x2B, false}, // '\' backslash
    {0x1B, false}, // ']' right bracket
    {0x07, true},  // '^' Shift+6
    {0x0C, true},  // '_' Shift+-
    {0x29, false}, // '`' backtick
    // 0x61-0x7A: Lowercase a-z (no shift)
    {0x1E, false}, // 'a'
    {0x30, false}, // 'b'
    {0x2E, false}, // 'c'
    {0x20, false}, // 'd'
    {0x12, false}, // 'e'
    {0x21, false}, // 'f'
    {0x22, false}, // 'g'
    {0x23, false}, // 'h'
    {0x17, false}, // 'i'
    {0x24, false}, // 'j'
    {0x25, false}, // 'k'
    {0x26, false}, // 'l'
    {0x32, false}, // 'm'
    {0x31, false}, // 'n'
    {0x18, false}, // 'o'
    {0x19, false}, // 'p'
    {0x10, false}, // 'q'
    {0x13, false}, // 'r'
    {0x1F, false}, // 's'
    {0x14, false}, // 't'
    {0x16, false}, // 'u'
    {0x2F, false}, // 'v'
    {0x11, false}, // 'w'
    {0x2D, false}, // 'x'
    {0x15, false}, // 'y'
    {0x2C, false}, // 'z'
    // 0x7B-0x7F: Braces and special
    {0x1A, true},  // '{' Shift+[
    {0x2B, true},  // '|' Shift+backslash
    {0x1B, true},  // '}' Shift+]
    {0x29, true},  // '~' Shift+`
    {0x00, false}, // DEL (0x7F)
};

// Left Shift scancode
constexpr uint8_t SCANCODE_LSHIFT = 0x2A;

// ─────────────────────────────────────────────────────────────────────────────
// FFI Exception Boundary - safe_call wrapper
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Safe call wrapper for FFI boundary.
 *
 * Catches all C++ exceptions and converts them to error codes.
 * This ensures no exceptions escape to C code which would be undefined behavior.
 *
 * Usage:
 *   return safe_call([&]() {
 *       // C++ code that might throw
 *       return LEGENDS_OK;
 *   });
 */
template<typename Func>
legends_error_t safe_call(legends_instance* inst, Func&& func) noexcept {
    try {
        return func();
    } catch (const std::bad_alloc&) {
        if (inst) { inst->last_error = "Out of memory"; inst->log_state.error("Out of memory"); }
        return LEGENDS_ERR_OUT_OF_MEMORY;
    } catch (const std::exception& e) {
        if (inst) { inst->last_error = e.what(); inst->log_state.error(e.what()); }
        return LEGENDS_ERR_INTERNAL;
    } catch (...) {
        if (inst) { inst->last_error = "Unknown internal error"; inst->log_state.error("Unknown internal error"); }
        return LEGENDS_ERR_INTERNAL;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper Macros
// ─────────────────────────────────────────────────────────────────────────────

// Validate boundary conditions - returns error, recoverable
#define LEGENDS_REQUIRE(cond, err) \
    do { if (!(cond)) return (err); } while(0)

// Check that caller is on the owner thread (requires `inst` in scope)
#define LEGENDS_CHECK_THREAD() \
    do { \
        if (inst && std::this_thread::get_id() != inst->owner_thread_id) { \
            inst->last_error = "Called from non-owner thread"; \
            return LEGENDS_ERR_WRONG_THREAD; \
        } \
    } while(0)

// Set error message, log it, and return error code (requires `inst` in scope)
// Undef if already defined (error.h may have it)
#ifdef LEGENDS_ERROR
#undef LEGENDS_ERROR
#endif
#define LEGENDS_ERROR(err, msg) \
    do { \
        if (inst) { inst->last_error = (msg); inst->log_state.error(msg); } \
        return (err); \
    } while(0)

// Aliases for aibox macro compatibility (SAFE_MULTIPLY_OR_ERROR uses these)
#define DOSBOXX_ERROR LEGENDS_ERROR
#define DOSBOXX_ERR_INVALID_STATE LEGENDS_ERR_INVALID_STATE

// ─────────────────────────────────────────────────────────────────────────────
// Save State Bounds Validation Macros (P0 Security Fix)
// ─────────────────────────────────────────────────────────────────────────────

// Validate that a fixed-size section fits within buffer bounds
// Checks for overflow: offset + size could wrap around on 32-bit
#define VALIDATE_SECTION_BOUNDS(offset, section_type, buf_size) \
    do { \
        if ((offset) > (buf_size) || \
            sizeof(section_type) > (buf_size) - (offset)) { \
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, \
                "Section offset out of bounds: " #offset); \
        } \
    } while(0)

// Validate that variable-size data fits within buffer bounds
// data_size is from untrusted input, must check for overflow
#define VALIDATE_DATA_BOUNDS(offset, data_size, buf_size) \
    do { \
        if ((offset) > (buf_size) || \
            (data_size) > (buf_size) - (offset)) { \
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, \
                "Data section exceeds buffer bounds at offset: " #offset); \
        } \
    } while(0)

// Validate that a count doesn't exceed a maximum (prevents huge allocations)
#define VALIDATE_COUNT_MAX(count, max_val, name) \
    do { \
        if ((count) > (max_val)) { \
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, \
                "Count exceeds maximum for " name); \
        } \
    } while(0)

// Maximum size for indexed pixels buffer (4MB - enough for 2048x2048)
constexpr size_t MAX_INDEXED_PIXELS_SIZE = 4 * 1024 * 1024;

// Log at various levels (requires `inst` in scope)
#define LEGENDS_LOG_INFO(msg) do { if (inst) inst->log_state.info(msg); } while(0)
#define LEGENDS_LOG_DEBUG(msg) do { if (inst) inst->log_state.debug(msg); } while(0)
#define LEGENDS_LOG_WARN(msg) do { if (inst) inst->log_state.warn(msg); } while(0)

} // anonymous namespace

extern "C" {

// Forward declarations for internal helper functions
void sync_state_from_engine(legends_instance* inst);
void sync_state_to_engine(legends_instance* inst);
size_t get_engine_state_size(legends_instance* inst);
legends_error_t drain_input_to_engine(legends_instance* inst, uint32_t* count_out);

/* =========================================================================
 * LIFECYCLE API
 * ========================================================================= */

legends_error_t legends_get_api_version(
    uint32_t* major,
    uint32_t* minor,
    uint32_t* patch
) {
    LEGENDS_REQUIRE(major != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(minor != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(patch != nullptr, LEGENDS_ERR_NULL_POINTER);

    *major = LEGENDS_API_VERSION_MAJOR;
    *minor = LEGENDS_API_VERSION_MINOR;
    *patch = LEGENDS_API_VERSION_PATCH;

    return LEGENDS_OK;
}

legends_error_t legends_create(
    const legends_config_t* config,
    legends_handle* handle_out
) {
    // inst is nullptr here (no instance yet) — macros that use inst will null-check
    legends_instance* inst = nullptr;

    LEGENDS_REQUIRE(handle_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    // Initialize output to null
    *handle_out = nullptr;

    // Allocate new instance (make_unique provides exception-safe allocation)
    std::unique_ptr<legends_instance> owned_inst;
    try {
        owned_inst = std::make_unique<legends_instance>();
    } catch (const std::bad_alloc&) {
        g_pre_creation_error = "Out of memory allocating instance";
        return LEGENDS_ERR_OUT_OF_MEMORY;
    }

    // Single instance enforcement using atomic compare-exchange
    legends_instance* expected = nullptr;
    if (!g_active_instance.compare_exchange_strong(expected, owned_inst.get(),
            std::memory_order_acq_rel, std::memory_order_acquire)) {
        // owned_inst destructor handles cleanup automatically
        if (expected && expected->log_state.callback) {
            try {
                expected->log_state.callback(
                    0,  // LOG_LEVEL_ERROR
                    "Instance already exists - only one instance per process allowed",
                    expected->log_state.userdata);
            } catch (...) {
                // Cannot propagate exceptions across C ABI boundary
            }
        }
        g_pre_creation_error = "Instance already exists - only one instance per process allowed";
        return LEGENDS_ERR_ALREADY_CREATED;
    }

    // CAS succeeded — release ownership to the atomic, inst is now the raw pointer
    inst = owned_inst.release();

    // Store owner thread ID for thread affinity checking
    inst->owner_thread_id = std::this_thread::get_id();

    // Validate config if provided
    if (config != nullptr) {
        if (config->struct_size != sizeof(legends_config_t)) {
            g_active_instance.store(nullptr, std::memory_order_release);
            delete inst;
            g_pre_creation_error = "Invalid config struct size";
            return LEGENDS_ERR_INVALID_CONFIG;
        }
        if (config->api_version != LEGENDS_API_VERSION) {
            g_active_instance.store(nullptr, std::memory_order_release);
            delete inst;
            g_pre_creation_error = "API version mismatch";
            return LEGENDS_ERR_VERSION_MISMATCH;
        }
        if (config->cpu_cycles != 0 &&
            (config->cpu_cycles < 100 || config->cpu_cycles > 1000000)) {
            g_active_instance.store(nullptr, std::memory_order_release);
            delete inst;
            g_pre_creation_error = "cpu_cycles out of range (0=auto, or 100..1000000)";
            return LEGENDS_ERR_INVALID_CONFIG;
        }
        // Store config (deep copy strings so caller can free originals)
        inst->config = *config;
        if (config->config_path) {
            inst->config_path_owned = config->config_path;
            inst->config.config_path = inst->config_path_owned.c_str();
        }
        if (config->working_dir) {
            inst->working_dir_owned = config->working_dir;
            inst->config.working_dir = inst->working_dir_owned.c_str();
        }
    } else {
        // Use defaults
        inst->config = legends_config_t{};
        inst->config.struct_size = sizeof(legends_config_t);
        inst->config.api_version = LEGENDS_API_VERSION;
        inst->config.memory_kb = 640;
        inst->config.cpu_cycles = 3000;  // Default cycles per ms
        inst->config.deterministic = 1;
    }

    try {
        // Create machine configuration from legends_config
        legends::MachineConfig mc;
        mc.memory_size = static_cast<size_t>(inst->config.memory_kb) * 1024;
        mc.cpu_cycles = inst->config.cpu_cycles > 0 ? inst->config.cpu_cycles : 3000;
        mc.deterministic = (inst->config.deterministic != 0);

        // Map machine type
        switch (inst->config.machine_type) {
            case 0: mc.machine_type = legends::MachineType::VGA; break;
            case 1: mc.machine_type = legends::MachineType::EGA; break;
            case 2: mc.machine_type = legends::MachineType::CGA; break;
            case 3: mc.machine_type = legends::MachineType::Hercules; break;
            case 4: mc.machine_type = legends::MachineType::Tandy; break;
            default: mc.machine_type = legends::MachineType::VGA; break;
        }

        // Create and initialize machine context
        inst->machine = std::make_unique<legends::MachineContext>(mc);
        auto result = inst->machine->initialize();
        if (!result.has_value()) {
            inst->last_error = result.error().format();
            inst->machine.reset();
            g_active_instance.store(nullptr, std::memory_order_release);
            delete inst;
            return LEGENDS_ERR_INTERNAL;
        }

        // Enable audio before engine creation (Phase -1)
        dosbox_lib_set_audio_enabled(nullptr, 1);

        // Initialize DOSBox-X Engine Bridge (PR #22)
        dosbox_lib_config_t engine_config = DOSBOX_LIB_CONFIG_INIT;
        engine_config.memory_kb = inst->config.memory_kb;
        engine_config.cpu_cycles = inst->config.cpu_cycles;
        engine_config.deterministic = inst->config.deterministic;

        auto engine_err = dosbox_lib_create(&engine_config, &inst->engine_handle);
        if (engine_err != DOSBOX_LIB_OK) {
            inst->last_error = "Failed to create DOSBox-X engine";
            inst->machine.reset();
            g_active_instance.store(nullptr, std::memory_order_release);
            delete inst;
            return dosbox_to_legends_error(engine_err);
        }

        engine_err = dosbox_lib_init(inst->engine_handle);
        if (engine_err != DOSBOX_LIB_OK) {
            dosbox_lib_destroy(inst->engine_handle);
            inst->engine_handle = nullptr;
            inst->last_error = "Failed to initialize DOSBox-X engine";
            inst->machine.reset();
            g_active_instance.store(nullptr, std::memory_order_release);
            delete inst;
            return dosbox_to_legends_error(engine_err);
        }

        // Initialize time state
        inst->time_state.reset();
        inst->time_state.cycles_per_ms = mc.cpu_cycles;

        // Initialize frame state with test pattern and embedded font.
        // The test pattern provides visible content ("C:\>") immediately.
        // The embedded CP437 font ensures proper text rendering even when
        // engine VGA hardware is unavailable (headless mode).
        // Once the engine boots and provides real VGA data, sync_state_from_engine()
        // will overwrite these with actual engine state.
        inst->frame_state.reset();
        inst->frame_state.init_test_pattern();
        inst->frame_state.load_embedded_font();

        // Initialize input state
        inst->input_state.reset();

        // Return real pointer as handle
        *handle_out = inst;
        inst->last_error.clear();

        LEGENDS_LOG_INFO("DOSBox-X instance created successfully (with engine bridge)");
        return LEGENDS_OK;

    } catch (const std::exception& e) {
        inst->last_error = e.what();
        inst->machine.reset();
        g_active_instance.store(nullptr, std::memory_order_release);
        delete inst;
        return LEGENDS_ERR_INTERNAL;
    }
}

legends_error_t legends_destroy(legends_handle handle) {
    // Allow destroying null handle (no-op)
    if (handle == nullptr) {
        return LEGENDS_OK;
    }

    auto* inst = get_instance(handle);
    if (inst == nullptr) {
        return LEGENDS_ERR_NULL_HANDLE;
    }

    // Verify caller is on owner thread
    LEGENDS_CHECK_THREAD();

    LEGENDS_LOG_INFO("Destroying DOSBox-X instance");

    // Shutdown and destroy machine context
    if (inst->machine) {
        inst->machine->shutdown();
        inst->machine.reset();
    }

    // Destroy DOSBox-X Engine Bridge (PR #22)
    if (inst->engine_handle != nullptr) {
        dosbox_lib_destroy(inst->engine_handle);
        inst->engine_handle = nullptr;
    }

    // Clean up all per-instance state
    inst->destroy_cleanup();

    // Null out the global and delete via unique_ptr (RAII cleanup)
    g_active_instance.store(nullptr, std::memory_order_release);
    delete inst;

    return LEGENDS_OK;
}

legends_error_t legends_force_destroy(void) {
    auto* inst = g_active_instance.load(std::memory_order_acquire);
    if (inst == nullptr) {
        return LEGENDS_OK;
    }
    return legends_destroy(reinterpret_cast<legends_handle>(inst));
}

legends_error_t legends_reset(legends_handle handle) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    if (inst->in_step) { return LEGENDS_ERR_REENTRANT_CALL; }
    LEGENDS_REQUIRE(inst->machine != nullptr, LEGENDS_ERR_NOT_INITIALIZED);

    try {
        auto result = inst->machine->reset();
        if (!result.has_value()) {
            inst->last_error = result.error().format();
            return LEGENDS_ERR_INTERNAL;
        }

        // Reset engine state for determinism
        if (inst->engine_handle) {
            auto engine_err = dosbox_lib_reset(inst->engine_handle);
            if (engine_err != DOSBOX_LIB_OK) {
                inst->last_error = "Failed to reset engine state";
                return dosbox_to_legends_error(engine_err);
            }
        }

        // Reset all per-instance state
        inst->reset_state();

        // Reinitialize frame state with test pattern
        inst->frame_state.init_test_pattern();

        inst->last_error.clear();
        return LEGENDS_OK;

    } catch (const std::exception& e) {
        inst->last_error = e.what();
        return LEGENDS_ERR_INTERNAL;
    }
}

legends_error_t legends_get_config(
    legends_handle handle,
    legends_config_t* config_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(config_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    *config_out = inst->config;
    return LEGENDS_OK;
}

/* =========================================================================
 * STEPPING API - Phase 2 Implementation
 * ========================================================================= */

legends_error_t legends_step_cycles(
    legends_handle handle,
    uint64_t cycles,
    legends_step_result_t* result_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(inst->machine != nullptr, LEGENDS_ERR_NOT_INITIALIZED);
    LEGENDS_REQUIRE(inst->engine_handle != nullptr, LEGENDS_ERR_NOT_INITIALIZED);

    // Reentrancy guard (M1): reject if already inside a step call
    // (e.g., called from a log callback)
    if (inst->in_step) {
        inst->last_error = "Reentrant call to step function";
        return LEGENDS_ERR_REENTRANT_CALL;
    }
    inst->in_step = true;
    // Scope guard: clear in_step on all exit paths
    struct StepGuard { bool& flag; ~StepGuard() { flag = false; } } step_guard{inst->in_step};

    try {
        // Set dosbox context TLS pointer so compat shims resolve during
        // the entire step scope (including input draining).
        void* raw_ctx = nullptr;
        auto ctx_err = dosbox_lib_get_context_ptr(inst->engine_handle, &raw_ctx);
        if (ctx_err != DOSBOX_LIB_OK || raw_ctx == nullptr) {
            inst->last_error = "Failed to get engine context pointer";
            if (result_out != nullptr) {
                result_out->stop_reason = LEGENDS_STOP_ERROR;
            }
            return (ctx_err != DOSBOX_LIB_OK) ? dosbox_to_legends_error(ctx_err)
                                               : LEGENDS_ERR_NOT_INITIALIZED;
        }
        auto* dctx = static_cast<dosbox::DOSBoxContext*>(raw_ctx);
        dosbox::ContextGuard dosbox_guard(*dctx);

        // Set aibox context for compatibility shim (still needed for legacy code paths)
        legends::compat::ContextGuard legend_guard(*inst->machine);

        // Drain input queue before stepping to preserve device interleaving order
        legends_error_t drain_err = drain_input_to_engine(inst, nullptr);
        if (drain_err != LEGENDS_OK) {
            inst->last_error = "Input injection failed";
            if (result_out != nullptr) {
                result_out->stop_reason = LEGENDS_STOP_ERROR;
            }
            return drain_err;
        }

        // Delegate to the DOSBox library
        dosbox_lib_step_result_t engine_result{};
        auto err = dosbox_lib_step_cycles(inst->engine_handle, cycles, &engine_result);

        if (err != DOSBOX_LIB_OK) {
            inst->last_error = "Engine step_cycles failed";
            if (result_out != nullptr) {
                result_out->stop_reason = LEGENDS_STOP_ERROR;
            }
            return dosbox_to_legends_error(err);
        }

        // Map engine stop reason to legends stop reason
        uint32_t stop_reason = LEGENDS_STOP_COMPLETED;
        switch (engine_result.stop_reason) {
            case DOSBOX_LIB_STOP_COMPLETED:
                stop_reason = LEGENDS_STOP_COMPLETED;
                break;
            case DOSBOX_LIB_STOP_HALT:
                stop_reason = LEGENDS_STOP_HALT;
                break;
            case DOSBOX_LIB_STOP_BREAKPOINT:
                stop_reason = LEGENDS_STOP_BREAKPOINT;
                break;
            case DOSBOX_LIB_STOP_ERROR:
                stop_reason = LEGENDS_STOP_ERROR;
                break;
            case DOSBOX_LIB_STOP_USER_REQUEST:
                stop_reason = LEGENDS_STOP_USER_REQUEST;
                break;
            case DOSBOX_LIB_STOP_CALLBACK:
                stop_reason = LEGENDS_STOP_COMPLETED;
                break;
            default:
                stop_reason = LEGENDS_STOP_ERROR;
                break;
        }

        // Sync legends layer state from engine
        sync_state_from_engine(inst);

        // Fill result if requested
        if (result_out != nullptr) {
            result_out->cycles_executed = engine_result.cycles_executed;
            result_out->emu_time_us = inst->time_state.emu_time_us;
            result_out->stop_reason = stop_reason;
            result_out->events_processed = engine_result.events_processed;
        }

        inst->last_error.clear();
        return LEGENDS_OK;

    } catch (const std::exception& e) {
        inst->last_error = e.what();
        if (result_out != nullptr) {
            result_out->stop_reason = LEGENDS_STOP_ERROR;
        }
        return LEGENDS_ERR_INTERNAL;
    }
}

legends_error_t legends_step_ms(
    legends_handle handle,
    uint32_t ms,
    legends_step_result_t* result_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();

    // Convert milliseconds to cycles using fixed ratio for determinism
    uint64_t target_cycles = inst->time_state.ms_to_cycles(ms);

    // Delegate to cycle-based stepping
    return legends_step_cycles(handle, target_cycles, result_out);
}

legends_error_t legends_get_emu_time(
    legends_handle handle,
    uint64_t* time_us_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(time_us_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    *time_us_out = inst->time_state.emu_time_us;
    return LEGENDS_OK;
}

legends_error_t legends_get_total_cycles(
    legends_handle handle,
    uint64_t* cycles_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(cycles_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    *cycles_out = inst->time_state.total_cycles;
    return LEGENDS_OK;
}

/* =========================================================================
 * FRAME CAPTURE API - Phase 3 Implementation
 * ========================================================================= */

legends_error_t legends_capture_text(
    legends_handle handle,
    legends_text_cell_t* cells,
    size_t cells_count,
    size_t* cells_count_out,
    legends_text_info_t* info_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(cells_count_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    size_t required_cells = inst->frame_state.text_cell_count();
    *cells_count_out = required_cells;

    if (info_out != nullptr) {
        info_out->columns = inst->frame_state.columns;
        info_out->rows = inst->frame_state.rows;
        info_out->active_page = inst->frame_state.active_page;
        info_out->cursor_x = inst->frame_state.cursor_x;
        info_out->cursor_y = inst->frame_state.cursor_y;
        info_out->cursor_visible = inst->frame_state.cursor_visible ? 1 : 0;
        info_out->cursor_start = inst->frame_state.cursor_start;
        info_out->cursor_end = inst->frame_state.cursor_end;
    }

    if (cells == nullptr) {
        return LEGENDS_OK;
    }

    if (cells_count < required_cells) {
        return LEGENDS_ERR_BUFFER_TOO_SMALL;
    }

    for (size_t i = 0; i < required_cells; ++i) {
        uint16_t cell = inst->frame_state.text_buffer[i];
        cells[i].character = static_cast<uint8_t>(cell & 0xFF);
        cells[i].attribute = static_cast<uint8_t>((cell >> 8) & 0xFF);
    }

    inst->frame_state.dirty = false;

    return LEGENDS_OK;
}

legends_error_t legends_capture_rgb(
    legends_handle handle,
    uint8_t* buffer,
    size_t buffer_size,
    size_t* size_out,
    uint16_t* width_out,
    uint16_t* height_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(size_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    uint16_t width, height;

    if (inst->frame_state.is_text_mode) {
        width = inst->frame_state.columns * 8;
        height = inst->frame_state.rows * inst->frame_state.char_height;
    } else {
        width = inst->frame_state.gfx_width;
        height = inst->frame_state.gfx_height;
    }

    constexpr uint16_t MAX_FRAME_DIMENSION = 2048;
    if (width > MAX_FRAME_DIMENSION || height > MAX_FRAME_DIMENSION) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE,
            "Frame dimensions exceed maximum (2048x2048)");
    }

    size_t required_size = 0;
    SAFE_MULTIPLY_OR_ERROR(static_cast<size_t>(width) * height, 3, required_size);
    *size_out = required_size;

    if (width_out != nullptr) { *width_out = width; }
    if (height_out != nullptr) { *height_out = height; }

    if (buffer == nullptr) {
        return LEGENDS_OK;
    }

    if (buffer_size < required_size) {
        return LEGENDS_ERR_BUFFER_TOO_SMALL;
    }

    if (inst->frame_state.is_text_mode) {
        const auto& palette = inst->frame_state.palette;
        const auto& font = inst->frame_state.font_data;
        const uint8_t ch_h = inst->frame_state.char_height;

        for (uint16_t row = 0; row < inst->frame_state.rows; ++row) {
            for (uint16_t col = 0; col < inst->frame_state.columns; ++col) {
                size_t cell_idx = row * inst->frame_state.columns + col;
                uint16_t cell = inst->frame_state.text_buffer[cell_idx];
                uint8_t ch = static_cast<uint8_t>(cell & 0xFF);
                uint8_t attr = static_cast<uint8_t>((cell >> 8) & 0xFF);

                uint8_t fg_idx = attr & 0x0F;
                uint8_t bg_idx = (attr >> 4) & 0x07;

                legends::vision::RgbColor fg_color = palette[fg_idx];
                legends::vision::RgbColor bg_color = palette[bg_idx];

                for (int py = 0; py < ch_h; ++py) {
                    // Look up glyph row from font bitmap
                    uint8_t glyph_row = 0;
                    size_t font_offset = static_cast<size_t>(ch) * ch_h + py;
                    if (!font.empty() && font_offset < font.size()) {
                        glyph_row = font[font_offset];
                    } else if (ch != ' ' && ch != 0) {
                        // Fallback: solid block when font data not yet available
                        glyph_row = 0xFF;
                    }

                    for (int px = 0; px < 8; ++px) {
                        size_t pixel_x = col * 8 + px;
                        size_t pixel_y = row * ch_h + py;
                        size_t pixel_idx = (pixel_y * width + pixel_x) * 3;

                        // 1bpp bitmap: MSB is leftmost pixel
                        bool is_fg = (glyph_row >> (7 - px)) & 1;
                        const auto& color = is_fg ? fg_color : bg_color;

                        buffer[pixel_idx + 0] = color.r;
                        buffer[pixel_idx + 1] = color.g;
                        buffer[pixel_idx + 2] = color.b;
                    }
                }
            }
        }

        // Cursor rendering (Phase -1, REQ-PLUMB-002)
        if (inst->frame_state.cursor_visible &&
            inst->frame_state.cursor_x < inst->frame_state.columns &&
            inst->frame_state.cursor_y < inst->frame_state.rows) {

            uint8_t cx = inst->frame_state.cursor_x;
            uint8_t cy = inst->frame_state.cursor_y;
            uint8_t cstart = inst->frame_state.cursor_start & 0x1F;
            uint8_t cend = inst->frame_state.cursor_end;

            // Get foreground color from the character attribute at cursor position
            size_t cursor_cell = cy * inst->frame_state.columns + cx;
            uint8_t cursor_attr = static_cast<uint8_t>(
                (inst->frame_state.text_buffer[cursor_cell] >> 8) & 0xFF);
            uint8_t cursor_fg_idx = cursor_attr & 0x0F;
            legends::vision::RgbColor cursor_color = inst->frame_state.palette[cursor_fg_idx];

            // Draw cursor block from start to end scanlines
            for (int py = cstart; py <= cend && py < ch_h; ++py) {
                for (int px = 0; px < 8; ++px) {
                    size_t pixel_x = cx * 8 + px;
                    size_t pixel_y = cy * ch_h + py;
                    size_t pixel_idx = (pixel_y * width + pixel_x) * 3;

                    buffer[pixel_idx + 0] = cursor_color.r;
                    buffer[pixel_idx + 1] = cursor_color.g;
                    buffer[pixel_idx + 2] = cursor_color.b;
                }
            }
        }
    } else {
        size_t pixel_count = static_cast<size_t>(width) * height;

        if (inst->frame_state.indexed_pixels.size() < pixel_count) {
            std::memset(buffer, 0, required_size);
        } else {
            const auto& palette = inst->frame_state.palette;
            for (size_t i = 0; i < pixel_count; ++i) {
                uint8_t idx = inst->frame_state.indexed_pixels[i];
                legends::vision::RgbColor color = palette[idx];
                buffer[i * 3 + 0] = color.r;
                buffer[i * 3 + 1] = color.g;
                buffer[i * 3 + 2] = color.b;
            }
        }
    }

    inst->frame_state.dirty = false;

    return LEGENDS_OK;
}

legends_error_t legends_is_frame_dirty(
    legends_handle handle,
    int* dirty_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(dirty_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    *dirty_out = inst->frame_state.dirty ? 1 : 0;
    return LEGENDS_OK;
}

legends_error_t legends_get_cursor(
    legends_handle handle,
    uint8_t* x_out,
    uint8_t* y_out,
    int* visible_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();

    if (x_out != nullptr) { *x_out = inst->frame_state.cursor_x; }
    if (y_out != nullptr) { *y_out = inst->frame_state.cursor_y; }
    if (visible_out != nullptr) { *visible_out = inst->frame_state.cursor_visible ? 1 : 0; }

    return LEGENDS_OK;
}

/* =========================================================================
 * AUDIO CAPTURE API - Phase -1 Implementation
 * ========================================================================= */

legends_error_t legends_capture_audio(
    legends_handle handle,
    int16_t* buffer,
    size_t buffer_count,
    size_t* count_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(count_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    if (!inst->engine_handle) {
        *count_out = 0;
        return LEGENDS_OK;
    }

    return dosbox_to_legends_error(
        dosbox_lib_get_audio_samples(inst->engine_handle, buffer, buffer_count, count_out));
}

legends_error_t legends_is_audio_active(
    legends_handle handle,
    int* active_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(active_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    // Audio is active if the engine was created with audio enabled
    // Check by querying if there's audio infrastructure available
    if (!inst->engine_handle) {
        *active_out = 0;
        return LEGENDS_OK;
    }

    // Try to query sample count — if the engine supports it, audio is active
    size_t available = 0;
    auto err = dosbox_lib_get_audio_samples(inst->engine_handle, nullptr, 0, &available);
    // Audio is active if the call succeeds (even if no samples yet)
    *active_out = (err == DOSBOX_LIB_OK) ? 1 : 0;
    return LEGENDS_OK;
}

/* =========================================================================
 * INPUT INJECTION API - Phase 4 Implementation
 * ========================================================================= */

legends_error_t legends_key_event(
    legends_handle handle,
    uint8_t scancode,
    int is_down
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    if (inst->in_step) { return LEGENDS_ERR_REENTRANT_CALL; }

    if (!inst->input_state.enqueue_key(scancode, is_down != 0, false)) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
    }

    inst->frame_state.dirty = true;
    return LEGENDS_OK;
}

legends_error_t legends_key_event_ext(
    legends_handle handle,
    uint8_t scancode,
    int is_down
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    if (inst->in_step) { return LEGENDS_ERR_REENTRANT_CALL; }

    if (!inst->input_state.enqueue_key(scancode, is_down != 0, true)) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
    }

    inst->frame_state.dirty = true;
    return LEGENDS_OK;
}

legends_error_t legends_text_input(
    legends_handle handle,
    const char* utf8_text
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    if (inst->in_step) { return LEGENDS_ERR_REENTRANT_CALL; }
    LEGENDS_REQUIRE(utf8_text != nullptr, LEGENDS_ERR_NULL_POINTER);

    const char* p = utf8_text;
    while (*p != '\0') {
        unsigned char ch = static_cast<unsigned char>(*p);

        if (ch < 128) {
            const ScancodeMapping& mapping = ASCII_TO_SCANCODE[ch];

            if (mapping.scancode != 0) {
                size_t slots_needed = mapping.needs_shift ? 4 : 2;
                size_t available = InputState::EFFECTIVE_CAPACITY - inst->input_state.size();
                if (available < slots_needed) {
                    LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                }

                if (mapping.needs_shift) {
                    inst->input_state.enqueue_key(SCANCODE_LSHIFT, true, false);
                }
                inst->input_state.enqueue_key(mapping.scancode, true, false);
                inst->input_state.enqueue_key(mapping.scancode, false, false);
                if (mapping.needs_shift) {
                    inst->input_state.enqueue_key(SCANCODE_LSHIFT, false, false);
                }
            }
            ++p;
        } else {
            int seq_len = 1;
            if ((ch & 0xE0) == 0xC0) seq_len = 2;
            else if ((ch & 0xF0) == 0xE0) seq_len = 3;
            else if ((ch & 0xF8) == 0xF0) seq_len = 4;

            // Validate continuation bytes exist before advancing
            bool valid = true;
            for (int i = 1; i < seq_len; ++i) {
                if (p[i] == '\0') { valid = false; break; }
            }
            p += valid ? seq_len : 1;
        }
    }

    inst->frame_state.dirty = true;
    return LEGENDS_OK;
}

legends_error_t legends_mouse_event(
    legends_handle handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    if (inst->in_step) { return LEGENDS_ERR_REENTRANT_CALL; }

    if (!inst->input_state.enqueue_mouse(delta_x, delta_y, buttons)) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Mouse event queue full");
    }

    inst->frame_state.dirty = true;
    return LEGENDS_OK;
}

/* =========================================================================
 * STATE SYNCHRONIZATION - Phase 3 Implementation
 *
 * These functions synchronize state between the legends layer and the
 * DOSBox engine layer. This ensures the two layers remain consistent
 * after operations like stepping or loading state.
 * ========================================================================= */

/**
 * @brief Sync legends layer state from engine.
 *
 * Called after:
 * - stepping cycles (engine has updated timing)
 * - loading state (engine state was restored)
 *
 * Updates legends layer timing state to match engine.
 */
void sync_state_from_engine(legends_instance* inst) {
    if (!inst || !inst->engine_handle) {
        return;
    }

    dosbox_lib_get_total_cycles(inst->engine_handle, &inst->time_state.total_cycles);
    dosbox_lib_get_emu_time(inst->engine_handle, &inst->time_state.emu_time_us);

    dosbox_lib_pic_state_t pic_state;
    if (dosbox_lib_get_pic_state(inst->engine_handle, &pic_state) == DOSBOX_LIB_OK) {
        inst->pics[0].irr = pic_state.master_irr;
        inst->pics[0].imr = pic_state.master_imr;
        inst->pics[0].isr = pic_state.master_isr;
        inst->pics[1].irr = pic_state.slave_irr;
        inst->pics[1].imr = pic_state.slave_imr;
        inst->pics[1].isr = pic_state.slave_isr;
    }

    // Sync display mode from engine (H8)
    dosbox_lib_display_info_t display;
    if (dosbox_lib_get_display_info(inst->engine_handle, &display) == DOSBOX_LIB_OK) {
        inst->frame_state.is_text_mode = (display.is_text_mode != 0);
        inst->frame_state.columns = display.text_columns;
        inst->frame_state.rows = display.text_rows;
        inst->frame_state.gfx_width = display.width;
        inst->frame_state.gfx_height = display.height;
        inst->frame_state.dirty = true;
    }

    // Palette sync (Phase -1)
    uint8_t palette_rgb[768];
    if (dosbox_lib_get_palette(inst->engine_handle, palette_rgb) == DOSBOX_LIB_OK) {
        for (int i = 0; i < 256; ++i) {
            inst->frame_state.palette.set(i, legends::vision::RgbColor{
                palette_rgb[i * 3],
                palette_rgb[i * 3 + 1],
                palette_rgb[i * 3 + 2]
            });
        }
    }

    // Framebuffer data sync (Phase -1)
    // Only overwrite legends-layer state when the engine provides valid data.
    // In headless mode, VGA functions return NOT_SUPPORTED, and the engine
    // text memory at 0xB8000 may be all zeros (no BIOS booted yet).
    // In those cases, keep the current frame_state (test pattern + embedded font).
    if (inst->frame_state.is_text_mode) {
        // Text buffer — only overwrite if engine has non-zero content
        size_t count = 0;
        if (dosbox_lib_get_text_buffer(inst->engine_handle, nullptr, 0, &count) == DOSBOX_LIB_OK
            && count > 0 && count <= FrameState::MAX_TEXT_CELLS) {
            std::array<uint16_t, FrameState::MAX_TEXT_CELLS> temp{};
            if (dosbox_lib_get_text_buffer(inst->engine_handle,
                    temp.data(), count, &count) == DOSBOX_LIB_OK) {
                // Check if engine text buffer has any non-zero content
                bool has_content = false;
                for (size_t i = 0; i < count; ++i) {
                    if (temp[i] != 0) { has_content = true; break; }
                }
                if (has_content) {
                    std::copy(temp.begin(), temp.begin() + count,
                              inst->frame_state.text_buffer.begin());
                }
            }
        }
        // Font data — only overwrite if engine returns valid font (not NOT_SUPPORTED)
        size_t font_size = 0;
        uint8_t ch_height = 0;
        auto font_err = dosbox_lib_get_font_data(
            inst->engine_handle, nullptr, 0, &font_size, &ch_height);
        if (font_err == DOSBOX_LIB_OK && font_size > 0) {
            inst->frame_state.font_data.resize(font_size);
            inst->frame_state.char_height = ch_height;
            dosbox_lib_get_font_data(inst->engine_handle,
                inst->frame_state.font_data.data(), font_size, &font_size, &ch_height);
        }
    } else {
        // Indexed pixels for graphics modes — only if supported
        size_t px_count = 0;
        auto px_err = dosbox_lib_get_indexed_pixels(
            inst->engine_handle, nullptr, 0, &px_count);
        if (px_err == DOSBOX_LIB_OK && px_count > 0) {
            inst->frame_state.indexed_pixels.resize(px_count);
            dosbox_lib_get_indexed_pixels(inst->engine_handle,
                inst->frame_state.indexed_pixels.data(), px_count, &px_count);
        }
    }

    // Cursor sync (Phase -1, REQ-PLUMB-002)
    // Only overwrite cursor state if the BDA appears initialized (non-zero cursor shape).
    // When engine memory is uninitialized, BDA is all zeros which gives start=0, end=0.
    dosbox_lib_cursor_info_t cursor;
    if (dosbox_lib_get_cursor_info(inst->engine_handle, &cursor) == DOSBOX_LIB_OK) {
        // A cursor_end of 0 with cursor_start of 0 usually means BDA is uninitialized
        bool bda_initialized = (cursor.end_line > 0 || cursor.start_line > 0
                                || cursor.col > 0 || cursor.row > 0);
        if (bda_initialized) {
            inst->frame_state.cursor_x = cursor.col;
            inst->frame_state.cursor_y = cursor.row;
            inst->frame_state.cursor_visible = (cursor.visible != 0);
            inst->frame_state.cursor_start = cursor.start_line;
            inst->frame_state.cursor_end = cursor.end_line;
            inst->frame_state.active_page = cursor.active_page;
        }
    }
}

/**
 * @brief Drain input queue to engine.
 *
 * Called before stepping to forward all queued input events to the engine.
 * This ensures input is processed in the correct interleaved order for determinism.
 *
 * @return LEGENDS_OK on success, error if injection failed
 */
legends_error_t drain_input_to_engine(legends_instance* inst, uint32_t* count_out) {
    if (count_out != nullptr) {
        *count_out = 0;
    }
    if (!inst || !inst->engine_handle) return LEGENDS_OK;
    uint32_t count = 0;

    InputEvent evt;
    while (inst->input_state.peek(&evt)) {
        dosbox_lib_error_t err = DOSBOX_LIB_OK;
        switch (evt.type) {
            case InputEventType::Key:
                err = dosbox_lib_inject_key(inst->engine_handle,
                    evt.key.scancode,
                    evt.key.is_down ? 1 : 0,
                    evt.key.is_extended ? 1 : 0);
                break;
            case InputEventType::Mouse:
                err = dosbox_lib_inject_mouse(inst->engine_handle,
                    evt.mouse.delta_x,
                    evt.mouse.delta_y,
                    evt.mouse.buttons);
                break;
        }

        if (err != DOSBOX_LIB_OK) {
            if (count_out != nullptr) {
                *count_out = count;
            }
            return dosbox_to_legends_error(err);
        }

        inst->input_state.pop();
        ++count;
    }

    if (count_out != nullptr) {
        *count_out = count;
    }
    return LEGENDS_OK;
}

/**
 * @brief Push legends layer state to engine.
 *
 * Called when legends layer state is modified directly and
 * engine needs to be updated to match.
 *
 * Note: Currently timing is engine-authoritative (engine is source of truth
 * after stepping). This function is for cases where legends layer needs to
 * push state to the engine (e.g., external state injection).
 */
void sync_state_to_engine(legends_instance* inst) {
    if (!inst || !inst->engine_handle) {
        return;
    }

    // Currently, timing flows engine -> legends, not the reverse.
    // Input is forwarded via drain_input_to_engine() before stepping.
    // This function is a placeholder for future state push needs.
}

/* =========================================================================
 * SAVE/LOAD API - Phase 5 Implementation
 *
 * Per TLA+ SaveState.tla specification:
 * - Event queue MUST be serialized for deterministic replay
 * - Obs(Deserialize(Serialize(S))) = Obs(S) must hold
 * - State includes: now, Q (events), CPU, PICs, DMA
 * ========================================================================= */

// Helper: Get engine state size
size_t get_engine_state_size(legends_instance* inst) {
    if (!inst || !inst->engine_handle) {
        return 0;
    }
    size_t engine_size = 0;
    dosbox_lib_save_state(inst->engine_handle, nullptr, 0, &engine_size);
    return engine_size;
}

// Helper: Calculate total save state size
size_t calculate_save_state_size(legends_instance* inst) {
    size_t size = sizeof(SaveStateHeader);
    size += sizeof(SaveStateTime);
    size += sizeof(SaveStateCPU);
    size += sizeof(SaveStatePIC);
    size += 8 * WIRE_DMA_CHANNEL_SIZE;

    size += sizeof(SaveStateEventQueueHeader);
    size += inst->event_queue.event_count * sizeof(ScheduledEvent);

    size += sizeof(SaveStateInputHeader);
    size += inst->input_state.size() * WIRE_INPUT_EVENT_SIZE;

    size += sizeof(SaveStateFrameHeader);
    size += inst->frame_state.text_cell_count() * sizeof(uint16_t);
    size += inst->frame_state.indexed_pixels.size();

    size += get_engine_state_size(inst);

    return size;
}

legends_error_t legends_save_state(
    legends_handle handle,
    void* buffer,
    size_t buffer_size,
    size_t* size_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    if (inst->in_step) { return LEGENDS_ERR_REENTRANT_CALL; }
    LEGENDS_REQUIRE(size_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    // Calculate required size
    size_t required_size = calculate_save_state_size(inst);
    *size_out = required_size;

    // Two-call pattern: if buffer is NULL, just return size
    if (buffer == nullptr) {
        return LEGENDS_OK;
    }

    if (buffer_size < required_size) {
        return LEGENDS_ERR_BUFFER_TOO_SMALL;
    }

    uint8_t* ptr = static_cast<uint8_t*>(buffer);
    uint8_t* data_start = ptr + sizeof(SaveStateHeader);

    // Build header on stack to avoid unaligned access on caller buffer (H9)
    SaveStateHeader header{};
    header.magic = SAVESTATE_MAGIC;
    header.version = SAVESTATE_VERSION;
    header.total_size = static_cast<uint32_t>(required_size);
    std::memset(header._reserved, 0, sizeof(header._reserved));

    size_t offset = sizeof(SaveStateHeader);

    // Write time state
    header.time_offset = static_cast<uint32_t>(offset);
    SaveStateTime time_section{};
    time_section.total_cycles = inst->time_state.total_cycles;
    time_section.emu_time_us = inst->time_state.emu_time_us;
    time_section.cycles_per_ms = inst->time_state.cycles_per_ms;
    time_section._pad = 0;
    std::memcpy(ptr + offset, &time_section, sizeof(time_section));
    offset += sizeof(SaveStateTime);

    // Write CPU state
    header.cpu_offset = static_cast<uint32_t>(offset);
    SaveStateCPU cpu_section{};
    cpu_section.interrupt_flag = inst->machine ? (inst->machine->cpu.flags.interrupt ? 1 : 0) : 0;
    cpu_section.halted = inst->machine ? (inst->machine->cpu.halted ? 1 : 0) : 0;
    cpu_section.mode = 0;  // Real mode for now
    cpu_section._pad = 0;
    std::memset(cpu_section._reserved, 0, sizeof(cpu_section._reserved));
    std::memcpy(ptr + offset, &cpu_section, sizeof(cpu_section));
    offset += sizeof(SaveStateCPU);

    // Write PIC state (CRITICAL for TLA+ compliance)
    header.pic_offset = static_cast<uint32_t>(offset);
    SaveStatePIC pic_section{};
    pic_section.pics[0] = inst->pics[0];
    pic_section.pics[1] = inst->pics[1];
    std::memcpy(ptr + offset, &pic_section, sizeof(pic_section));
    offset += sizeof(SaveStatePIC);

    // Write DMA state (portable serialization)
    header.dma_offset = static_cast<uint32_t>(offset);
    for (int i = 0; i < 8; ++i) {
        serialize_dma_channel(ptr + offset, inst->dma[i]);
        offset += WIRE_DMA_CHANNEL_SIZE;
    }

    // Write event queue (CRITICAL for TLA+ compliance - event queue MUST be serialized)
    header.event_queue_offset = static_cast<uint32_t>(offset);
    SaveStateEventQueueHeader eq_header{};
    eq_header.event_count = static_cast<uint32_t>(inst->event_queue.event_count);
    eq_header.next_event_id = inst->event_queue.next_event_id;
    std::memcpy(ptr + offset, &eq_header, sizeof(eq_header));
    offset += sizeof(SaveStateEventQueueHeader);

    // Write events
    for (size_t i = 0; i < inst->event_queue.event_count; ++i) {
        std::memcpy(ptr + offset, &inst->event_queue.events[i], sizeof(ScheduledEvent));
        offset += sizeof(ScheduledEvent);
    }

    // Write input state (unified queue with portable serialization)
    header.input_offset = static_cast<uint32_t>(offset);
    SaveStateInputHeader input_hdr{};
    size_t input_count = inst->input_state.size();
    input_hdr.event_count = static_cast<uint32_t>(input_count);
    input_hdr.next_sequence_lo = static_cast<uint32_t>(inst->input_state.next_sequence & 0xFFFFFFFF);
    input_hdr.next_sequence_hi = static_cast<uint32_t>(inst->input_state.next_sequence >> 32);
    input_hdr._reserved = 0;
    std::memcpy(ptr + offset, &input_hdr, sizeof(input_hdr));
    offset += sizeof(SaveStateInputHeader);

    // Write unified input events with portable serialization
    for (size_t i = 0; i < input_count; ++i) {
        size_t idx = (inst->input_state.head + i) % InputState::MAX_INPUT_EVENTS;
        serialize_input_event(ptr + offset, inst->input_state.queue[idx]);
        offset += WIRE_INPUT_EVENT_SIZE;
    }

    // Write frame state
    header.frame_offset = static_cast<uint32_t>(offset);
    SaveStateFrameHeader frame_hdr{};
    frame_hdr.is_text_mode = inst->frame_state.is_text_mode ? 1 : 0;
    frame_hdr.columns = inst->frame_state.columns;
    frame_hdr.rows = inst->frame_state.rows;
    frame_hdr.cursor_x = inst->frame_state.cursor_x;
    frame_hdr.cursor_y = inst->frame_state.cursor_y;
    frame_hdr.cursor_visible = inst->frame_state.cursor_visible ? 1 : 0;
    frame_hdr.active_page = inst->frame_state.active_page;
    frame_hdr._pad = 0;
    frame_hdr.gfx_width = inst->frame_state.gfx_width;
    frame_hdr.gfx_height = inst->frame_state.gfx_height;
    size_t text_size = inst->frame_state.text_cell_count() * sizeof(uint16_t);
    size_t pixels_size = inst->frame_state.indexed_pixels.size();
    frame_hdr.text_buffer_size = static_cast<uint32_t>(text_size);
    frame_hdr.indexed_pixels_size = static_cast<uint32_t>(pixels_size);
    std::memcpy(ptr + offset, &frame_hdr, sizeof(frame_hdr));
    offset += sizeof(SaveStateFrameHeader);

    // Write text buffer
    std::memcpy(ptr + offset, inst->frame_state.text_buffer.data(), text_size);
    offset += text_size;

    // Write indexed pixels
    if (pixels_size > 0) {
        std::memcpy(ptr + offset, inst->frame_state.indexed_pixels.data(), pixels_size);
        offset += pixels_size;
    }

    // Write engine state (Phase 2 - full DOSBox context)
    size_t engine_size = get_engine_state_size(inst);
    if (engine_size > 0 && inst->engine_handle) {
        // Verify buffer capacity before engine write
        size_t remaining = buffer_size - offset;
        if (engine_size > remaining) {
            // Buffer too small - report required size in size_out
            *size_out = offset + engine_size;
            return LEGENDS_ERR_BUFFER_TOO_SMALL;
        }

        header.engine_offset = static_cast<uint32_t>(offset);

        size_t actual_engine_size = 0;
        auto engine_err = dosbox_lib_save_state(
            inst->engine_handle,
            ptr + offset,
            remaining,  // Pass actual remaining space, not queried size
            &actual_engine_size
        );

        // Map engine errors appropriately
        if (engine_err == DOSBOX_LIB_ERR_BUFFER_TOO_SMALL) {
            // Engine needs more space - report required size
            *size_out = offset + actual_engine_size;
            return LEGENDS_ERR_BUFFER_TOO_SMALL;
        }
        if (engine_err != DOSBOX_LIB_OK) {
            return dosbox_to_legends_error(engine_err);
        }

        // Verify engine didn't exceed allocated space
        if (actual_engine_size > remaining) {
            // Engine violated contract - this shouldn't happen
            return LEGENDS_ERR_INTERNAL;
        }

        // Use actual size written, not pre-computed size
        // This ensures header and checksum match actual data
        header.engine_size = static_cast<uint32_t>(actual_engine_size);
        offset += actual_engine_size;
    } else {
        header.engine_offset = 0;
        header.engine_size = 0;
    }

    // Calculate checksum based on actual written data (offset),
    // not pre-computed required_size, in case actual sizes differed
    const size_t actual_data_size = offset - sizeof(SaveStateHeader);
    header.total_size = static_cast<uint32_t>(offset);
    header.checksum = crc32(data_start, actual_data_size);

    // Write header to buffer (memcpy avoids unaligned access on caller buffer)
    std::memcpy(ptr, &header, sizeof(header));

    // Update size_out to actual written size
    *size_out = offset;

    return LEGENDS_OK;
}

// ─────────────────────────────────────────────────────────────────────────────
// V2 Legacy Loader (backward compatibility)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Load a V2 save state (separate keyboard/mouse queues, memcpy serialization).
 *
 * WARNING: V2 saves used raw memcpy and are NOT portable across platforms.
 * This loader only works if the save was created on the same platform/compiler.
 *
 * V2 saves are converted to V3's unified queue format during load.
 */
static legends_error_t load_state_v2_legacy(
    legends_instance* inst,
    const uint8_t* ptr,
    size_t buffer_size,
    const SaveStateHeader* header
) {
    // V2 validation - total_size must be at least header size to prevent underflow
    if (header->total_size < sizeof(SaveStateHeader)) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Declared size smaller than header");
    }

    size_t verified_size = header->total_size;
    if (verified_size > buffer_size) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "V2: Buffer smaller than declared size");
    }

    // Checksum validation
    const uint8_t* data_start = ptr + sizeof(SaveStateHeader);
    size_t data_size = verified_size - sizeof(SaveStateHeader);
    uint32_t computed_crc = crc32(data_start, data_size);
    if (computed_crc != header->checksum) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Checksum mismatch");
    }

    // Validate section offsets (same as V3 for common sections)
    VALIDATE_SECTION_BOUNDS(header->time_offset, SaveStateTime, verified_size);
    VALIDATE_SECTION_BOUNDS(header->cpu_offset, SaveStateCPU, verified_size);
    VALIDATE_SECTION_BOUNDS(header->pic_offset, SaveStatePIC, verified_size);
    VALIDATE_SECTION_BOUNDS(header->input_offset, SaveStateInputHeader_V2, verified_size);
    VALIDATE_SECTION_BOUNDS(header->frame_offset, SaveStateFrameHeader, verified_size);
    // V2 DMA uses raw memcpy - validate bounds before access
    VALIDATE_DATA_BOUNDS(header->dma_offset, 8 * sizeof(DMAChannelState), verified_size);
    // V2 event queue offset validation
    VALIDATE_SECTION_BOUNDS(header->event_queue_offset, SaveStateEventQueueHeader, verified_size);

    // ─────────────────────────────────────────────────────────────────────────
    // V2 Phase 1: Validate ALL section data (no global mutations)
    // ─────────────────────────────────────────────────────────────────────────

    // memcpy to aligned locals to avoid UB on caller buffer (H9)
    SaveStateTime time_v2_local;
    std::memcpy(&time_v2_local, ptr + header->time_offset, sizeof(time_v2_local));
    const SaveStateTime* time_section = &time_v2_local;

    SaveStateCPU cpu_v2_local;
    std::memcpy(&cpu_v2_local, ptr + header->cpu_offset, sizeof(cpu_v2_local));
    const SaveStateCPU* cpu_section = &cpu_v2_local;

    SaveStatePIC pic_v2_local;
    std::memcpy(&pic_v2_local, ptr + header->pic_offset, sizeof(pic_v2_local));
    const SaveStatePIC* pic_section = &pic_v2_local;

    // Validate event queue
    SaveStateEventQueueHeader eq_v2_local;
    std::memcpy(&eq_v2_local, ptr + header->event_queue_offset, sizeof(eq_v2_local));
    const SaveStateEventQueueHeader* eq_header = &eq_v2_local;
    VALIDATE_COUNT_MAX(eq_header->event_count, EventQueueState::MAX_EVENTS, "V2: event_count");
    size_t v2_events_data_size = static_cast<size_t>(eq_header->event_count) * sizeof(ScheduledEvent);
    size_t eq_data_offset = header->event_queue_offset + sizeof(SaveStateEventQueueHeader);
    VALIDATE_DATA_BOUNDS(eq_data_offset, v2_events_data_size, verified_size);

    // Validate V2 input
    SaveStateInputHeader_V2 input_v2_local;
    std::memcpy(&input_v2_local, ptr + header->input_offset, sizeof(input_v2_local));
    const SaveStateInputHeader_V2* input_header_v2 = &input_v2_local;
    VALIDATE_COUNT_MAX(input_header_v2->key_queue_size, V2_MAX_KEY_EVENTS, "V2: key_queue_size");
    VALIDATE_COUNT_MAX(input_header_v2->mouse_queue_size, V2_MAX_MOUSE_EVENTS, "V2: mouse_queue_size");
    size_t total_events = input_header_v2->key_queue_size + input_header_v2->mouse_queue_size;
    if (total_events > InputState::EFFECTIVE_CAPACITY) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Too many events for unified queue");
    }
    size_t key_data_size = 0;
    SAFE_MULTIPLY_OR_ERROR(input_header_v2->key_queue_size, sizeof(KeyEvent_V2), key_data_size);
    size_t mouse_data_size = 0;
    SAFE_MULTIPLY_OR_ERROR(input_header_v2->mouse_queue_size, sizeof(MouseEvent_V2), mouse_data_size);
    size_t input_data_offset = header->input_offset + sizeof(SaveStateInputHeader_V2);
    VALIDATE_DATA_BOUNDS(input_data_offset, key_data_size, verified_size);
    VALIDATE_DATA_BOUNDS(input_data_offset + key_data_size, mouse_data_size, verified_size);

    // Validate frame header fields (matching V3 sanity checks)
    SaveStateFrameHeader frame_v2_local;
    std::memcpy(&frame_v2_local, ptr + header->frame_offset, sizeof(frame_v2_local));
    const SaveStateFrameHeader* frame_header = &frame_v2_local;
    if (frame_header->is_text_mode > 1) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: invalid bool value for is_text_mode");
    }
    constexpr uint8_t V2_MAX_COLUMNS = 80;
    constexpr uint8_t V2_MAX_ROWS = 50;
    if (frame_header->columns > V2_MAX_COLUMNS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Frame columns exceeds maximum (80)");
    }
    if (frame_header->rows > V2_MAX_ROWS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Frame rows exceeds maximum (50)");
    }
    const size_t v2_cell_count = static_cast<size_t>(frame_header->columns) * frame_header->rows;
    if (v2_cell_count > FrameState::MAX_TEXT_CELLS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Frame cell count exceeds maximum");
    }
    const size_t v2_pixel_size = static_cast<size_t>(frame_header->gfx_width) * frame_header->gfx_height;
    if (v2_pixel_size > MAX_INDEXED_PIXELS_SIZE) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Graphics dimensions exceed maximum");
    }
    size_t frame_data_offset = header->frame_offset + sizeof(SaveStateFrameHeader);
    size_t text_buffer_size = static_cast<size_t>(frame_header->columns) * frame_header->rows * sizeof(uint16_t);
    VALIDATE_DATA_BOUNDS(frame_data_offset, text_buffer_size, verified_size);
    size_t pixel_buffer_size = static_cast<size_t>(frame_header->gfx_width) * frame_header->gfx_height;
    if (pixel_buffer_size > 0) {
        VALIDATE_DATA_BOUNDS(frame_data_offset + text_buffer_size, pixel_buffer_size, verified_size);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // V2 Phase 2: Engine load (most likely failure point — F2 atomicity fix)
    // ─────────────────────────────────────────────────────────────────────────

    if (header->engine_size > 0 && inst->engine_handle) {
        VALIDATE_DATA_BOUNDS(header->engine_offset, header->engine_size, verified_size);
        auto engine_err = dosbox_lib_load_state(inst->engine_handle,
            ptr + header->engine_offset, header->engine_size);
        if (engine_err != DOSBOX_LIB_OK) {
            LEGENDS_ERROR(LEGENDS_ERR_INTERNAL, "V2: Engine state load failed");
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // V2 Phase 3: Stage validated data into locals (may allocate — can fail)
    // ─────────────────────────────────────────────────────────────────────────

    // Stage time
    TimeState staged_time{};
    staged_time.total_cycles = time_section->total_cycles;
    staged_time.emu_time_us = time_section->emu_time_us;
    staged_time.cycles_per_ms = time_section->cycles_per_ms;

    // Stage PIC
    PICState staged_pics[2];
    for (int i = 0; i < 2; ++i) {
        staged_pics[i].irr = pic_section->pics[i].irr;
        staged_pics[i].imr = pic_section->pics[i].imr;
        staged_pics[i].isr = pic_section->pics[i].isr;
        staged_pics[i].vector_base = pic_section->pics[i].vector_base;
        staged_pics[i].cascade_irq = pic_section->pics[i].cascade_irq;
    }

    // Stage DMA
    DMAChannelState staged_dma[8];
    const uint8_t* dma_data = ptr + header->dma_offset;
    for (int i = 0; i < 8; ++i) {
        std::memcpy(&staged_dma[i], dma_data + i * sizeof(DMAChannelState), sizeof(DMAChannelState));
    }

    // Stage event queue
    EventQueueState staged_eq{};
    staged_eq.event_count = eq_header->event_count;
    staged_eq.next_event_id = eq_header->next_event_id;
    for (size_t i = 0; i < eq_header->event_count; ++i) {
        std::memcpy(&staged_eq.events[i], ptr + eq_data_offset + i * sizeof(ScheduledEvent),
                    sizeof(ScheduledEvent));
    }

    // Stage V2 input: convert to unified queue
    InputState staged_input{};
    size_t offset = input_data_offset;
    for (uint32_t i = 0; i < input_header_v2->key_queue_size; ++i) {
        KeyEvent_V2 ke_v2;
        std::memcpy(&ke_v2, ptr + offset, sizeof(KeyEvent_V2));
        offset += sizeof(KeyEvent_V2);
        staged_input.enqueue_key(ke_v2.scancode, ke_v2.is_down, ke_v2.is_extended);
    }
    for (uint32_t i = 0; i < input_header_v2->mouse_queue_size; ++i) {
        MouseEvent_V2 me_v2;
        std::memcpy(&me_v2, ptr + offset, sizeof(MouseEvent_V2));
        offset += sizeof(MouseEvent_V2);
        staged_input.enqueue_mouse(me_v2.delta_x, me_v2.delta_y, me_v2.buttons);
    }

    // Stage frame (allocations happen here — before any inst-> mutation)
    std::vector<uint8_t> staged_indexed_pixels;
    if (pixel_buffer_size > 0) {
        try {
            staged_indexed_pixels.resize(pixel_buffer_size);
        } catch (const std::bad_alloc&) {
            return LEGENDS_ERR_OUT_OF_MEMORY;
        }
        std::memcpy(staged_indexed_pixels.data(), ptr + frame_data_offset + text_buffer_size, pixel_buffer_size);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // V2 Phase 4: Commit — all writes, no failure possible
    // ─────────────────────────────────────────────────────────────────────────

    inst->time_state = staged_time;

    if (inst->machine) {
        inst->machine->cpu.flags.interrupt = (cpu_section->interrupt_flag != 0);
        inst->machine->cpu.halted = (cpu_section->halted != 0);
    }

    inst->pics[0] = staged_pics[0];
    inst->pics[1] = staged_pics[1];

    for (int i = 0; i < 8; ++i) {
        inst->dma[i] = staged_dma[i];
    }

    inst->event_queue = staged_eq;
    inst->input_state = std::move(staged_input);

    inst->frame_state.is_text_mode = frame_header->is_text_mode != 0;
    inst->frame_state.columns = frame_header->columns;
    inst->frame_state.rows = frame_header->rows;
    inst->frame_state.cursor_x = frame_header->cursor_x;
    inst->frame_state.cursor_y = frame_header->cursor_y;
    inst->frame_state.cursor_visible = frame_header->cursor_visible != 0;
    inst->frame_state.active_page = frame_header->active_page;
    inst->frame_state.gfx_width = frame_header->gfx_width;
    inst->frame_state.gfx_height = frame_header->gfx_height;

    if (text_buffer_size <= inst->frame_state.text_buffer.size() * sizeof(uint16_t)) {
        std::memcpy(inst->frame_state.text_buffer.data(), ptr + frame_data_offset, text_buffer_size);
    }
    inst->frame_state.indexed_pixels = std::move(staged_indexed_pixels);

    inst->last_error.clear();
    return LEGENDS_OK;
}

legends_error_t legends_load_state(
    legends_handle handle,
    const void* buffer,
    size_t buffer_size
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    if (inst->in_step) { return LEGENDS_ERR_REENTRANT_CALL; }
    LEGENDS_REQUIRE(buffer != nullptr, LEGENDS_ERR_NULL_POINTER);


    if (buffer_size < sizeof(SaveStateHeader)) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Buffer too small for header");
    }

    const uint8_t* ptr = static_cast<const uint8_t*>(buffer);

    // memcpy header to aligned local to avoid UB on caller buffer (H9)
    SaveStateHeader header_local;
    std::memcpy(&header_local, ptr, sizeof(header_local));
    const SaveStateHeader* header = &header_local;

    // Validate magic
    if (header->magic != SAVESTATE_MAGIC) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Invalid save state magic");
    }

    // Validate version - V3 is current, V2 is legacy (separate queues, non-portable)
    if (header->version == 2) {
        // V2 saves used separate keyboard/mouse queues and non-portable memcpy.
        // Load using legacy loader and convert to V3's unified queue format.
        return load_state_v2_legacy(inst, ptr, buffer_size, header);
    }
    if (header->version != SAVESTATE_VERSION) {
        LEGENDS_ERROR(LEGENDS_ERR_VERSION_MISMATCH,
            "Unknown save state version (expected V3)");
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Comprehensive bounds validation
    // ─────────────────────────────────────────────────────────────────────────

    // Validate size - total_size must be at least header size to prevent underflow
    if (header->total_size < sizeof(SaveStateHeader)) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Declared size smaller than header");
    }

    // Validate that declared size doesn't exceed buffer
    if (header->total_size > buffer_size) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Buffer smaller than declared state size");
    }

    // Validate checksum over the checksummed region
    const uint8_t* data_start = ptr + sizeof(SaveStateHeader);
    size_t data_size = header->total_size - sizeof(SaveStateHeader);
    uint32_t computed_crc = crc32(data_start, data_size);
    if (computed_crc != header->checksum) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Save state checksum mismatch");
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Validate ALL section offsets against TOTAL_SIZE (checksummed region)
    // This ensures all sections fall within the integrity-verified data
    // ─────────────────────────────────────────────────────────────────────────

    // Use total_size (not buffer_size) for section validation to ensure integrity
    const size_t verified_size = header->total_size;

    // Validate fixed-size section bounds against checksummed region
    VALIDATE_SECTION_BOUNDS(header->time_offset, SaveStateTime, verified_size);
    VALIDATE_SECTION_BOUNDS(header->cpu_offset, SaveStateCPU, verified_size);
    VALIDATE_SECTION_BOUNDS(header->pic_offset, SaveStatePIC, verified_size);
    // DMA uses wire format size, not struct size
    VALIDATE_DATA_BOUNDS(header->dma_offset, 8 * WIRE_DMA_CHANNEL_SIZE, verified_size);
    VALIDATE_SECTION_BOUNDS(header->event_queue_offset, SaveStateEventQueueHeader, verified_size);
    VALIDATE_SECTION_BOUNDS(header->input_offset, SaveStateInputHeader, verified_size);
    VALIDATE_SECTION_BOUNDS(header->frame_offset, SaveStateFrameHeader, verified_size);

    // ─────────────────────────────────────────────────────────────────────────
    // Phase 1: Validate ALL section data (no global mutations)
    // All reads below are from the save state buffer only.
    // ─────────────────────────────────────────────────────────────────────────

    // Read section headers via memcpy to avoid unaligned access (H9)
    SaveStateTime time_local;
    std::memcpy(&time_local, ptr + header->time_offset, sizeof(time_local));
    const SaveStateTime* time_section = &time_local;

    SaveStateCPU cpu_local;
    std::memcpy(&cpu_local, ptr + header->cpu_offset, sizeof(cpu_local));
    const SaveStateCPU* cpu_section = &cpu_local;

    SaveStatePIC pic_local;
    std::memcpy(&pic_local, ptr + header->pic_offset, sizeof(pic_local));
    const SaveStatePIC* pic_section = &pic_local;

    // Validate event queue
    SaveStateEventQueueHeader eq_local;
    std::memcpy(&eq_local, ptr + header->event_queue_offset, sizeof(eq_local));
    const SaveStateEventQueueHeader* eq_header = &eq_local;
    VALIDATE_COUNT_MAX(eq_header->event_count, EventQueueState::MAX_EVENTS, "event_count");
    size_t events_data_size = static_cast<size_t>(eq_header->event_count) * sizeof(ScheduledEvent);
    size_t eq_data_offset = header->event_queue_offset + sizeof(SaveStateEventQueueHeader);
    VALIDATE_DATA_BOUNDS(eq_data_offset, events_data_size, verified_size);

    // Validate input state
    SaveStateInputHeader input_local;
    std::memcpy(&input_local, ptr + header->input_offset, sizeof(input_local));
    const SaveStateInputHeader* input_header = &input_local;
    VALIDATE_COUNT_MAX(input_header->event_count, InputState::EFFECTIVE_CAPACITY, "input_event_count");
    size_t input_data_size = static_cast<size_t>(input_header->event_count) * WIRE_INPUT_EVENT_SIZE;
    size_t input_data_offset = header->input_offset + sizeof(SaveStateInputHeader);
    VALIDATE_DATA_BOUNDS(input_data_offset, input_data_size, verified_size);

    // Pre-validate input event types before any mutations
    {
        size_t pre_offset = input_data_offset;
        for (uint32_t i = 0; i < input_header->event_count; ++i) {
            InputEvent evt = deserialize_input_event(ptr + pre_offset);
            if (evt.type != InputEventType::Key && evt.type != InputEventType::Mouse) {
                LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Unknown input event type in save state");
            }
            pre_offset += WIRE_INPUT_EVENT_SIZE;
        }
    }

    // Validate frame state
    SaveStateFrameHeader frame_local;
    std::memcpy(&frame_local, ptr + header->frame_offset, sizeof(frame_local));
    const SaveStateFrameHeader* frame_header = &frame_local;
    constexpr size_t max_text_buffer_bytes = FrameState::MAX_TEXT_CELLS * sizeof(uint16_t);
    VALIDATE_COUNT_MAX(frame_header->text_buffer_size, max_text_buffer_bytes, "text_buffer_size");
    VALIDATE_COUNT_MAX(frame_header->indexed_pixels_size, MAX_INDEXED_PIXELS_SIZE, "indexed_pixels_size");
    size_t frame_data_offset = header->frame_offset + sizeof(SaveStateFrameHeader);
    VALIDATE_DATA_BOUNDS(frame_data_offset, frame_header->text_buffer_size, verified_size);
    VALIDATE_DATA_BOUNDS(frame_data_offset + frame_header->text_buffer_size,
                         frame_header->indexed_pixels_size, verified_size);
    constexpr uint8_t MAX_COLUMNS = 80;
    constexpr uint8_t MAX_ROWS = 50;
    if (frame_header->columns > MAX_COLUMNS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Frame columns exceeds maximum (80)");
    }
    if (frame_header->rows > MAX_ROWS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Frame rows exceeds maximum (50)");
    }
    const size_t cell_count = static_cast<size_t>(frame_header->columns) * frame_header->rows;
    if (cell_count > FrameState::MAX_TEXT_CELLS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Frame cell count exceeds maximum");
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Phase 2: Engine load (most likely external failure point)
    // Must succeed BEFORE mutating any legends-layer globals (F2 atomicity fix).
    // ─────────────────────────────────────────────────────────────────────────

    if (inst->engine_handle) {
        if (header->engine_offset == 0 || header->engine_size == 0) {
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE,
                "Save state missing engine data (required when engine is active)");
        }
        VALIDATE_DATA_BOUNDS(header->engine_offset, header->engine_size, verified_size);

        auto engine_err = dosbox_lib_load_state(
            inst->engine_handle,
            ptr + header->engine_offset,
            header->engine_size
        );
        if (engine_err != DOSBOX_LIB_OK) {
            return dosbox_to_legends_error(engine_err);
        }
        // Note: Do NOT call sync_state_from_engine() here.
        // After load, both legends layer and engine state were restored from save.
        // They are already synchronized. Calling sync would overwrite with stale values.
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Phase 3: Stage validated data into locals (may allocate — can fail)
    // ─────────────────────────────────────────────────────────────────────────

    // Stage time
    TimeState staged_time{};
    staged_time.total_cycles = time_section->total_cycles;
    staged_time.emu_time_us = time_section->emu_time_us;
    staged_time.cycles_per_ms = time_section->cycles_per_ms;

    // Stage PIC
    PICState staged_pics[2];
    staged_pics[0] = pic_section->pics[0];
    staged_pics[1] = pic_section->pics[1];

    // Stage DMA
    DMAChannelState staged_dma[8];
    size_t dma_offset = header->dma_offset;
    for (int i = 0; i < 8; ++i) {
        staged_dma[i] = deserialize_dma_channel(ptr + dma_offset);
        dma_offset += WIRE_DMA_CHANNEL_SIZE;
    }

    // Stage event queue
    EventQueueState staged_eq{};
    staged_eq.event_count = eq_header->event_count;
    staged_eq.next_event_id = eq_header->next_event_id;
    size_t eq_offset = eq_data_offset;
    for (size_t i = 0; i < staged_eq.event_count; ++i) {
        std::memcpy(&staged_eq.events[i], ptr + eq_offset, sizeof(ScheduledEvent));
        eq_offset += sizeof(ScheduledEvent);
    }

    // Stage input
    InputState staged_input{};
    staged_input.next_sequence = static_cast<uint64_t>(input_header->next_sequence_lo) |
                                 (static_cast<uint64_t>(input_header->next_sequence_hi) << 32);
    size_t input_offset = input_data_offset;
    for (uint32_t i = 0; i < input_header->event_count; ++i) {
        InputEvent evt = deserialize_input_event(ptr + input_offset);
        staged_input.enqueue_raw(evt);
        input_offset += WIRE_INPUT_EVENT_SIZE;
    }
    staged_input.next_sequence = static_cast<uint64_t>(input_header->next_sequence_lo) |
                                 (static_cast<uint64_t>(input_header->next_sequence_hi) << 32);

    // Stage frame (allocations happen here — before any inst-> mutation)
    std::vector<uint8_t> staged_indexed_pixels;
    size_t frame_offset = frame_data_offset;
    if (frame_header->indexed_pixels_size > 0) {
        try {
            staged_indexed_pixels.resize(frame_header->indexed_pixels_size);
        } catch (const std::bad_alloc&) {
            return LEGENDS_ERR_OUT_OF_MEMORY;
        }
        std::memcpy(staged_indexed_pixels.data(),
                    ptr + frame_offset + frame_header->text_buffer_size,
                    frame_header->indexed_pixels_size);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Phase 4: Commit — all writes, no failure possible
    // ─────────────────────────────────────────────────────────────────────────

    inst->time_state = staged_time;

    if (inst->machine) {
        inst->machine->cpu.flags.interrupt = (cpu_section->interrupt_flag != 0);
        inst->machine->cpu.halted = (cpu_section->halted != 0);
    }

    inst->pics[0] = staged_pics[0];
    inst->pics[1] = staged_pics[1];

    for (int i = 0; i < 8; ++i) {
        inst->dma[i] = staged_dma[i];
    }

    inst->event_queue = staged_eq;
    inst->input_state = std::move(staged_input);

    inst->frame_state.is_text_mode = (frame_header->is_text_mode != 0);
    inst->frame_state.columns = frame_header->columns;
    inst->frame_state.rows = frame_header->rows;
    inst->frame_state.cursor_x = frame_header->cursor_x;
    inst->frame_state.cursor_y = frame_header->cursor_y;
    inst->frame_state.cursor_visible = (frame_header->cursor_visible != 0);
    inst->frame_state.active_page = frame_header->active_page;
    inst->frame_state.gfx_width = frame_header->gfx_width;
    inst->frame_state.gfx_height = frame_header->gfx_height;
    std::memcpy(inst->frame_state.text_buffer.data(), ptr + frame_offset, frame_header->text_buffer_size);
    inst->frame_state.indexed_pixels = std::move(staged_indexed_pixels);
    inst->frame_state.dirty = true;

    return LEGENDS_OK;
}

legends_error_t legends_get_state_hash(
    legends_handle handle,
    uint8_t hash_out[32]
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(hash_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    // Sync state from engine first to ensure hash consistency
    sync_state_from_engine(inst);

    SHA256 sha;

    // Include engine's authoritative hash as primary source
    // This ensures the hash reflects actual engine state, not stale legends layer state
    if (inst->engine_handle) {
        uint8_t engine_hash[32];
        if (dosbox_lib_get_state_hash(inst->engine_handle, engine_hash) == DOSBOX_LIB_OK) {
            sha.update(engine_hash, 32);
        }
    }

    // Include legends-layer state that affects determinism
    // (pending input queue events will affect future state)
    uint64_t input_queue_size = inst->input_state.size();
    sha.update(&input_queue_size, sizeof(input_queue_size));

    // If there are pending input events, hash their sequence numbers
    // to catch ordering differences
    if (input_queue_size > 0) {
        sha.update(&inst->input_state.next_sequence, sizeof(inst->input_state.next_sequence));
        size_t idx = inst->input_state.head;
        for (size_t i = 0; i < input_queue_size; ++i) {
            const auto& evt = inst->input_state.queue[idx];
            const uint8_t type = static_cast<uint8_t>(evt.type);
            sha.update(&type, sizeof(type));
            sha.update(&evt.sequence, sizeof(evt.sequence));
            if (evt.type == InputEventType::Key) {
                sha.update(&evt.key.scancode, sizeof(evt.key.scancode));
                const uint8_t down = evt.key.is_down ? 1 : 0;
                const uint8_t ext = evt.key.is_extended ? 1 : 0;
                sha.update(&down, sizeof(down));
                sha.update(&ext, sizeof(ext));
            } else {
                sha.update(&evt.mouse.delta_x, sizeof(evt.mouse.delta_x));
                sha.update(&evt.mouse.delta_y, sizeof(evt.mouse.delta_y));
                sha.update(&evt.mouse.buttons, sizeof(evt.mouse.buttons));
            }
            idx = (idx + 1) % InputState::MAX_INPUT_EVENTS;
        }
    }

    // Hash time (now) - these are synced from engine
    sha.update(&inst->time_state.total_cycles, sizeof(inst->time_state.total_cycles));
    sha.update(&inst->time_state.emu_time_us, sizeof(inst->time_state.emu_time_us));

    // Hash PIC state (synced from engine in sync_state_from_engine)
    sha.update(&inst->pics[0].irr, 1);
    sha.update(&inst->pics[0].imr, 1);
    sha.update(&inst->pics[0].isr, 1);
    sha.update(&inst->pics[1].irr, 1);
    sha.update(&inst->pics[1].imr, 1);
    sha.update(&inst->pics[1].isr, 1);

    // Include legends-layer event queue (scheduled events affect timing)
    sha.update(&inst->event_queue.event_count, sizeof(inst->event_queue.event_count));
    sha.update(&inst->event_queue.next_event_id, sizeof(inst->event_queue.next_event_id));
    for (size_t i = 0; i < inst->event_queue.event_count; ++i) {
        sha.update(&inst->event_queue.events[i].id, sizeof(inst->event_queue.events[i].id));
        sha.update(&inst->event_queue.events[i].deadline, sizeof(inst->event_queue.events[i].deadline));
    }

    sha.finalize(hash_out);
    return LEGENDS_OK;
}

legends_error_t legends_verify_determinism(
    legends_handle handle,
    uint64_t test_cycles,
    int* is_deterministic_out
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(is_deterministic_out != nullptr, LEGENDS_ERR_NULL_POINTER);


    // Per TLA+ specification:
    // Round-trip test: save -> step N cycles -> hash1; restore -> step N cycles -> hash2
    // Returns success if hash1 == hash2

    // Step 1: Save current state
    size_t state_size;
    legends_error_t err = legends_save_state(handle, nullptr, 0, &state_size);
    if (err != LEGENDS_OK) {
        return err;
    }

    std::vector<uint8_t> saved_state;
    try {
        saved_state.resize(state_size);
    } catch (const std::bad_alloc&) {
        return LEGENDS_ERR_OUT_OF_MEMORY;
    }
    err = legends_save_state(handle, saved_state.data(), saved_state.size(), &state_size);
    if (err != LEGENDS_OK) {
        return err;
    }

    // Step 2: Step N cycles and compute hash1
    err = legends_step_cycles(handle, test_cycles, nullptr);
    if (err != LEGENDS_OK) {
        return err;
    }

    uint8_t hash1[32];
    err = legends_get_state_hash(handle, hash1);
    if (err != LEGENDS_OK) {
        return err;
    }

    // Step 3: Restore saved state
    err = legends_load_state(handle, saved_state.data(), saved_state.size());
    if (err != LEGENDS_OK) {
        return err;
    }

    // Step 4: Step N cycles again and compute hash2
    err = legends_step_cycles(handle, test_cycles, nullptr);
    if (err != LEGENDS_OK) {
        return err;
    }

    uint8_t hash2[32];
    err = legends_get_state_hash(handle, hash2);
    if (err != LEGENDS_OK) {
        return err;
    }

    // Step 5: Compare hashes
    *is_deterministic_out = (std::memcmp(hash1, hash2, 32) == 0) ? 1 : 0;

    return LEGENDS_OK;
}

/* =========================================================================
 * INTROSPECTION & ERROR HANDLING
 * ========================================================================= */

legends_error_t legends_get_last_error(
    legends_handle handle,
    char* buffer,
    size_t buffer_size,
    size_t* length_out
) {
    LEGENDS_REQUIRE(length_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    // Can be called with NULL handle for pre-creation errors
    auto* inst = get_instance(handle);
    const std::string& error_str = inst ? inst->last_error : g_pre_creation_error;

    size_t required_len = error_str.size() + 1;  // Include null terminator
    *length_out = required_len;

    if (buffer == nullptr) {
        return LEGENDS_OK;
    }

    if (buffer_size < required_len) {
        return LEGENDS_ERR_BUFFER_TOO_SMALL;
    }

    std::memcpy(buffer, error_str.c_str(), required_len);
    return LEGENDS_OK;
}

legends_error_t legends_set_log_callback(
    legends_handle handle,
    legends_log_callback_t callback,
    void* userdata
) {
    auto* inst = get_instance(handle);
    LEGENDS_REQUIRE(inst != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();

    inst->log_state.callback = callback;
    inst->log_state.userdata = userdata;

    // Log that callback was set/cleared (only if setting, not clearing)
    if (callback != nullptr) {
        LEGENDS_LOG_DEBUG("Log callback registered");
    }

    return LEGENDS_OK;
}

} // extern "C"
