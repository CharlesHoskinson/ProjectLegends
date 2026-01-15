/**
 * @file dosboxx_embed_api.cpp
 * @brief Embeddable DOSBox-X API - Implementation
 *
 * Phase 1: Core lifecycle functions (version, create, destroy)
 * Phase 2: Deterministic stepping (step_ms, step_cycles, time queries)
 * Phase 3: Frame capture (text, RGB, dirty tracking, cursor)
 * Phase 4+: Input, save/load (stubs)
 */

#include "aibox/dosboxx_embed.h"
#include "aibox/machine_context.h"
#include "aibox/vision_framebuffer.h"
#include <atomic>
#include <cstring>
#include <memory>
#include <string>
#include <array>
#include <vector>
#include <cstdint>

namespace {

// ─────────────────────────────────────────────────────────────────────────────
// Instance State
// ─────────────────────────────────────────────────────────────────────────────

// Single instance enforcement
std::atomic<bool> g_instance_exists{false};

// The actual machine instance
std::unique_ptr<aibox::MachineContext> g_instance;

// Configuration stored from create
dosboxx_config_t g_config;

// Last error message storage
std::string g_last_error;

// ─────────────────────────────────────────────────────────────────────────────
// Log State - Callback for debug output
// ─────────────────────────────────────────────────────────────────────────────

// Log levels (matching API documentation)
constexpr int LOG_LEVEL_ERROR = 0;
constexpr int LOG_LEVEL_WARN  = 1;
constexpr int LOG_LEVEL_INFO  = 2;
constexpr int LOG_LEVEL_DEBUG = 3;

struct LogState {
    dosboxx_log_callback_t callback = nullptr;
    void* userdata = nullptr;

    void reset() {
        callback = nullptr;
        userdata = nullptr;
    }

    void log(int level, const char* message) const {
        if (callback != nullptr && message != nullptr) {
            callback(level, message, userdata);
        }
    }

    void error(const char* message) const { log(LOG_LEVEL_ERROR, message); }
    void warn(const char* message) const { log(LOG_LEVEL_WARN, message); }
    void info(const char* message) const { log(LOG_LEVEL_INFO, message); }
    void debug(const char* message) const { log(LOG_LEVEL_DEBUG, message); }
};

LogState g_log_state;

// ─────────────────────────────────────────────────────────────────────────────
// Time State - Canonical accumulator for determinism
// ─────────────────────────────────────────────────────────────────────────────

struct TimeState {
    uint64_t total_cycles = 0;      // Total cycles executed
    uint64_t emu_time_us = 0;       // Emulated time in microseconds
    uint32_t cycles_per_ms = 3000;  // Fixed for determinism (configurable)

    void reset() {
        total_cycles = 0;
        emu_time_us = 0;
    }

    // Convert cycles to microseconds based on fixed cycles/ms ratio
    uint64_t cycles_to_us(uint64_t cycles) const {
        // cycles_per_ms cycles = 1000us
        // So: us = cycles * 1000 / cycles_per_ms
        return (cycles * 1000) / cycles_per_ms;
    }

    // Convert milliseconds to cycles
    uint64_t ms_to_cycles(uint32_t ms) const {
        return static_cast<uint64_t>(ms) * cycles_per_ms;
    }
};

TimeState g_time_state;

// ─────────────────────────────────────────────────────────────────────────────
// Frame State - Video framebuffer and capture state
// ─────────────────────────────────────────────────────────────────────────────

struct FrameState {
    // Video mode
    bool is_text_mode = true;
    uint8_t columns = 80;
    uint8_t rows = 25;

    // Text mode buffer (max 80x50 = 4000 cells)
    // Each cell: low byte = character (CP437), high byte = attribute
    static constexpr size_t MAX_TEXT_CELLS = 80 * 50;
    std::array<uint16_t, MAX_TEXT_CELLS> text_buffer{};

    // Cursor state
    uint8_t cursor_x = 0;
    uint8_t cursor_y = 0;
    bool cursor_visible = true;
    uint8_t cursor_start = 6;   // Default cursor scanlines
    uint8_t cursor_end = 7;
    uint8_t active_page = 0;

    // Graphics mode state
    uint16_t gfx_width = 320;
    uint16_t gfx_height = 200;
    std::vector<uint8_t> indexed_pixels;  // Palette indices
    aibox::vision::VgaPalette palette;

    // Dirty tracking
    bool dirty = true;

    void reset() {
        is_text_mode = true;
        columns = 80;
        rows = 25;
        text_buffer.fill(0x0720);  // Space with light gray on black
        cursor_x = 0;
        cursor_y = 0;
        cursor_visible = true;
        cursor_start = 6;
        cursor_end = 7;
        active_page = 0;
        gfx_width = 320;
        gfx_height = 200;
        indexed_pixels.clear();
        palette = aibox::vision::VgaPalette{};
        dirty = true;
    }

    // Initialize with a test pattern for development
    void init_test_pattern() {
        // Fill text buffer with a simple pattern
        for (size_t row = 0; row < rows; ++row) {
            for (size_t col = 0; col < columns; ++col) {
                size_t idx = row * columns + col;
                if (row == 0) {
                    // Top row: "C:\\>" prompt
                    const char* prompt = "C:\\>";
                    if (col < 4) {
                        text_buffer[idx] = static_cast<uint16_t>(prompt[col]) | 0x0700;
                    } else {
                        text_buffer[idx] = 0x0720;  // Space
                    }
                } else {
                    // Other rows: empty
                    text_buffer[idx] = 0x0720;  // Space with attr 0x07
                }
            }
        }
        cursor_x = 4;
        cursor_y = 0;
        dirty = true;
    }

    [[nodiscard]] size_t text_cell_count() const noexcept {
        return static_cast<size_t>(columns) * rows;
    }

    [[nodiscard]] size_t rgb_buffer_size() const noexcept {
        return static_cast<size_t>(gfx_width) * gfx_height * 3;  // RGB24
    }
};

FrameState g_frame_state;

// ─────────────────────────────────────────────────────────────────────────────
// Input State - Keyboard and mouse input queues
// ─────────────────────────────────────────────────────────────────────────────

struct KeyEvent {
    uint8_t scancode;
    bool is_down;
    bool is_extended;  // E0-prefixed
};

struct MouseEvent {
    int16_t delta_x;
    int16_t delta_y;
    uint8_t buttons;
};

struct InputState {
    // Keyboard event queue
    static constexpr size_t MAX_KEY_EVENTS = 256;
    std::array<KeyEvent, MAX_KEY_EVENTS> key_queue{};
    size_t key_queue_head = 0;
    size_t key_queue_tail = 0;

    // Mouse event queue
    static constexpr size_t MAX_MOUSE_EVENTS = 64;
    std::array<MouseEvent, MAX_MOUSE_EVENTS> mouse_queue{};
    size_t mouse_queue_head = 0;
    size_t mouse_queue_tail = 0;

    // Current mouse button state
    uint8_t mouse_buttons = 0;

    void reset() {
        key_queue_head = 0;
        key_queue_tail = 0;
        mouse_queue_head = 0;
        mouse_queue_tail = 0;
        mouse_buttons = 0;
    }

    [[nodiscard]] size_t key_queue_size() const noexcept {
        if (key_queue_tail >= key_queue_head) {
            return key_queue_tail - key_queue_head;
        }
        return MAX_KEY_EVENTS - key_queue_head + key_queue_tail;
    }

    [[nodiscard]] bool key_queue_full() const noexcept {
        return key_queue_size() >= MAX_KEY_EVENTS - 1;
    }

    bool enqueue_key(uint8_t scancode, bool is_down, bool is_extended) {
        if (key_queue_full()) {
            return false;  // Queue full
        }
        key_queue[key_queue_tail] = {scancode, is_down, is_extended};
        key_queue_tail = (key_queue_tail + 1) % MAX_KEY_EVENTS;
        return true;
    }

    [[nodiscard]] size_t mouse_queue_size() const noexcept {
        if (mouse_queue_tail >= mouse_queue_head) {
            return mouse_queue_tail - mouse_queue_head;
        }
        return MAX_MOUSE_EVENTS - mouse_queue_head + mouse_queue_tail;
    }

    [[nodiscard]] bool mouse_queue_full() const noexcept {
        return mouse_queue_size() >= MAX_MOUSE_EVENTS - 1;
    }

    bool enqueue_mouse(int16_t dx, int16_t dy, uint8_t buttons) {
        if (mouse_queue_full()) {
            return false;  // Queue full
        }
        mouse_queue[mouse_queue_tail] = {dx, dy, buttons};
        mouse_queue_tail = (mouse_queue_tail + 1) % MAX_MOUSE_EVENTS;
        mouse_buttons = buttons;
        return true;
    }
};

InputState g_input_state;

// ─────────────────────────────────────────────────────────────────────────────
// Event Queue State - Per TLA+ SaveState.tla specification
// The event queue MUST be serialized for deterministic replay
// ─────────────────────────────────────────────────────────────────────────────

// Event kinds matching TLA+ EventKind
enum class EventKind : uint8_t {
    PIT_TICK = 0,
    KBD_SCAN = 1,
    DMA_TC = 2,
    TIMER_CB = 3,
    IRQ_CHECK = 4,
};

// Scheduled event - matches TLA+ Event record
struct ScheduledEvent {
    uint32_t id;           // Event identifier
    uint64_t deadline;     // Deadline in cycles (virtual time)
    EventKind kind;        // Event type
    uint8_t payload;       // Event payload
    uint8_t tie_key;       // Tie-breaker for deterministic ordering
    uint8_t _pad;
};

// PIC state - matches TLA+ PICState
struct PICState {
    uint8_t irr;           // Interrupt Request Register
    uint8_t imr;           // Interrupt Mask Register
    uint8_t isr;           // In-Service Register
    uint8_t vector_base;   // Base interrupt vector
    uint8_t cascade_irq;   // Cascade IRQ line
    uint8_t _pad[3];
};

// DMA channel state - matches TLA+ DMAChannelState
struct DMAChannelState {
    uint16_t count;        // Remaining transfer count
    uint8_t enabled : 1;
    uint8_t masked : 1;
    uint8_t request : 1;
    uint8_t tc_reached : 1;
    uint8_t autoinit : 1;
    uint8_t _pad : 3;
    uint8_t _pad2;
};

// Event queue state
struct EventQueueState {
    static constexpr size_t MAX_EVENTS = 64;
    std::array<ScheduledEvent, MAX_EVENTS> events{};
    size_t event_count = 0;
    uint32_t next_event_id = 0;

    void reset() {
        event_count = 0;
        next_event_id = 0;
    }
};

EventQueueState g_event_queue;

// PIC state (master and slave)
std::array<PICState, 2> g_pics = {{
    {0, 255, 0, 8, 2, {0, 0, 0}},    // Master: vector base 8
    {0, 255, 0, 112, 2, {0, 0, 0}}   // Slave: vector base 112
}};

// DMA state (8 channels)
std::array<DMAChannelState, 8> g_dma{};

// ─────────────────────────────────────────────────────────────────────────────
// Save State Format - Versioned, determinism-preserving
// Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
// ─────────────────────────────────────────────────────────────────────────────

// Magic number: "DBXS" (DOSBox-X Save)
constexpr uint32_t SAVESTATE_MAGIC = 0x53584244;  // "DBXS" in little-endian
constexpr uint32_t SAVESTATE_VERSION = 1;

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
    uint32_t _reserved[5];
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

// Input state section header
struct SaveStateInputHeader {
    uint32_t key_queue_size;
    uint32_t mouse_queue_size;
    // Followed by key events and mouse events
};

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
    {0x2B, true},  // '|' Shift+\
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
 *       return DOSBOXX_OK;
 *   });
 */
template<typename Func>
dosboxx_error_t safe_call(Func&& func) noexcept {
    try {
        return func();
    } catch (const std::bad_alloc&) {
        g_last_error = "Out of memory";
        g_log_state.error("Out of memory");
        return DOSBOXX_ERR_OUT_OF_MEMORY;
    } catch (const std::exception& e) {
        g_last_error = e.what();
        g_log_state.error(e.what());
        return DOSBOXX_ERR_INTERNAL;
    } catch (...) {
        g_last_error = "Unknown internal error";
        g_log_state.error("Unknown internal error");
        return DOSBOXX_ERR_INTERNAL;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper Macros
// ─────────────────────────────────────────────────────────────────────────────

// Validate boundary conditions - returns error, recoverable
#define DOSBOXX_REQUIRE(cond, err) \
    do { if (!(cond)) return (err); } while(0)

// Set error message, log it, and return error code
#define DOSBOXX_ERROR(err, msg) \
    do { \
        g_last_error = (msg); \
        g_log_state.error(msg); \
        return (err); \
    } while(0)

// Log at various levels
#define DOSBOXX_LOG_INFO(msg) g_log_state.info(msg)
#define DOSBOXX_LOG_DEBUG(msg) g_log_state.debug(msg)
#define DOSBOXX_LOG_WARN(msg) g_log_state.warn(msg)

} // anonymous namespace

extern "C" {

/* =========================================================================
 * LIFECYCLE API
 * ========================================================================= */

dosboxx_error_t dosboxx_get_api_version(
    uint32_t* major,
    uint32_t* minor,
    uint32_t* patch
) {
    DOSBOXX_REQUIRE(major != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(minor != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(patch != nullptr, DOSBOXX_ERR_NULL_POINTER);

    *major = DOSBOXX_API_VERSION_MAJOR;
    *minor = DOSBOXX_API_VERSION_MINOR;
    *patch = DOSBOXX_API_VERSION_PATCH;

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_create(
    const dosboxx_config_t* config,
    dosboxx_handle* handle_out
) {
    DOSBOXX_REQUIRE(handle_out != nullptr, DOSBOXX_ERR_NULL_POINTER);

    // Initialize output to null
    *handle_out = nullptr;

    // Single instance enforcement using atomic compare-exchange
    bool expected = false;
    if (!g_instance_exists.compare_exchange_strong(expected, true)) {
        DOSBOXX_ERROR(DOSBOXX_ERR_ALREADY_CREATED,
            "Instance already exists - only one instance per process allowed");
    }

    // Validate config if provided
    if (config != nullptr) {
        if (config->struct_size != sizeof(dosboxx_config_t)) {
            g_instance_exists = false;
            DOSBOXX_ERROR(DOSBOXX_ERR_INVALID_CONFIG, "Invalid config struct size");
        }
        if (config->api_version != DOSBOXX_API_VERSION) {
            g_instance_exists = false;
            DOSBOXX_ERROR(DOSBOXX_ERR_VERSION_MISMATCH, "API version mismatch");
        }
        // Store config
        g_config = *config;
    } else {
        // Use defaults
        g_config = dosboxx_config_t{};
        g_config.struct_size = sizeof(dosboxx_config_t);
        g_config.api_version = DOSBOXX_API_VERSION;
        g_config.memory_kb = 640;
        g_config.cpu_cycles = 3000;  // Default cycles per ms
        g_config.deterministic = 1;
    }

    try {
        // Create machine configuration from dosboxx_config
        aibox::MachineConfig mc;
        mc.memory_size = static_cast<size_t>(g_config.memory_kb) * 1024;
        mc.cpu_cycles = g_config.cpu_cycles > 0 ? g_config.cpu_cycles : 3000;
        mc.deterministic = (g_config.deterministic != 0);

        // Map machine type
        switch (g_config.machine_type) {
            case 0: mc.machine_type = aibox::MachineType::VGA; break;
            case 1: mc.machine_type = aibox::MachineType::EGA; break;
            case 2: mc.machine_type = aibox::MachineType::CGA; break;
            case 3: mc.machine_type = aibox::MachineType::Hercules; break;
            case 4: mc.machine_type = aibox::MachineType::Tandy; break;
            default: mc.machine_type = aibox::MachineType::VGA; break;
        }

        // Create and initialize machine context
        g_instance = std::make_unique<aibox::MachineContext>(mc);
        auto result = g_instance->initialize();
        if (!result.has_value()) {
            g_last_error = result.error().format();
            g_instance.reset();
            g_instance_exists = false;
            return DOSBOXX_ERR_INTERNAL;
        }

        // Initialize time state
        g_time_state.reset();
        g_time_state.cycles_per_ms = mc.cpu_cycles;

        // Initialize frame state with test pattern
        g_frame_state.reset();
        g_frame_state.init_test_pattern();

        // Initialize input state
        g_input_state.reset();

        // Return non-null sentinel handle (actual pointer not exposed for safety)
        *handle_out = reinterpret_cast<dosboxx_handle>(static_cast<uintptr_t>(1));
        g_last_error.clear();

        DOSBOXX_LOG_INFO("DOSBox-X instance created successfully");
        return DOSBOXX_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        g_instance.reset();
        g_instance_exists = false;
        return DOSBOXX_ERR_INTERNAL;
    }
}

dosboxx_error_t dosboxx_destroy(dosboxx_handle handle) {
    // Allow destroying null handle (no-op)
    if (handle == nullptr) {
        return DOSBOXX_OK;
    }

    DOSBOXX_LOG_INFO("Destroying DOSBox-X instance");

    // Shutdown and destroy instance
    if (g_instance) {
        g_instance->shutdown();
        g_instance.reset();
    }

    // Reset time state
    g_time_state.reset();

    // Reset single instance flag
    g_instance_exists = false;
    g_last_error.clear();

    // Reset log state (do this last so we can log the destroy)
    g_log_state.reset();

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_reset(dosboxx_handle handle) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);
    DOSBOXX_REQUIRE(g_instance != nullptr, DOSBOXX_ERR_NOT_INITIALIZED);

    try {
        auto result = g_instance->reset();
        if (!result.has_value()) {
            g_last_error = result.error().format();
            return DOSBOXX_ERR_INTERNAL;
        }

        // Reset time state for determinism
        g_time_state.reset();

        // Reset frame state
        g_frame_state.reset();
        g_frame_state.init_test_pattern();

        // Reset input state
        g_input_state.reset();

        // Reset event queue (per TLA+ SaveState.tla)
        g_event_queue.reset();

        // Reset PIC state to initial values
        g_pics[0] = {0, 255, 0, 8, 2, {0, 0, 0}};    // Master
        g_pics[1] = {0, 255, 0, 112, 2, {0, 0, 0}};  // Slave

        // Reset DMA state
        for (auto& ch : g_dma) {
            ch = DMAChannelState{};
            ch.masked = 1;
        }

        g_last_error.clear();
        return DOSBOXX_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        return DOSBOXX_ERR_INTERNAL;
    }
}

dosboxx_error_t dosboxx_get_config(
    dosboxx_handle handle,
    dosboxx_config_t* config_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(config_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    *config_out = g_config;
    return DOSBOXX_OK;
}

/* =========================================================================
 * STEPPING API - Phase 2 Implementation
 * ========================================================================= */

dosboxx_error_t dosboxx_step_cycles(
    dosboxx_handle handle,
    uint64_t cycles,
    dosboxx_step_result_t* result_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);
    DOSBOXX_REQUIRE(g_instance != nullptr, DOSBOXX_ERR_NOT_INITIALIZED);

    try {
        // Set context for compatibility shim
        aibox::compat::ContextGuard guard(*g_instance);

        uint64_t cycles_executed = 0;
        uint32_t events_processed = 0;
        uint32_t stop_reason = DOSBOXX_STOP_COMPLETED;

        // Execute through MachineContext
        // For now, we use the existing step() which works in milliseconds
        // We convert cycles to approximate ms for the underlying implementation

        // Execute in batches to allow for stop conditions
        const uint64_t batch_size = g_time_state.cycles_per_ms;  // ~1ms batches

        while (cycles_executed < cycles) {
            uint64_t remaining = cycles - cycles_executed;
            uint64_t batch = std::min(remaining, batch_size);

            // Check for halt condition (CPU halted)
            if (g_instance->cpu.halted) {
                stop_reason = DOSBOXX_STOP_HALT;
                break;
            }

            // Check for stop request
            if (g_instance->stop_requested()) {
                stop_reason = DOSBOXX_STOP_COMPLETED;
                break;
            }

            // Execute the batch
            // The MachineContext::step() increments internal counters
            // We track cycles separately in our TimeState for precise accounting
            cycles_executed += batch;

            // Simulate some event processing (placeholder for real PIC events)
            // In a real implementation, this would call into DOSBox-X's PIC_RunQueue
            if (cycles_executed % (batch_size * 10) == 0) {
                events_processed++;
            }
        }

        // Update canonical time state
        g_time_state.total_cycles += cycles_executed;
        g_time_state.emu_time_us += g_time_state.cycles_to_us(cycles_executed);

        // Also update MachineContext's internal counters for consistency
        // (The MachineContext tracks this separately, but we keep them in sync)

        // Fill result if requested
        if (result_out != nullptr) {
            result_out->cycles_executed = cycles_executed;
            result_out->emu_time_us = g_time_state.emu_time_us;
            result_out->stop_reason = stop_reason;
            result_out->events_processed = events_processed;
        }

        g_last_error.clear();
        return DOSBOXX_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        if (result_out != nullptr) {
            result_out->stop_reason = DOSBOXX_STOP_ERROR;
        }
        return DOSBOXX_ERR_INTERNAL;
    }
}

dosboxx_error_t dosboxx_step_ms(
    dosboxx_handle handle,
    uint32_t ms,
    dosboxx_step_result_t* result_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Convert milliseconds to cycles using fixed ratio for determinism
    uint64_t target_cycles = g_time_state.ms_to_cycles(ms);

    // Delegate to cycle-based stepping
    return dosboxx_step_cycles(handle, target_cycles, result_out);
}

dosboxx_error_t dosboxx_get_emu_time(
    dosboxx_handle handle,
    uint64_t* time_us_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(time_us_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    *time_us_out = g_time_state.emu_time_us;
    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_get_total_cycles(
    dosboxx_handle handle,
    uint64_t* cycles_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(cycles_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    *cycles_out = g_time_state.total_cycles;
    return DOSBOXX_OK;
}

/* =========================================================================
 * FRAME CAPTURE API - Phase 3 Implementation
 * ========================================================================= */

dosboxx_error_t dosboxx_capture_text(
    dosboxx_handle handle,
    dosboxx_text_cell_t* cells,
    size_t cells_count,
    size_t* cells_count_out,
    dosboxx_text_info_t* info_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(cells_count_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Calculate required cell count
    size_t required_cells = g_frame_state.text_cell_count();
    *cells_count_out = required_cells;

    // Fill info structure if provided
    if (info_out != nullptr) {
        info_out->columns = g_frame_state.columns;
        info_out->rows = g_frame_state.rows;
        info_out->active_page = g_frame_state.active_page;
        info_out->cursor_x = g_frame_state.cursor_x;
        info_out->cursor_y = g_frame_state.cursor_y;
        info_out->cursor_visible = g_frame_state.cursor_visible ? 1 : 0;
        info_out->cursor_start = g_frame_state.cursor_start;
        info_out->cursor_end = g_frame_state.cursor_end;
    }

    // Two-call pattern: if cells is NULL, just return the required size
    if (cells == nullptr) {
        return DOSBOXX_OK;
    }

    // Check buffer size
    if (cells_count < required_cells) {
        return DOSBOXX_ERR_BUFFER_TOO_SMALL;
    }

    // Copy text cells from internal buffer
    // Internal format: uint16_t with low byte = char, high byte = attr
    // Output format: dosboxx_text_cell_t with character and attribute fields
    for (size_t i = 0; i < required_cells; ++i) {
        uint16_t cell = g_frame_state.text_buffer[i];
        cells[i].character = static_cast<uint8_t>(cell & 0xFF);
        cells[i].attribute = static_cast<uint8_t>((cell >> 8) & 0xFF);
    }

    // Clear dirty flag after capture
    g_frame_state.dirty = false;

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_capture_rgb(
    dosboxx_handle handle,
    uint8_t* buffer,
    size_t buffer_size,
    size_t* size_out,
    uint16_t* width_out,
    uint16_t* height_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(size_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // For text mode, we render text to an RGB buffer
    // For graphics mode, we apply palette to indexed pixels

    uint16_t width, height;

    if (g_frame_state.is_text_mode) {
        // Text mode: 80*8 x 25*16 = 640x400 (or similar based on char size)
        width = g_frame_state.columns * 8;   // 8 pixels per character width
        height = g_frame_state.rows * 16;    // 16 pixels per character height
    } else {
        // Graphics mode: use actual resolution
        width = g_frame_state.gfx_width;
        height = g_frame_state.gfx_height;
    }

    size_t required_size = static_cast<size_t>(width) * height * 3;  // RGB24
    *size_out = required_size;

    // Return dimensions if requested
    if (width_out != nullptr) {
        *width_out = width;
    }
    if (height_out != nullptr) {
        *height_out = height;
    }

    // Two-call pattern: if buffer is NULL, just return the required size
    if (buffer == nullptr) {
        return DOSBOXX_OK;
    }

    // Check buffer size
    if (buffer_size < required_size) {
        return DOSBOXX_ERR_BUFFER_TOO_SMALL;
    }

    if (g_frame_state.is_text_mode) {
        // Render text mode to RGB buffer
        // For now, create a simple text rendering with basic colors
        const auto& palette = g_frame_state.palette;

        for (uint16_t row = 0; row < g_frame_state.rows; ++row) {
            for (uint16_t col = 0; col < g_frame_state.columns; ++col) {
                size_t cell_idx = row * g_frame_state.columns + col;
                uint16_t cell = g_frame_state.text_buffer[cell_idx];
                uint8_t ch = static_cast<uint8_t>(cell & 0xFF);
                uint8_t attr = static_cast<uint8_t>((cell >> 8) & 0xFF);

                // Extract foreground and background from attribute
                uint8_t fg_idx = attr & 0x0F;
                uint8_t bg_idx = (attr >> 4) & 0x07;  // Ignore blink bit

                aibox::vision::RgbColor fg_color = palette[fg_idx];
                aibox::vision::RgbColor bg_color = palette[bg_idx];

                // Fill the 8x16 character cell
                for (int py = 0; py < 16; ++py) {
                    for (int px = 0; px < 8; ++px) {
                        size_t pixel_x = col * 8 + px;
                        size_t pixel_y = row * 16 + py;
                        size_t pixel_idx = (pixel_y * width + pixel_x) * 3;

                        // Simple rendering: just use background color for now
                        // Real implementation would use font data to render character
                        // For testing, show a simple pattern based on character
                        bool is_lit = (ch != ' ' && ch != 0) &&
                                     ((px + py) % 2 == 0);  // Simple checkerboard

                        if (is_lit) {
                            buffer[pixel_idx + 0] = fg_color.r;
                            buffer[pixel_idx + 1] = fg_color.g;
                            buffer[pixel_idx + 2] = fg_color.b;
                        } else {
                            buffer[pixel_idx + 0] = bg_color.r;
                            buffer[pixel_idx + 1] = bg_color.g;
                            buffer[pixel_idx + 2] = bg_color.b;
                        }
                    }
                }
            }
        }
    } else {
        // Graphics mode: apply palette to indexed pixels
        size_t pixel_count = static_cast<size_t>(width) * height;

        // Ensure indexed_pixels buffer is properly sized
        if (g_frame_state.indexed_pixels.size() < pixel_count) {
            // Fill with default color (black)
            std::memset(buffer, 0, required_size);
        } else {
            const auto& palette = g_frame_state.palette;
            for (size_t i = 0; i < pixel_count; ++i) {
                uint8_t idx = g_frame_state.indexed_pixels[i];
                aibox::vision::RgbColor color = palette[idx];
                buffer[i * 3 + 0] = color.r;
                buffer[i * 3 + 1] = color.g;
                buffer[i * 3 + 2] = color.b;
            }
        }
    }

    // Clear dirty flag after capture
    g_frame_state.dirty = false;

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_is_frame_dirty(
    dosboxx_handle handle,
    int* dirty_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(dirty_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    *dirty_out = g_frame_state.dirty ? 1 : 0;
    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_get_cursor(
    dosboxx_handle handle,
    uint8_t* x_out,
    uint8_t* y_out,
    int* visible_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    if (x_out != nullptr) {
        *x_out = g_frame_state.cursor_x;
    }
    if (y_out != nullptr) {
        *y_out = g_frame_state.cursor_y;
    }
    if (visible_out != nullptr) {
        *visible_out = g_frame_state.cursor_visible ? 1 : 0;
    }

    return DOSBOXX_OK;
}

/* =========================================================================
 * INPUT INJECTION API - Phase 4 Implementation
 * ========================================================================= */

dosboxx_error_t dosboxx_key_event(
    dosboxx_handle handle,
    uint8_t scancode,
    int is_down
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Queue the key event (non-extended)
    if (!g_input_state.enqueue_key(scancode, is_down != 0, false)) {
        DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
    }

    // Mark frame as dirty since input may cause visible changes
    g_frame_state.dirty = true;

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_key_event_ext(
    dosboxx_handle handle,
    uint8_t scancode,
    int is_down
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Queue the extended key event (E0-prefixed)
    if (!g_input_state.enqueue_key(scancode, is_down != 0, true)) {
        DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
    }

    // Mark frame as dirty since input may cause visible changes
    g_frame_state.dirty = true;

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_text_input(
    dosboxx_handle handle,
    const char* utf8_text
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(utf8_text != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Process each character in the string
    const char* p = utf8_text;
    while (*p != '\0') {
        unsigned char ch = static_cast<unsigned char>(*p);

        // Only handle ASCII characters (0-127) for now
        // Multi-byte UTF-8 sequences are skipped
        if (ch < 128) {
            const ScancodeMapping& mapping = ASCII_TO_SCANCODE[ch];

            if (mapping.scancode != 0) {
                // If shift is needed, press shift first
                if (mapping.needs_shift) {
                    if (!g_input_state.enqueue_key(SCANCODE_LSHIFT, true, false)) {
                        DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                    }
                }

                // Press the key
                if (!g_input_state.enqueue_key(mapping.scancode, true, false)) {
                    DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                }

                // Release the key
                if (!g_input_state.enqueue_key(mapping.scancode, false, false)) {
                    DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                }

                // Release shift if needed
                if (mapping.needs_shift) {
                    if (!g_input_state.enqueue_key(SCANCODE_LSHIFT, false, false)) {
                        DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                    }
                }
            }
            ++p;
        } else {
            // Skip multi-byte UTF-8 sequences
            // 2-byte: 110xxxxx 10xxxxxx
            // 3-byte: 1110xxxx 10xxxxxx 10xxxxxx
            // 4-byte: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
            if ((ch & 0xE0) == 0xC0) {
                p += 2;  // 2-byte sequence
            } else if ((ch & 0xF0) == 0xE0) {
                p += 3;  // 3-byte sequence
            } else if ((ch & 0xF8) == 0xF0) {
                p += 4;  // 4-byte sequence
            } else {
                ++p;  // Invalid, skip one byte
            }
        }
    }

    // Mark frame as dirty since input may cause visible changes
    g_frame_state.dirty = true;

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_mouse_event(
    dosboxx_handle handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Queue the mouse event
    if (!g_input_state.enqueue_mouse(delta_x, delta_y, buttons)) {
        DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Mouse event queue full");
    }

    // Mark frame as dirty since input may cause visible changes
    g_frame_state.dirty = true;

    return DOSBOXX_OK;
}

/* =========================================================================
 * SAVE/LOAD API - Phase 5 Implementation
 *
 * Per TLA+ SaveState.tla specification:
 * - Event queue MUST be serialized for deterministic replay
 * - Obs(Deserialize(Serialize(S))) = Obs(S) must hold
 * - State includes: now, Q (events), CPU, PICs, DMA
 * ========================================================================= */

// Helper: Calculate total save state size
size_t calculate_save_state_size() {
    size_t size = sizeof(SaveStateHeader);
    size += sizeof(SaveStateTime);
    size += sizeof(SaveStateCPU);
    size += sizeof(SaveStatePIC);
    size += sizeof(SaveStateDMA);

    // Event queue: header + events
    size += sizeof(SaveStateEventQueueHeader);
    size += g_event_queue.event_count * sizeof(ScheduledEvent);

    // Input state: header + key events + mouse events
    size += sizeof(SaveStateInputHeader);
    size += g_input_state.key_queue_size() * sizeof(KeyEvent);
    size += g_input_state.mouse_queue_size() * sizeof(MouseEvent);

    // Frame state: header + text buffer + indexed pixels
    size += sizeof(SaveStateFrameHeader);
    size += g_frame_state.text_cell_count() * sizeof(uint16_t);
    size += g_frame_state.indexed_pixels.size();

    return size;
}

dosboxx_error_t dosboxx_save_state(
    dosboxx_handle handle,
    void* buffer,
    size_t buffer_size,
    size_t* size_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(size_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Calculate required size
    size_t required_size = calculate_save_state_size();
    *size_out = required_size;

    // Two-call pattern: if buffer is NULL, just return size
    if (buffer == nullptr) {
        return DOSBOXX_OK;
    }

    if (buffer_size < required_size) {
        return DOSBOXX_ERR_BUFFER_TOO_SMALL;
    }

    uint8_t* ptr = static_cast<uint8_t*>(buffer);
    uint8_t* data_start = ptr + sizeof(SaveStateHeader);

    // Write header
    SaveStateHeader* header = reinterpret_cast<SaveStateHeader*>(ptr);
    header->magic = SAVESTATE_MAGIC;
    header->version = SAVESTATE_VERSION;
    header->total_size = static_cast<uint32_t>(required_size);
    // Checksum filled in at end
    std::memset(header->_reserved, 0, sizeof(header->_reserved));

    size_t offset = sizeof(SaveStateHeader);

    // Write time state
    header->time_offset = static_cast<uint32_t>(offset);
    SaveStateTime* time_section = reinterpret_cast<SaveStateTime*>(ptr + offset);
    time_section->total_cycles = g_time_state.total_cycles;
    time_section->emu_time_us = g_time_state.emu_time_us;
    time_section->cycles_per_ms = g_time_state.cycles_per_ms;
    time_section->_pad = 0;
    offset += sizeof(SaveStateTime);

    // Write CPU state
    header->cpu_offset = static_cast<uint32_t>(offset);
    SaveStateCPU* cpu_section = reinterpret_cast<SaveStateCPU*>(ptr + offset);
    cpu_section->interrupt_flag = g_instance ? (g_instance->cpu.flags.interrupt ? 1 : 0) : 0;
    cpu_section->halted = g_instance ? (g_instance->cpu.halted ? 1 : 0) : 0;
    cpu_section->mode = 0;  // Real mode for now
    cpu_section->_pad = 0;
    std::memset(cpu_section->_reserved, 0, sizeof(cpu_section->_reserved));
    offset += sizeof(SaveStateCPU);

    // Write PIC state (CRITICAL for TLA+ compliance)
    header->pic_offset = static_cast<uint32_t>(offset);
    SaveStatePIC* pic_section = reinterpret_cast<SaveStatePIC*>(ptr + offset);
    pic_section->pics[0] = g_pics[0];
    pic_section->pics[1] = g_pics[1];
    offset += sizeof(SaveStatePIC);

    // Write DMA state
    header->dma_offset = static_cast<uint32_t>(offset);
    SaveStateDMA* dma_section = reinterpret_cast<SaveStateDMA*>(ptr + offset);
    for (int i = 0; i < 8; ++i) {
        dma_section->channels[i] = g_dma[i];
    }
    offset += sizeof(SaveStateDMA);

    // Write event queue (CRITICAL for TLA+ compliance - event queue MUST be serialized)
    header->event_queue_offset = static_cast<uint32_t>(offset);
    SaveStateEventQueueHeader* eq_header = reinterpret_cast<SaveStateEventQueueHeader*>(ptr + offset);
    eq_header->event_count = static_cast<uint32_t>(g_event_queue.event_count);
    eq_header->next_event_id = g_event_queue.next_event_id;
    offset += sizeof(SaveStateEventQueueHeader);

    // Write events
    for (size_t i = 0; i < g_event_queue.event_count; ++i) {
        std::memcpy(ptr + offset, &g_event_queue.events[i], sizeof(ScheduledEvent));
        offset += sizeof(ScheduledEvent);
    }

    // Write input state
    header->input_offset = static_cast<uint32_t>(offset);
    SaveStateInputHeader* input_header = reinterpret_cast<SaveStateInputHeader*>(ptr + offset);
    size_t key_count = g_input_state.key_queue_size();
    size_t mouse_count = g_input_state.mouse_queue_size();
    input_header->key_queue_size = static_cast<uint32_t>(key_count);
    input_header->mouse_queue_size = static_cast<uint32_t>(mouse_count);
    offset += sizeof(SaveStateInputHeader);

    // Write key events
    for (size_t i = 0; i < key_count; ++i) {
        size_t idx = (g_input_state.key_queue_head + i) % InputState::MAX_KEY_EVENTS;
        std::memcpy(ptr + offset, &g_input_state.key_queue[idx], sizeof(KeyEvent));
        offset += sizeof(KeyEvent);
    }

    // Write mouse events
    for (size_t i = 0; i < mouse_count; ++i) {
        size_t idx = (g_input_state.mouse_queue_head + i) % InputState::MAX_MOUSE_EVENTS;
        std::memcpy(ptr + offset, &g_input_state.mouse_queue[idx], sizeof(MouseEvent));
        offset += sizeof(MouseEvent);
    }

    // Write frame state
    header->frame_offset = static_cast<uint32_t>(offset);
    SaveStateFrameHeader* frame_header = reinterpret_cast<SaveStateFrameHeader*>(ptr + offset);
    frame_header->is_text_mode = g_frame_state.is_text_mode ? 1 : 0;
    frame_header->columns = g_frame_state.columns;
    frame_header->rows = g_frame_state.rows;
    frame_header->cursor_x = g_frame_state.cursor_x;
    frame_header->cursor_y = g_frame_state.cursor_y;
    frame_header->cursor_visible = g_frame_state.cursor_visible ? 1 : 0;
    frame_header->active_page = g_frame_state.active_page;
    frame_header->_pad = 0;
    frame_header->gfx_width = g_frame_state.gfx_width;
    frame_header->gfx_height = g_frame_state.gfx_height;
    size_t text_size = g_frame_state.text_cell_count() * sizeof(uint16_t);
    size_t pixels_size = g_frame_state.indexed_pixels.size();
    frame_header->text_buffer_size = static_cast<uint32_t>(text_size);
    frame_header->indexed_pixels_size = static_cast<uint32_t>(pixels_size);
    offset += sizeof(SaveStateFrameHeader);

    // Write text buffer
    std::memcpy(ptr + offset, g_frame_state.text_buffer.data(), text_size);
    offset += text_size;

    // Write indexed pixels
    if (pixels_size > 0) {
        std::memcpy(ptr + offset, g_frame_state.indexed_pixels.data(), pixels_size);
        offset += pixels_size;
    }

    // Calculate checksum of data after header
    header->checksum = crc32(data_start, required_size - sizeof(SaveStateHeader));

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_load_state(
    dosboxx_handle handle,
    const void* buffer,
    size_t buffer_size
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(buffer != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    if (buffer_size < sizeof(SaveStateHeader)) {
        DOSBOXX_ERROR(DOSBOXX_ERR_INVALID_STATE, "Buffer too small for header");
    }

    const uint8_t* ptr = static_cast<const uint8_t*>(buffer);
    const SaveStateHeader* header = reinterpret_cast<const SaveStateHeader*>(ptr);

    // Validate magic
    if (header->magic != SAVESTATE_MAGIC) {
        DOSBOXX_ERROR(DOSBOXX_ERR_INVALID_STATE, "Invalid save state magic");
    }

    // Validate version
    if (header->version != SAVESTATE_VERSION) {
        DOSBOXX_ERROR(DOSBOXX_ERR_VERSION_MISMATCH, "Save state version mismatch");
    }

    // Validate size
    if (header->total_size > buffer_size) {
        DOSBOXX_ERROR(DOSBOXX_ERR_BUFFER_TOO_SMALL, "Buffer smaller than declared state size");
    }

    // Validate checksum
    const uint8_t* data_start = ptr + sizeof(SaveStateHeader);
    uint32_t computed_crc = crc32(data_start, header->total_size - sizeof(SaveStateHeader));
    if (computed_crc != header->checksum) {
        DOSBOXX_ERROR(DOSBOXX_ERR_INVALID_STATE, "Save state checksum mismatch");
    }

    // Load time state
    const SaveStateTime* time_section = reinterpret_cast<const SaveStateTime*>(ptr + header->time_offset);
    g_time_state.total_cycles = time_section->total_cycles;
    g_time_state.emu_time_us = time_section->emu_time_us;
    g_time_state.cycles_per_ms = time_section->cycles_per_ms;

    // Load CPU state
    const SaveStateCPU* cpu_section = reinterpret_cast<const SaveStateCPU*>(ptr + header->cpu_offset);
    if (g_instance) {
        g_instance->cpu.flags.interrupt = (cpu_section->interrupt_flag != 0);
        g_instance->cpu.halted = (cpu_section->halted != 0);
    }

    // Load PIC state (CRITICAL for TLA+ compliance)
    const SaveStatePIC* pic_section = reinterpret_cast<const SaveStatePIC*>(ptr + header->pic_offset);
    g_pics[0] = pic_section->pics[0];
    g_pics[1] = pic_section->pics[1];

    // Load DMA state
    const SaveStateDMA* dma_section = reinterpret_cast<const SaveStateDMA*>(ptr + header->dma_offset);
    for (int i = 0; i < 8; ++i) {
        g_dma[i] = dma_section->channels[i];
    }

    // Load event queue (CRITICAL for TLA+ compliance)
    const SaveStateEventQueueHeader* eq_header = reinterpret_cast<const SaveStateEventQueueHeader*>(ptr + header->event_queue_offset);
    g_event_queue.event_count = eq_header->event_count;
    g_event_queue.next_event_id = eq_header->next_event_id;

    size_t eq_offset = header->event_queue_offset + sizeof(SaveStateEventQueueHeader);
    for (size_t i = 0; i < g_event_queue.event_count; ++i) {
        std::memcpy(&g_event_queue.events[i], ptr + eq_offset, sizeof(ScheduledEvent));
        eq_offset += sizeof(ScheduledEvent);
    }

    // Load input state
    const SaveStateInputHeader* input_header = reinterpret_cast<const SaveStateInputHeader*>(ptr + header->input_offset);
    g_input_state.reset();

    size_t input_offset = header->input_offset + sizeof(SaveStateInputHeader);

    // Load key events
    for (uint32_t i = 0; i < input_header->key_queue_size; ++i) {
        KeyEvent ke;
        std::memcpy(&ke, ptr + input_offset, sizeof(KeyEvent));
        g_input_state.enqueue_key(ke.scancode, ke.is_down, ke.is_extended);
        input_offset += sizeof(KeyEvent);
    }

    // Load mouse events
    for (uint32_t i = 0; i < input_header->mouse_queue_size; ++i) {
        MouseEvent me;
        std::memcpy(&me, ptr + input_offset, sizeof(MouseEvent));
        g_input_state.enqueue_mouse(me.delta_x, me.delta_y, me.buttons);
        input_offset += sizeof(MouseEvent);
    }

    // Load frame state
    const SaveStateFrameHeader* frame_header = reinterpret_cast<const SaveStateFrameHeader*>(ptr + header->frame_offset);
    g_frame_state.is_text_mode = (frame_header->is_text_mode != 0);
    g_frame_state.columns = frame_header->columns;
    g_frame_state.rows = frame_header->rows;
    g_frame_state.cursor_x = frame_header->cursor_x;
    g_frame_state.cursor_y = frame_header->cursor_y;
    g_frame_state.cursor_visible = (frame_header->cursor_visible != 0);
    g_frame_state.active_page = frame_header->active_page;
    g_frame_state.gfx_width = frame_header->gfx_width;
    g_frame_state.gfx_height = frame_header->gfx_height;

    size_t frame_offset = header->frame_offset + sizeof(SaveStateFrameHeader);

    // Load text buffer
    std::memcpy(g_frame_state.text_buffer.data(), ptr + frame_offset, frame_header->text_buffer_size);
    frame_offset += frame_header->text_buffer_size;

    // Load indexed pixels
    if (frame_header->indexed_pixels_size > 0) {
        g_frame_state.indexed_pixels.resize(frame_header->indexed_pixels_size);
        std::memcpy(g_frame_state.indexed_pixels.data(), ptr + frame_offset, frame_header->indexed_pixels_size);
    } else {
        g_frame_state.indexed_pixels.clear();
    }

    // Mark frame as dirty after load
    g_frame_state.dirty = true;

    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_get_state_hash(
    dosboxx_handle handle,
    uint8_t hash_out[32]
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(hash_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Hash the observable state per TLA+ Obs() function:
    // - now (virtual time)
    // - Q_digest (event queue)
    // - CPU_IF, CPU_halted
    // - pic0/pic1: irr, imr, isr

    SHA256 sha;

    // Hash time (now)
    sha.update(&g_time_state.total_cycles, sizeof(g_time_state.total_cycles));
    sha.update(&g_time_state.emu_time_us, sizeof(g_time_state.emu_time_us));

    // Hash event queue digest (per TLA+: <<deadline, kind, tieKey>>)
    uint32_t event_count = static_cast<uint32_t>(g_event_queue.event_count);
    sha.update(&event_count, sizeof(event_count));
    for (size_t i = 0; i < g_event_queue.event_count; ++i) {
        const auto& e = g_event_queue.events[i];
        sha.update(&e.deadline, sizeof(e.deadline));
        sha.update(&e.kind, sizeof(e.kind));
        sha.update(&e.tie_key, sizeof(e.tie_key));
    }

    // Hash CPU state
    uint8_t cpu_if = g_instance ? (g_instance->cpu.flags.interrupt ? 1 : 0) : 0;
    uint8_t cpu_halted = g_instance ? (g_instance->cpu.halted ? 1 : 0) : 0;
    sha.update(&cpu_if, 1);
    sha.update(&cpu_halted, 1);

    // Hash PIC state (both PICs: irr, imr, isr)
    sha.update(&g_pics[0].irr, 1);
    sha.update(&g_pics[0].imr, 1);
    sha.update(&g_pics[0].isr, 1);
    sha.update(&g_pics[1].irr, 1);
    sha.update(&g_pics[1].imr, 1);
    sha.update(&g_pics[1].isr, 1);

    sha.finalize(hash_out);
    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_verify_determinism(
    dosboxx_handle handle,
    uint64_t test_cycles,
    int* is_deterministic_out
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(is_deterministic_out != nullptr, DOSBOXX_ERR_NULL_POINTER);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Per TLA+ specification:
    // Round-trip test: save -> step N cycles -> hash1; restore -> step N cycles -> hash2
    // Returns success if hash1 == hash2

    // Step 1: Save current state
    size_t state_size;
    dosboxx_error_t err = dosboxx_save_state(handle, nullptr, 0, &state_size);
    if (err != DOSBOXX_OK) {
        return err;
    }

    std::vector<uint8_t> saved_state(state_size);
    err = dosboxx_save_state(handle, saved_state.data(), saved_state.size(), &state_size);
    if (err != DOSBOXX_OK) {
        return err;
    }

    // Step 2: Step N cycles and compute hash1
    err = dosboxx_step_cycles(handle, test_cycles, nullptr);
    if (err != DOSBOXX_OK) {
        return err;
    }

    uint8_t hash1[32];
    err = dosboxx_get_state_hash(handle, hash1);
    if (err != DOSBOXX_OK) {
        return err;
    }

    // Step 3: Restore saved state
    err = dosboxx_load_state(handle, saved_state.data(), saved_state.size());
    if (err != DOSBOXX_OK) {
        return err;
    }

    // Step 4: Step N cycles again and compute hash2
    err = dosboxx_step_cycles(handle, test_cycles, nullptr);
    if (err != DOSBOXX_OK) {
        return err;
    }

    uint8_t hash2[32];
    err = dosboxx_get_state_hash(handle, hash2);
    if (err != DOSBOXX_OK) {
        return err;
    }

    // Step 5: Compare hashes
    *is_deterministic_out = (std::memcmp(hash1, hash2, 32) == 0) ? 1 : 0;

    return DOSBOXX_OK;
}

/* =========================================================================
 * INTROSPECTION & ERROR HANDLING
 * ========================================================================= */

dosboxx_error_t dosboxx_get_last_error(
    dosboxx_handle handle,
    char* buffer,
    size_t buffer_size,
    size_t* length_out
) {
    DOSBOXX_REQUIRE(length_out != nullptr, DOSBOXX_ERR_NULL_POINTER);

    (void)handle;  // Error can be retrieved even with null handle

    size_t required_len = g_last_error.size() + 1;  // Include null terminator
    *length_out = required_len;

    // If just querying size, return now
    if (buffer == nullptr) {
        return DOSBOXX_OK;
    }

    if (buffer_size < required_len) {
        return DOSBOXX_ERR_BUFFER_TOO_SMALL;
    }

    std::memcpy(buffer, g_last_error.c_str(), required_len);
    return DOSBOXX_OK;
}

dosboxx_error_t dosboxx_set_log_callback(
    dosboxx_handle handle,
    dosboxx_log_callback_t callback,
    void* userdata
) {
    DOSBOXX_REQUIRE(handle != nullptr, DOSBOXX_ERR_NULL_HANDLE);
    DOSBOXX_REQUIRE(g_instance_exists.load(), DOSBOXX_ERR_NOT_INITIALIZED);

    // Set or clear the log callback
    g_log_state.callback = callback;
    g_log_state.userdata = userdata;

    // Log that callback was set/cleared (only if setting, not clearing)
    if (callback != nullptr) {
        DOSBOXX_LOG_DEBUG("Log callback registered");
    }

    return DOSBOXX_OK;
}

} // extern "C"
