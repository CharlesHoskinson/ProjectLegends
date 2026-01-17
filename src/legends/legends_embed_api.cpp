/**
 * @file legends_embed_api.cpp
 * @brief Embeddable DOSBox-X API - Implementation
 *
 * Phase 1: Core lifecycle functions (version, create, destroy)
 * Phase 2: Deterministic stepping (step_ms, step_cycles, time queries)
 * Phase 3: Frame capture (text, RGB, dirty tracking, cursor)
 * Phase 4+: Input, save/load (stubs)
 *
 * NOTE: This implementation bridges to the DOSBox-X engine library
 * (engine/include/dosbox/dosbox_library.h) for core emulation.
 * The legends_* functions delegate to dosbox_lib_* functions.
 */

#include "legends/legends_embed.h"
#include "legends/machine_context.h"
#include "legends/vision_framebuffer.h"

// DOSBox-X Engine Bridge (PR #22)
#include "dosbox/dosbox_library.h"
#include "dosbox/error_mapping.h"

#include <atomic>
#include <cstring>
#include <memory>
#include <string>
#include <array>
#include <vector>
#include <cstdint>
#include <thread>

namespace {

// ─────────────────────────────────────────────────────────────────────────────
// Instance State
// ─────────────────────────────────────────────────────────────────────────────

// Single instance enforcement
std::atomic<bool> g_instance_exists{false};

// Owner thread ID - core must only be accessed from creating thread
std::thread::id g_owner_thread_id{};

// The actual machine instance
std::unique_ptr<legends::MachineContext> g_instance;

// DOSBox-X Engine Bridge Handle (PR #22)
// This handle is used for delegating to the DOSBox-X library API
dosbox_lib_handle_t g_engine_handle{nullptr};

// Configuration stored from create
legends_config_t g_config;

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
    legends_log_callback_t callback = nullptr;
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
    legends::vision::VgaPalette palette;

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
        palette = legends::vision::VgaPalette{};
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
// Input State - Unified queue preserving device interleaving order
// Determinism requires preserved order across device types (keyboard/mouse)
// ─────────────────────────────────────────────────────────────────────────────

// Unified input event type that preserves ordering across device types
enum class InputEventType : uint8_t { Key = 0, Mouse = 1 };

struct InputEvent {
    InputEventType type;
    uint64_t sequence;  // Global sequence number for ordering
    union {
        struct {
            uint8_t scancode;
            bool is_down;
            bool is_extended;
        } key;
        struct {
            int16_t delta_x;
            int16_t delta_y;
            uint8_t buttons;
        } mouse;
    };
};

struct InputState {
    // Unified queue combining keyboard and mouse events
    static constexpr size_t MAX_INPUT_EVENTS = 320;  // Combined capacity
    static constexpr size_t EFFECTIVE_CAPACITY = MAX_INPUT_EVENTS - 1;  // Ring buffer uses one-slot-empty design
    std::array<InputEvent, MAX_INPUT_EVENTS> queue{};
    size_t head = 0;
    size_t tail = 0;
    uint64_t next_sequence = 0;

    // Current mouse button state (for tracking)
    uint8_t mouse_buttons = 0;

    [[nodiscard]] size_t size() const noexcept {
        return (tail >= head) ? (tail - head) : (MAX_INPUT_EVENTS - head + tail);
    }

    [[nodiscard]] bool full() const noexcept {
        return size() >= EFFECTIVE_CAPACITY;
    }

    [[nodiscard]] bool empty() const noexcept {
        return head == tail;
    }

    bool enqueue_key(uint8_t scancode, bool is_down, bool is_extended) {
        if (full()) return false;
        auto& evt = queue[tail];
        evt.type = InputEventType::Key;
        evt.sequence = next_sequence++;
        evt.key.scancode = scancode;
        evt.key.is_down = is_down;
        evt.key.is_extended = is_extended;
        tail = (tail + 1) % MAX_INPUT_EVENTS;
        return true;
    }

    bool enqueue_mouse(int16_t dx, int16_t dy, uint8_t buttons) {
        if (full()) return false;
        auto& evt = queue[tail];
        evt.type = InputEventType::Mouse;
        evt.sequence = next_sequence++;
        evt.mouse.delta_x = dx;
        evt.mouse.delta_y = dy;
        evt.mouse.buttons = buttons;
        tail = (tail + 1) % MAX_INPUT_EVENTS;
        mouse_buttons = buttons;
        return true;
    }

    bool dequeue(InputEvent* out) {
        if (empty()) return false;
        *out = queue[head];
        head = (head + 1) % MAX_INPUT_EVENTS;
        return true;
    }

    bool peek(InputEvent* out) const {
        if (empty()) return false;
        *out = queue[head];
        return true;
    }

    void pop() {
        if (!empty()) {
            head = (head + 1) % MAX_INPUT_EVENTS;
        }
    }

    // Enqueue a raw event with its original sequence (for loading saved state)
    bool enqueue_raw(const InputEvent& evt) {
        if (full()) return false;
        queue[tail] = evt;
        tail = (tail + 1) % MAX_INPUT_EVENTS;
        // Update mouse_buttons if it's a mouse event
        if (evt.type == InputEventType::Mouse) {
            mouse_buttons = evt.mouse.buttons;
        }
        return true;
    }

    void clear() {
        head = tail = 0;
        next_sequence = 0;
        mouse_buttons = 0;
    }

    void reset() {
        clear();
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
constexpr uint32_t SAVESTATE_VERSION = 3;  // Version 3: Unified input queue, portable serialization

// ─────────────────────────────────────────────────────────────────────────────
// Portable Serialization Helpers (little-endian, cross-platform)
// Uses little-endian byte shifts - fully portable across platforms
// ─────────────────────────────────────────────────────────────────────────────

// Wire format sizes (fixed across all platforms)
constexpr size_t WIRE_INPUT_EVENT_SIZE = 24;  // type(1) + pad(7) + sequence(8) + data(8)
constexpr size_t WIRE_DMA_CHANNEL_SIZE = 4;   // count(2) + flags(1) + pad(1)

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

// Portable serialization for unified InputEvent
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
legends_error_t safe_call(Func&& func) noexcept {
    try {
        return func();
    } catch (const std::bad_alloc&) {
        g_last_error = "Out of memory";
        g_log_state.error("Out of memory");
        return LEGENDS_ERR_OUT_OF_MEMORY;
    } catch (const std::exception& e) {
        g_last_error = e.what();
        g_log_state.error(e.what());
        return LEGENDS_ERR_INTERNAL;
    } catch (...) {
        g_last_error = "Unknown internal error";
        g_log_state.error("Unknown internal error");
        return LEGENDS_ERR_INTERNAL;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper Macros
// ─────────────────────────────────────────────────────────────────────────────

// Validate boundary conditions - returns error, recoverable
#define LEGENDS_REQUIRE(cond, err) \
    do { if (!(cond)) return (err); } while(0)

// Check that caller is on the owner thread
#define LEGENDS_CHECK_THREAD() \
    do { \
        if (g_instance_exists.load() && std::this_thread::get_id() != g_owner_thread_id) { \
            g_last_error = "Called from non-owner thread"; \
            return LEGENDS_ERR_WRONG_THREAD; \
        } \
    } while(0)

// Set error message, log it, and return error code
// Undef if already defined (error.h may have it)
#ifdef LEGENDS_ERROR
#undef LEGENDS_ERROR
#endif
#define LEGENDS_ERROR(err, msg) \
    do { \
        g_last_error = (msg); \
        g_log_state.error(msg); \
        return (err); \
    } while(0)

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

// Log at various levels
#define LEGENDS_LOG_INFO(msg) g_log_state.info(msg)
#define LEGENDS_LOG_DEBUG(msg) g_log_state.debug(msg)
#define LEGENDS_LOG_WARN(msg) g_log_state.warn(msg)

} // anonymous namespace

extern "C" {

// Forward declarations for internal helper functions
void sync_state_from_engine();
void sync_state_to_engine();
size_t get_engine_state_size();
legends_error_t drain_input_to_engine(uint32_t* count_out);

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
    LEGENDS_REQUIRE(handle_out != nullptr, LEGENDS_ERR_NULL_POINTER);

    // Initialize output to null
    *handle_out = nullptr;

    // Single instance enforcement using atomic compare-exchange
    bool expected = false;
    if (!g_instance_exists.compare_exchange_strong(expected, true)) {
        LEGENDS_ERROR(LEGENDS_ERR_ALREADY_CREATED,
            "Instance already exists - only one instance per process allowed");
    }

    // Store owner thread ID for thread affinity checking
    g_owner_thread_id = std::this_thread::get_id();

    // Validate config if provided
    if (config != nullptr) {
        if (config->struct_size != sizeof(legends_config_t)) {
            g_instance_exists = false;
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_CONFIG, "Invalid config struct size");
        }
        if (config->api_version != LEGENDS_API_VERSION) {
            g_instance_exists = false;
            LEGENDS_ERROR(LEGENDS_ERR_VERSION_MISMATCH, "API version mismatch");
        }
        // Store config
        g_config = *config;
    } else {
        // Use defaults
        g_config = legends_config_t{};
        g_config.struct_size = sizeof(legends_config_t);
        g_config.api_version = LEGENDS_API_VERSION;
        g_config.memory_kb = 640;
        g_config.cpu_cycles = 3000;  // Default cycles per ms
        g_config.deterministic = 1;
    }

    try {
        // Create machine configuration from legends_config
        legends::MachineConfig mc;
        mc.memory_size = static_cast<size_t>(g_config.memory_kb) * 1024;
        mc.cpu_cycles = g_config.cpu_cycles > 0 ? g_config.cpu_cycles : 3000;
        mc.deterministic = (g_config.deterministic != 0);

        // Map machine type
        switch (g_config.machine_type) {
            case 0: mc.machine_type = legends::MachineType::VGA; break;
            case 1: mc.machine_type = legends::MachineType::EGA; break;
            case 2: mc.machine_type = legends::MachineType::CGA; break;
            case 3: mc.machine_type = legends::MachineType::Hercules; break;
            case 4: mc.machine_type = legends::MachineType::Tandy; break;
            default: mc.machine_type = legends::MachineType::VGA; break;
        }

        // Create and initialize machine context
        g_instance = std::make_unique<legends::MachineContext>(mc);
        auto result = g_instance->initialize();
        if (!result.has_value()) {
            g_last_error = result.error().format();
            g_instance.reset();
            g_instance_exists = false;
            return LEGENDS_ERR_INTERNAL;
        }

        // Initialize DOSBox-X Engine Bridge (PR #22)
        // Create engine config from legends config
        dosbox_lib_config_t engine_config = DOSBOX_LIB_CONFIG_INIT;
        engine_config.memory_kb = g_config.memory_kb;
        engine_config.cpu_cycles = g_config.cpu_cycles;
        engine_config.deterministic = g_config.deterministic;

        auto engine_err = dosbox_lib_create(&engine_config, &g_engine_handle);
        if (engine_err != DOSBOX_LIB_OK) {
            g_last_error = "Failed to create DOSBox-X engine";
            g_instance.reset();
            g_instance_exists = false;
            return dosbox_to_legends_error(engine_err);
        }

        engine_err = dosbox_lib_init(g_engine_handle);
        if (engine_err != DOSBOX_LIB_OK) {
            dosbox_lib_destroy(g_engine_handle);
            g_engine_handle = nullptr;
            g_last_error = "Failed to initialize DOSBox-X engine";
            g_instance.reset();
            g_instance_exists = false;
            return dosbox_to_legends_error(engine_err);
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
        *handle_out = reinterpret_cast<legends_handle>(static_cast<uintptr_t>(1));
        g_last_error.clear();

        LEGENDS_LOG_INFO("DOSBox-X instance created successfully (with engine bridge)");
        return LEGENDS_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        g_instance.reset();
        g_instance_exists = false;
        return LEGENDS_ERR_INTERNAL;
    }
}

legends_error_t legends_destroy(legends_handle handle) {
    // Allow destroying null handle (no-op)
    if (handle == nullptr) {
        return LEGENDS_OK;
    }

    // Verify caller is on owner thread to prevent data races
    // on global state. Must check after null-handle check since LEGENDS_CHECK_THREAD
    // requires g_instance_exists to be true.
    LEGENDS_CHECK_THREAD();

    LEGENDS_LOG_INFO("Destroying DOSBox-X instance");

    // Shutdown and destroy instance
    if (g_instance) {
        g_instance->shutdown();
        g_instance.reset();
    }

    // Destroy DOSBox-X Engine Bridge (PR #22)
    if (g_engine_handle != nullptr) {
        dosbox_lib_destroy(g_engine_handle);
        g_engine_handle = nullptr;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // P3 Fix: Reset ALL global state to prevent leakage to subsequent instances
    // Previously only reset in legends_reset(), causing stale state issues
    // ─────────────────────────────────────────────────────────────────────────

    // Reset time state
    g_time_state.reset();

    // Reset frame and input state
    g_frame_state.reset();
    g_input_state.reset();

    // Reset event queue
    g_event_queue.reset();

    // Reset PIC state to defaults
    g_pics[0] = {0, 255, 0, 8, 2, {0, 0, 0}};    // Master
    g_pics[1] = {0, 255, 0, 112, 2, {0, 0, 0}};  // Slave

    // Reset DMA state
    for (auto& ch : g_dma) {
        ch = DMAChannelState{};
        ch.masked = 1;
    }

    // Reset single instance flag and owner thread
    g_instance_exists = false;
    g_owner_thread_id = std::thread::id{};
    g_last_error.clear();

    // Reset log state (do this last so we can log the destroy)
    g_log_state.reset();

    return LEGENDS_OK;
}

legends_error_t legends_reset(legends_handle handle) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);
    LEGENDS_REQUIRE(g_instance != nullptr, LEGENDS_ERR_NOT_INITIALIZED);

    try {
        auto result = g_instance->reset();
        if (!result.has_value()) {
            g_last_error = result.error().format();
            return LEGENDS_ERR_INTERNAL;
        }

        // Reset engine state for determinism
        // This ensures repeated resets produce identical starting states
        if (g_engine_handle) {
            auto engine_err = dosbox_lib_reset(g_engine_handle);
            if (engine_err != DOSBOX_LIB_OK) {
                g_last_error = "Failed to reset engine state";
                return dosbox_to_legends_error(engine_err);
            }
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
        return LEGENDS_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
        return LEGENDS_ERR_INTERNAL;
    }
}

legends_error_t legends_get_config(
    legends_handle handle,
    legends_config_t* config_out
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(config_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    *config_out = g_config;
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
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);
    LEGENDS_REQUIRE(g_instance != nullptr, LEGENDS_ERR_NOT_INITIALIZED);
    LEGENDS_REQUIRE(g_engine_handle != nullptr, LEGENDS_ERR_NOT_INITIALIZED);

    try {
        // Set context for compatibility shim (still needed for legacy code paths)
        legends::compat::ContextGuard guard(*g_instance);

        // Drain input queue before stepping to preserve device interleaving order
        legends_error_t drain_err = drain_input_to_engine(nullptr);
        if (drain_err != LEGENDS_OK) {
            g_last_error = "Input injection failed";
            if (result_out != nullptr) {
                result_out->stop_reason = LEGENDS_STOP_ERROR;
            }
            return drain_err;
        }

        // Delegate to the DOSBox library which now uses the CPU bridge
        // for actual CPU instruction execution
        dosbox_lib_step_result_t engine_result{};
        auto err = dosbox_lib_step_cycles(g_engine_handle, cycles, &engine_result);

        if (err != DOSBOX_LIB_OK) {
            g_last_error = "Engine step_cycles failed";
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
                // Callback is internal to engine; map to completed for legends
                stop_reason = LEGENDS_STOP_COMPLETED;
                break;
            default:
                stop_reason = LEGENDS_STOP_ERROR;
                break;
        }

        // Sync legends layer state from engine
        sync_state_from_engine();

        // Fill result if requested
        if (result_out != nullptr) {
            result_out->cycles_executed = engine_result.cycles_executed;
            result_out->emu_time_us = g_time_state.emu_time_us;
            result_out->stop_reason = stop_reason;
            result_out->events_processed = engine_result.events_processed;
        }

        g_last_error.clear();
        return LEGENDS_OK;

    } catch (const std::exception& e) {
        g_last_error = e.what();
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
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Convert milliseconds to cycles using fixed ratio for determinism
    uint64_t target_cycles = g_time_state.ms_to_cycles(ms);

    // Delegate to cycle-based stepping
    return legends_step_cycles(handle, target_cycles, result_out);
}

legends_error_t legends_get_emu_time(
    legends_handle handle,
    uint64_t* time_us_out
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(time_us_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    *time_us_out = g_time_state.emu_time_us;
    return LEGENDS_OK;
}

legends_error_t legends_get_total_cycles(
    legends_handle handle,
    uint64_t* cycles_out
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(cycles_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    *cycles_out = g_time_state.total_cycles;
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
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(cells_count_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

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
        return LEGENDS_OK;
    }

    // Check buffer size
    if (cells_count < required_cells) {
        return LEGENDS_ERR_BUFFER_TOO_SMALL;
    }

    // Copy text cells from internal buffer
    // Internal format: uint16_t with low byte = char, high byte = attr
    // Output format: legends_text_cell_t with character and attribute fields
    for (size_t i = 0; i < required_cells; ++i) {
        uint16_t cell = g_frame_state.text_buffer[i];
        cells[i].character = static_cast<uint8_t>(cell & 0xFF);
        cells[i].attribute = static_cast<uint8_t>((cell >> 8) & 0xFF);
    }

    // Clear dirty flag after capture
    g_frame_state.dirty = false;

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
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(size_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

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
        return LEGENDS_OK;
    }

    // Check buffer size
    if (buffer_size < required_size) {
        return LEGENDS_ERR_BUFFER_TOO_SMALL;
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

                legends::vision::RgbColor fg_color = palette[fg_idx];
                legends::vision::RgbColor bg_color = palette[bg_idx];

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
                legends::vision::RgbColor color = palette[idx];
                buffer[i * 3 + 0] = color.r;
                buffer[i * 3 + 1] = color.g;
                buffer[i * 3 + 2] = color.b;
            }
        }
    }

    // Clear dirty flag after capture
    g_frame_state.dirty = false;

    return LEGENDS_OK;
}

legends_error_t legends_is_frame_dirty(
    legends_handle handle,
    int* dirty_out
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(dirty_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    *dirty_out = g_frame_state.dirty ? 1 : 0;
    return LEGENDS_OK;
}

legends_error_t legends_get_cursor(
    legends_handle handle,
    uint8_t* x_out,
    uint8_t* y_out,
    int* visible_out
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    if (x_out != nullptr) {
        *x_out = g_frame_state.cursor_x;
    }
    if (y_out != nullptr) {
        *y_out = g_frame_state.cursor_y;
    }
    if (visible_out != nullptr) {
        *visible_out = g_frame_state.cursor_visible ? 1 : 0;
    }

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
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Queue the key event (non-extended)
    if (!g_input_state.enqueue_key(scancode, is_down != 0, false)) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
    }

    // Mark frame as dirty since input may cause visible changes
    g_frame_state.dirty = true;

    return LEGENDS_OK;
}

legends_error_t legends_key_event_ext(
    legends_handle handle,
    uint8_t scancode,
    int is_down
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Queue the extended key event (E0-prefixed)
    if (!g_input_state.enqueue_key(scancode, is_down != 0, true)) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
    }

    // Mark frame as dirty since input may cause visible changes
    g_frame_state.dirty = true;

    return LEGENDS_OK;
}

legends_error_t legends_text_input(
    legends_handle handle,
    const char* utf8_text
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(utf8_text != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

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
                        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                    }
                }

                // Press the key
                if (!g_input_state.enqueue_key(mapping.scancode, true, false)) {
                    LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                }

                // Release the key
                if (!g_input_state.enqueue_key(mapping.scancode, false, false)) {
                    LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
                }

                // Release shift if needed
                if (mapping.needs_shift) {
                    if (!g_input_state.enqueue_key(SCANCODE_LSHIFT, false, false)) {
                        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Keyboard event queue full");
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

    return LEGENDS_OK;
}

legends_error_t legends_mouse_event(
    legends_handle handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Queue the mouse event
    if (!g_input_state.enqueue_mouse(delta_x, delta_y, buttons)) {
        LEGENDS_ERROR(LEGENDS_ERR_BUFFER_TOO_SMALL, "Mouse event queue full");
    }

    // Mark frame as dirty since input may cause visible changes
    g_frame_state.dirty = true;

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
void sync_state_from_engine() {
    if (!g_engine_handle) {
        return;
    }

    // Sync timing state from engine (canonical source after stepping)
    dosbox_lib_get_total_cycles(g_engine_handle, &g_time_state.total_cycles);
    dosbox_lib_get_emu_time(g_engine_handle, &g_time_state.emu_time_us);

    // Sync PIC state from engine for hash consistency
    // This ensures legends layer hash matches actual engine state
    dosbox_lib_pic_state_t pic_state;
    if (dosbox_lib_get_pic_state(g_engine_handle, &pic_state) == DOSBOX_LIB_OK) {
        g_pics[0].irr = pic_state.master_irr;
        g_pics[0].imr = pic_state.master_imr;
        g_pics[0].isr = pic_state.master_isr;
        g_pics[1].irr = pic_state.slave_irr;
        g_pics[1].imr = pic_state.slave_imr;
        g_pics[1].isr = pic_state.slave_isr;
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
legends_error_t drain_input_to_engine(uint32_t* count_out) {
    if (count_out != nullptr) {
        *count_out = 0;
    }
    if (!g_engine_handle) return LEGENDS_OK;
    uint32_t count = 0;

    InputEvent evt;
    while (g_input_state.peek(&evt)) {
        dosbox_lib_error_t err = DOSBOX_LIB_OK;
        switch (evt.type) {
            case InputEventType::Key:
                err = dosbox_lib_inject_key(g_engine_handle,
                    evt.key.scancode,
                    evt.key.is_down ? 1 : 0,
                    evt.key.is_extended ? 1 : 0);
                break;
            case InputEventType::Mouse:
                err = dosbox_lib_inject_mouse(g_engine_handle,
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

        g_input_state.pop();
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
void sync_state_to_engine() {
    if (!g_engine_handle) {
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
size_t get_engine_state_size() {
    if (!g_engine_handle) {
        return 0;
    }
    size_t engine_size = 0;
    dosbox_lib_save_state(g_engine_handle, nullptr, 0, &engine_size);
    return engine_size;
}

// Helper: Calculate total save state size
size_t calculate_save_state_size() {
    size_t size = sizeof(SaveStateHeader);
    size += sizeof(SaveStateTime);
    size += sizeof(SaveStateCPU);
    size += sizeof(SaveStatePIC);
    // Use wire size for DMA (portable)
    size += 8 * WIRE_DMA_CHANNEL_SIZE;

    // Event queue: header + events
    size += sizeof(SaveStateEventQueueHeader);
    size += g_event_queue.event_count * sizeof(ScheduledEvent);

    // Unified input queue with portable wire format
    size += sizeof(SaveStateInputHeader);
    size += g_input_state.size() * WIRE_INPUT_EVENT_SIZE;

    // Frame state: header + text buffer + indexed pixels
    size += sizeof(SaveStateFrameHeader);
    size += g_frame_state.text_cell_count() * sizeof(uint16_t);
    size += g_frame_state.indexed_pixels.size();

    // Engine state (Phase 2 - full DOSBox context)
    size += get_engine_state_size();

    return size;
}

legends_error_t legends_save_state(
    legends_handle handle,
    void* buffer,
    size_t buffer_size,
    size_t* size_out
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(size_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Calculate required size
    size_t required_size = calculate_save_state_size();
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

    // Write DMA state (portable serialization)
    header->dma_offset = static_cast<uint32_t>(offset);
    for (int i = 0; i < 8; ++i) {
        serialize_dma_channel(ptr + offset, g_dma[i]);
        offset += WIRE_DMA_CHANNEL_SIZE;
    }

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

    // Write input state (unified queue with portable serialization)
    header->input_offset = static_cast<uint32_t>(offset);
    SaveStateInputHeader* input_header = reinterpret_cast<SaveStateInputHeader*>(ptr + offset);
    size_t input_count = g_input_state.size();
    input_header->event_count = static_cast<uint32_t>(input_count);
    input_header->next_sequence_lo = static_cast<uint32_t>(g_input_state.next_sequence & 0xFFFFFFFF);
    input_header->next_sequence_hi = static_cast<uint32_t>(g_input_state.next_sequence >> 32);
    input_header->_reserved = 0;
    offset += sizeof(SaveStateInputHeader);

    // Write unified input events with portable serialization
    for (size_t i = 0; i < input_count; ++i) {
        size_t idx = (g_input_state.head + i) % InputState::MAX_INPUT_EVENTS;
        serialize_input_event(ptr + offset, g_input_state.queue[idx]);
        offset += WIRE_INPUT_EVENT_SIZE;
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

    // Write engine state (Phase 2 - full DOSBox context)
    size_t engine_size = get_engine_state_size();
    if (engine_size > 0 && g_engine_handle) {
        // Verify buffer capacity before engine write
        size_t remaining = buffer_size - offset;
        if (engine_size > remaining) {
            // Buffer too small - report required size in size_out
            *size_out = offset + engine_size;
            return LEGENDS_ERR_BUFFER_TOO_SMALL;
        }

        header->engine_offset = static_cast<uint32_t>(offset);

        size_t actual_engine_size = 0;
        auto engine_err = dosbox_lib_save_state(
            g_engine_handle,
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
        header->engine_size = static_cast<uint32_t>(actual_engine_size);
        offset += actual_engine_size;
    } else {
        header->engine_offset = 0;
        header->engine_size = 0;
    }

    // Calculate checksum based on actual written data (offset),
    // not pre-computed required_size, in case actual sizes differed
    const size_t actual_data_size = offset - sizeof(SaveStateHeader);
    header->total_size = static_cast<uint32_t>(offset);  // Update to actual total
    header->checksum = crc32(data_start, actual_data_size);

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
    const uint8_t* ptr,
    size_t buffer_size,
    const SaveStateHeader* header
) {
    // V2 validation - basic bounds checking
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

    // Load time state (same as V3)
    const SaveStateTime* time_section = reinterpret_cast<const SaveStateTime*>(ptr + header->time_offset);
    g_time_state.total_cycles = time_section->total_cycles;
    g_time_state.emu_time_us = time_section->emu_time_us;
    g_time_state.cycles_per_ms = time_section->cycles_per_ms;

    // Load CPU state (same as V3)
    const SaveStateCPU* cpu_section = reinterpret_cast<const SaveStateCPU*>(ptr + header->cpu_offset);
    if (g_instance) {
        g_instance->cpu.flags.interrupt = (cpu_section->interrupt_flag != 0);
        g_instance->cpu.halted = (cpu_section->halted != 0);
    }

    // Load PIC state (same as V3)
    const SaveStatePIC* pic_section = reinterpret_cast<const SaveStatePIC*>(ptr + header->pic_offset);
    for (int i = 0; i < 2; ++i) {
        g_pics[i].irr = pic_section->pics[i].irr;
        g_pics[i].imr = pic_section->pics[i].imr;
        g_pics[i].isr = pic_section->pics[i].isr;
        g_pics[i].vector_base = pic_section->pics[i].vector_base;
        g_pics[i].cascade_irq = pic_section->pics[i].cascade_irq;
    }

    // Load DMA state (V2 used memcpy - may have platform issues)
    const uint8_t* dma_data = ptr + header->dma_offset;
    for (int i = 0; i < 8; ++i) {
        // V2 used raw memcpy - try to read with same struct layout
        std::memcpy(&g_dma[i], dma_data + i * sizeof(DMAChannelState), sizeof(DMAChannelState));
    }

    // Load event queue (same as V3)
    const SaveStateEventQueueHeader* eq_header =
        reinterpret_cast<const SaveStateEventQueueHeader*>(ptr + header->event_queue_offset);
    VALIDATE_COUNT_MAX(eq_header->event_count, EventQueueState::MAX_EVENTS, "V2: event_count");

    g_event_queue.event_count = eq_header->event_count;
    g_event_queue.next_event_id = eq_header->next_event_id;

    size_t eq_data_offset = header->event_queue_offset + sizeof(SaveStateEventQueueHeader);
    for (size_t i = 0; i < eq_header->event_count; ++i) {
        std::memcpy(&g_event_queue.events[i], ptr + eq_data_offset + i * sizeof(ScheduledEvent),
                    sizeof(ScheduledEvent));
    }

    // Load V2 input state and convert to unified queue
    const SaveStateInputHeader_V2* input_header_v2 =
        reinterpret_cast<const SaveStateInputHeader_V2*>(ptr + header->input_offset);

    VALIDATE_COUNT_MAX(input_header_v2->key_queue_size, V2_MAX_KEY_EVENTS, "V2: key_queue_size");
    VALIDATE_COUNT_MAX(input_header_v2->mouse_queue_size, V2_MAX_MOUSE_EVENTS, "V2: mouse_queue_size");

    // Check total events fit in unified queue
    size_t total_events = input_header_v2->key_queue_size + input_header_v2->mouse_queue_size;
    if (total_events > InputState::EFFECTIVE_CAPACITY) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "V2: Too many events for unified queue");
    }

    // Validate V2 input data bounds
    size_t key_data_size = static_cast<size_t>(input_header_v2->key_queue_size) * sizeof(KeyEvent_V2);
    size_t mouse_data_size = static_cast<size_t>(input_header_v2->mouse_queue_size) * sizeof(MouseEvent_V2);
    size_t input_data_offset = header->input_offset + sizeof(SaveStateInputHeader_V2);
    VALIDATE_DATA_BOUNDS(input_data_offset, key_data_size, verified_size);
    VALIDATE_DATA_BOUNDS(input_data_offset + key_data_size, mouse_data_size, verified_size);

    // Clear unified queue and convert V2 events
    g_input_state.clear();

    size_t offset = input_data_offset;

    // Load keyboard events first (they came first in V2 saves)
    for (uint32_t i = 0; i < input_header_v2->key_queue_size; ++i) {
        KeyEvent_V2 ke_v2;
        std::memcpy(&ke_v2, ptr + offset, sizeof(KeyEvent_V2));
        offset += sizeof(KeyEvent_V2);

        // Convert to unified queue (assign new sequence numbers)
        if (!g_input_state.enqueue_key(ke_v2.scancode, ke_v2.is_down, ke_v2.is_extended)) {
            LEGENDS_ERROR(LEGENDS_ERR_INTERNAL, "V2: Failed to enqueue key event");
        }
    }

    // Load mouse events (they came second in V2 saves)
    for (uint32_t i = 0; i < input_header_v2->mouse_queue_size; ++i) {
        MouseEvent_V2 me_v2;
        std::memcpy(&me_v2, ptr + offset, sizeof(MouseEvent_V2));
        offset += sizeof(MouseEvent_V2);

        // Convert to unified queue (assign new sequence numbers)
        if (!g_input_state.enqueue_mouse(me_v2.delta_x, me_v2.delta_y, me_v2.buttons)) {
            LEGENDS_ERROR(LEGENDS_ERR_INTERNAL, "V2: Failed to enqueue mouse event");
        }
    }

    // Load frame state (same as V3)
    const SaveStateFrameHeader* frame_header =
        reinterpret_cast<const SaveStateFrameHeader*>(ptr + header->frame_offset);

    g_frame_state.is_text_mode = frame_header->is_text_mode != 0;
    g_frame_state.columns = frame_header->columns;
    g_frame_state.rows = frame_header->rows;
    g_frame_state.cursor_x = frame_header->cursor_x;
    g_frame_state.cursor_y = frame_header->cursor_y;
    g_frame_state.cursor_visible = frame_header->cursor_visible != 0;
    g_frame_state.active_page = frame_header->active_page;
    g_frame_state.gfx_width = frame_header->gfx_width;
    g_frame_state.gfx_height = frame_header->gfx_height;

    size_t frame_data_offset = header->frame_offset + sizeof(SaveStateFrameHeader);
    size_t text_buffer_size = static_cast<size_t>(frame_header->columns) * frame_header->rows * sizeof(uint16_t);
    VALIDATE_DATA_BOUNDS(frame_data_offset, text_buffer_size, verified_size);

    // text_buffer is a fixed-size array - just copy the data (no resize needed)
    if (text_buffer_size <= g_frame_state.text_buffer.size() * sizeof(uint16_t)) {
        std::memcpy(g_frame_state.text_buffer.data(), ptr + frame_data_offset, text_buffer_size);
    }
    frame_data_offset += text_buffer_size;

    size_t pixel_buffer_size = static_cast<size_t>(frame_header->gfx_width) * frame_header->gfx_height;
    if (pixel_buffer_size > 0) {
        VALIDATE_DATA_BOUNDS(frame_data_offset, pixel_buffer_size, verified_size);
        g_frame_state.indexed_pixels.resize(pixel_buffer_size);
        std::memcpy(g_frame_state.indexed_pixels.data(), ptr + frame_data_offset, pixel_buffer_size);
    } else {
        g_frame_state.indexed_pixels.clear();
    }

    // Load engine state (same as V3)
    if (header->engine_size > 0 && g_engine_handle) {
        VALIDATE_DATA_BOUNDS(header->engine_offset, header->engine_size, verified_size);
        auto engine_err = dosbox_lib_load_state(g_engine_handle,
            ptr + header->engine_offset, header->engine_size);
        if (engine_err != DOSBOX_LIB_OK) {
            LEGENDS_ERROR(LEGENDS_ERR_INTERNAL, "V2: Engine state load failed");
        }
    }

    g_last_error.clear();
    return LEGENDS_OK;
}

legends_error_t legends_load_state(
    legends_handle handle,
    const void* buffer,
    size_t buffer_size
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(buffer != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    if (buffer_size < sizeof(SaveStateHeader)) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Buffer too small for header");
    }

    const uint8_t* ptr = static_cast<const uint8_t*>(buffer);
    const SaveStateHeader* header = reinterpret_cast<const SaveStateHeader*>(ptr);

    // Validate magic
    if (header->magic != SAVESTATE_MAGIC) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Invalid save state magic");
    }

    // Validate version - V3 is current, V2 is legacy (separate queues, non-portable)
    if (header->version == 2) {
        // V2 saves used separate keyboard/mouse queues and non-portable memcpy.
        // Load using legacy loader and convert to V3's unified queue format.
        return load_state_v2_legacy(ptr, buffer_size, header);
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
    // Now safe to read section headers (bounds validated above)
    // ─────────────────────────────────────────────────────────────────────────

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

    // Load DMA state (portable deserialization)
    size_t dma_offset = header->dma_offset;
    for (int i = 0; i < 8; ++i) {
        g_dma[i] = deserialize_dma_channel(ptr + dma_offset);
        dma_offset += WIRE_DMA_CHANNEL_SIZE;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Variable-size sections: validate counts AND data bounds before access
    // ─────────────────────────────────────────────────────────────────────────

    // Load event queue (CRITICAL for TLA+ compliance)
    const SaveStateEventQueueHeader* eq_header = reinterpret_cast<const SaveStateEventQueueHeader*>(ptr + header->event_queue_offset);

    // Validate event count doesn't exceed maximum (prevents huge allocations/OOB)
    VALIDATE_COUNT_MAX(eq_header->event_count, EventQueueState::MAX_EVENTS, "event_count");

    // Validate event data fits in buffer
    size_t events_data_size = static_cast<size_t>(eq_header->event_count) * sizeof(ScheduledEvent);
    size_t eq_data_offset = header->event_queue_offset + sizeof(SaveStateEventQueueHeader);
    VALIDATE_DATA_BOUNDS(eq_data_offset, events_data_size, verified_size);

    g_event_queue.event_count = eq_header->event_count;
    g_event_queue.next_event_id = eq_header->next_event_id;

    size_t eq_offset = eq_data_offset;
    for (size_t i = 0; i < g_event_queue.event_count; ++i) {
        std::memcpy(&g_event_queue.events[i], ptr + eq_offset, sizeof(ScheduledEvent));
        eq_offset += sizeof(ScheduledEvent);
    }

    // Load input state (unified queue with portable deserialization)
    const SaveStateInputHeader* input_header = reinterpret_cast<const SaveStateInputHeader*>(ptr + header->input_offset);

    // Validate against effective capacity (MAX - 1 due to ring buffer design)
    VALIDATE_COUNT_MAX(input_header->event_count, InputState::EFFECTIVE_CAPACITY, "input_event_count");

    // Validate input data fits in buffer (use wire format size)
    size_t input_data_size = static_cast<size_t>(input_header->event_count) * WIRE_INPUT_EVENT_SIZE;
    size_t input_data_offset = header->input_offset + sizeof(SaveStateInputHeader);
    VALIDATE_DATA_BOUNDS(input_data_offset, input_data_size, verified_size);

    g_input_state.clear();

    // Restore next_sequence from header
    g_input_state.next_sequence = static_cast<uint64_t>(input_header->next_sequence_lo) |
                                  (static_cast<uint64_t>(input_header->next_sequence_hi) << 32);

    size_t input_offset = input_data_offset;

    // Load unified input events with portable deserialization
    // Use enqueue_raw to preserve original sequence numbers
    for (uint32_t i = 0; i < input_header->event_count; ++i) {
        InputEvent evt = deserialize_input_event(ptr + input_offset);

        // Validate event type
        if (evt.type != InputEventType::Key && evt.type != InputEventType::Mouse) {
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Unknown input event type in save state");
        }

        // Use enqueue_raw to preserve the original sequence number from the save
        if (!g_input_state.enqueue_raw(evt)) {
            // Queue overflow during load - should never happen with validated count
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Input queue overflow during load");
        }

        input_offset += WIRE_INPUT_EVENT_SIZE;
    }

    // Restore next_sequence from saved state (enqueue_raw doesn't modify it)
    g_input_state.next_sequence = static_cast<uint64_t>(input_header->next_sequence_lo) |
                                  (static_cast<uint64_t>(input_header->next_sequence_hi) << 32);

    // Load frame state
    const SaveStateFrameHeader* frame_header = reinterpret_cast<const SaveStateFrameHeader*>(ptr + header->frame_offset);

    // Validate frame buffer sizes don't exceed maximums
    constexpr size_t max_text_buffer_bytes = FrameState::MAX_TEXT_CELLS * sizeof(uint16_t);
    VALIDATE_COUNT_MAX(frame_header->text_buffer_size, max_text_buffer_bytes, "text_buffer_size");
    VALIDATE_COUNT_MAX(frame_header->indexed_pixels_size, MAX_INDEXED_PIXELS_SIZE, "indexed_pixels_size");

    // Validate frame data fits in buffer
    size_t frame_data_offset = header->frame_offset + sizeof(SaveStateFrameHeader);
    VALIDATE_DATA_BOUNDS(frame_data_offset, frame_header->text_buffer_size, verified_size);
    VALIDATE_DATA_BOUNDS(frame_data_offset + frame_header->text_buffer_size,
                         frame_header->indexed_pixels_size, verified_size);

    // Validate frame dimensions against maximum values
    // Maximum is 80 columns x 50 rows for text mode
    constexpr uint8_t MAX_COLUMNS = 80;
    constexpr uint8_t MAX_ROWS = 50;

    if (frame_header->columns > MAX_COLUMNS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Frame columns exceeds maximum (80)");
    }
    if (frame_header->rows > MAX_ROWS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Frame rows exceeds maximum (50)");
    }

    // Validate that columns * rows doesn't exceed MAX_TEXT_CELLS
    const size_t cell_count = static_cast<size_t>(frame_header->columns) * frame_header->rows;
    if (cell_count > FrameState::MAX_TEXT_CELLS) {
        LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, "Frame cell count exceeds maximum");
    }

    g_frame_state.is_text_mode = (frame_header->is_text_mode != 0);
    g_frame_state.columns = frame_header->columns;
    g_frame_state.rows = frame_header->rows;
    g_frame_state.cursor_x = frame_header->cursor_x;
    g_frame_state.cursor_y = frame_header->cursor_y;
    g_frame_state.cursor_visible = (frame_header->cursor_visible != 0);
    g_frame_state.active_page = frame_header->active_page;
    g_frame_state.gfx_width = frame_header->gfx_width;
    g_frame_state.gfx_height = frame_header->gfx_height;

    size_t frame_offset = frame_data_offset;

    // Load text buffer (bounds now validated)
    std::memcpy(g_frame_state.text_buffer.data(), ptr + frame_offset, frame_header->text_buffer_size);
    frame_offset += frame_header->text_buffer_size;

    // Load indexed pixels (bounds now validated)
    if (frame_header->indexed_pixels_size > 0) {
        g_frame_state.indexed_pixels.resize(frame_header->indexed_pixels_size);
        std::memcpy(g_frame_state.indexed_pixels.data(), ptr + frame_offset, frame_header->indexed_pixels_size);
    } else {
        g_frame_state.indexed_pixels.clear();
    }

    // Mark frame as dirty after load
    g_frame_state.dirty = true;

    // Load engine state (Phase 2 - full DOSBox context)
    // V2 save states with an active engine MUST include engine state for determinism
    if (g_engine_handle) {
        if (header->engine_offset == 0 || header->engine_size == 0) {
            // Engine is active but save state has no engine data - would leave engine stale
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE,
                "Save state missing engine data (required when engine is active)");
        }

        // Validate engine state bounds against verified_size (checksummed region)
        VALIDATE_DATA_BOUNDS(header->engine_offset, header->engine_size, verified_size);

        auto engine_err = dosbox_lib_load_state(
            g_engine_handle,
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

    return LEGENDS_OK;
}

legends_error_t legends_get_state_hash(
    legends_handle handle,
    uint8_t hash_out[32]
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(hash_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Sync state from engine first to ensure hash consistency
    sync_state_from_engine();

    SHA256 sha;

    // Include engine's authoritative hash as primary source
    // This ensures the hash reflects actual engine state, not stale legends layer state
    if (g_engine_handle) {
        uint8_t engine_hash[32];
        if (dosbox_lib_get_state_hash(g_engine_handle, engine_hash) == DOSBOX_LIB_OK) {
            sha.update(engine_hash, 32);
        }
    }

    // Include legends-layer state that affects determinism
    // (pending input queue events will affect future state)
    uint64_t input_queue_size = g_input_state.size();
    sha.update(&input_queue_size, sizeof(input_queue_size));

    // If there are pending input events, hash their sequence numbers
    // to catch ordering differences
    if (input_queue_size > 0) {
        sha.update(&g_input_state.next_sequence, sizeof(g_input_state.next_sequence));
        size_t idx = g_input_state.head;
        for (size_t i = 0; i < input_queue_size; ++i) {
            const auto& evt = g_input_state.queue[idx];
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
    sha.update(&g_time_state.total_cycles, sizeof(g_time_state.total_cycles));
    sha.update(&g_time_state.emu_time_us, sizeof(g_time_state.emu_time_us));

    // Hash PIC state (synced from engine in sync_state_from_engine)
    sha.update(&g_pics[0].irr, 1);
    sha.update(&g_pics[0].imr, 1);
    sha.update(&g_pics[0].isr, 1);
    sha.update(&g_pics[1].irr, 1);
    sha.update(&g_pics[1].imr, 1);
    sha.update(&g_pics[1].isr, 1);

    // Include legends-layer event queue (scheduled events affect timing)
    sha.update(&g_event_queue.event_count, sizeof(g_event_queue.event_count));
    sha.update(&g_event_queue.next_event_id, sizeof(g_event_queue.next_event_id));
    for (size_t i = 0; i < g_event_queue.event_count; ++i) {
        sha.update(&g_event_queue.events[i].id, sizeof(g_event_queue.events[i].id));
        sha.update(&g_event_queue.events[i].deadline, sizeof(g_event_queue.events[i].deadline));
    }

    sha.finalize(hash_out);
    return LEGENDS_OK;
}

legends_error_t legends_verify_determinism(
    legends_handle handle,
    uint64_t test_cycles,
    int* is_deterministic_out
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(is_deterministic_out != nullptr, LEGENDS_ERR_NULL_POINTER);
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Per TLA+ specification:
    // Round-trip test: save -> step N cycles -> hash1; restore -> step N cycles -> hash2
    // Returns success if hash1 == hash2

    // Step 1: Save current state
    size_t state_size;
    legends_error_t err = legends_save_state(handle, nullptr, 0, &state_size);
    if (err != LEGENDS_OK) {
        return err;
    }

    std::vector<uint8_t> saved_state(state_size);
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

    (void)handle;  // Error can be retrieved even with null handle

    size_t required_len = g_last_error.size() + 1;  // Include null terminator
    *length_out = required_len;

    // If just querying size, return now
    if (buffer == nullptr) {
        return LEGENDS_OK;
    }

    if (buffer_size < required_len) {
        return LEGENDS_ERR_BUFFER_TOO_SMALL;
    }

    std::memcpy(buffer, g_last_error.c_str(), required_len);
    return LEGENDS_OK;
}

legends_error_t legends_set_log_callback(
    legends_handle handle,
    legends_log_callback_t callback,
    void* userdata
) {
    LEGENDS_REQUIRE(handle != nullptr, LEGENDS_ERR_NULL_HANDLE);
    LEGENDS_CHECK_THREAD();
    LEGENDS_REQUIRE(g_instance_exists.load(), LEGENDS_ERR_NOT_INITIALIZED);

    // Set or clear the log callback
    g_log_state.callback = callback;
    g_log_state.userdata = userdata;

    // Log that callback was set/cleared (only if setting, not clearing)
    if (callback != nullptr) {
        LEGENDS_LOG_DEBUG("Log callback registered");
    }

    return LEGENDS_OK;
}

} // extern "C"
