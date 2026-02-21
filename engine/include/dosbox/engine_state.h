/**
 * @file engine_state.h
 * @brief Engine state serialization format for save/load.
 *
 * Defines the binary format used by dosbox_lib_save_state() and
 * dosbox_lib_load_state() to serialize the DOSBoxContext state.
 *
 * Format version 3 includes:
 * - Header with magic, version, checksums
 * - Timing state
 * - PIC state (interrupt controller)
 * - Keyboard state (full 96-entry buffer) [V3]
 * - CPU state (cycle counters, NMI, halt) [V2]
 * - Memory state (page config, A20 gate, LFB) [V2]
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_ENGINE_STATE_H
#define DOSBOX_ENGINE_STATE_H

#include <cstdint>
#include <cstddef>

namespace dosbox {

// ═══════════════════════════════════════════════════════════════════════════════
// Constants
// ═══════════════════════════════════════════════════════════════════════════════

/// Magic number for engine state: "DBXE" (DOSBox-X Engine)
constexpr uint32_t ENGINE_STATE_MAGIC = 0x45584244;

/// Current engine state format version
/// V3: keyboard buffer expanded from 16 to 96 entries (H1)
constexpr uint32_t ENGINE_STATE_VERSION = 3;

// ═══════════════════════════════════════════════════════════════════════════════
// Engine State Header
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Header for serialized engine state.
 *
 * Contains magic number, version, total size, checksum,
 * and offsets to each serialized section.
 */
struct EngineStateHeader {
    uint32_t magic;              ///< ENGINE_STATE_MAGIC
    uint32_t version;            ///< ENGINE_STATE_VERSION
    uint32_t total_size;         ///< Total size including header
    uint32_t checksum;           ///< CRC32 of data after header
    uint32_t timing_offset;      ///< Offset to EngineStateTiming
    uint32_t pic_offset;         ///< Offset to EngineStatePic
    uint32_t keyboard_offset;    ///< Offset to EngineStateKeyboard
    uint32_t cpu_offset;         ///< Offset to EngineStateCpu [V2]
    uint32_t memory_offset;      ///< Offset to EngineStateMemory [V2]
    uint32_t _reserved[3];       ///< Reserved for future sections
};
static_assert(sizeof(EngineStateHeader) == 48, "EngineStateHeader must be 48 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// Timing State Section
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized timing state.
 *
 * Corresponds to DOSBoxContext::timing (TimingState).
 */
struct EngineStateTiming {
    uint64_t total_cycles;       ///< Total CPU cycles executed
    uint32_t virtual_ticks_ms;   ///< Emulated milliseconds
    int32_t ticks_done;          ///< Ticks completed this frame
    uint32_t ticks_scheduled;    ///< Ticks scheduled this frame
    uint32_t ticks_remain;       ///< Remaining ticks
    uint32_t ticks_added;        ///< Ticks added this cycle
    uint32_t frame_ticks;        ///< Ticks for current frame
    uint8_t locked;              ///< Ticks locked (turbo mode)
    uint8_t _pad[7];
};
static_assert(sizeof(EngineStateTiming) == 40, "EngineStateTiming must be 40 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// PIC State Section
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized PIC (interrupt controller) state.
 *
 * Corresponds to DOSBoxContext::pic (PicState).
 */
struct EngineStatePic {
    uint64_t ticks;              ///< PIC tick counter
    uint32_t irq_check;          ///< Pending IRQ bitmap
    uint32_t irq_check_pending;  ///< Deferred IRQ check
    int8_t master_cascade_irq;   ///< Cascade IRQ line (usually 2)
    uint8_t master_imr;          ///< Master PIC interrupt mask
    uint8_t slave_imr;           ///< Slave PIC interrupt mask
    uint8_t master_isr;          ///< Master PIC in-service register
    uint8_t slave_isr;           ///< Slave PIC in-service register
    uint8_t auto_eoi;            ///< Auto end-of-interrupt mode
    uint8_t in_event_service;    ///< Currently servicing event
    uint8_t _pad;
};
static_assert(sizeof(EngineStatePic) == 24, "EngineStatePic must be 24 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// Keyboard State Section
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized keyboard controller state.
 *
 * Corresponds to DOSBoxContext::keyboard (KeyboardState).
 * Includes ALL fields that contribute to the state hash.
 * V2: Expanded to include buffer contents, 8042, repeat, and all flags.
 */
struct EngineStateKeyboard {
    // Main keyboard buffer contents (96 entries x 2 bytes = 192 bytes)
    // V3: expanded from 16 to match KeyboardState::BUFFER_SIZE (H1 fix)
    uint16_t buffer[96];

    // 32-bit fields
    uint32_t buffer_used;        ///< Entries used in buffer
    uint32_t buffer_pos;         ///< Buffer read position
    int32_t pending_key;         ///< Pending key event
    uint32_t repeat_key;         ///< Key being repeated
    uint32_t repeat_wait;        ///< Repeat wait counter
    uint32_t repeat_pause;       ///< Initial repeat pause
    uint32_t repeat_rate;        ///< Repeat rate
    uint32_t led_state;          ///< LED state

    // 8042 controller buffer
    uint8_t buf8042[8];          ///< 8042 response buffer
    uint8_t buf8042_len;         ///< 8042 buffer length
    uint8_t buf8042_pos;         ///< 8042 buffer position

    // Single-byte fields (packed)
    uint8_t scanset;             ///< Current scan code set
    uint8_t enabled;             ///< Keyboard enabled
    uint8_t active;              ///< Keyboard active
    uint8_t p60data;             ///< Port 0x60 data
    uint8_t p60changed;          ///< Port 0x60 changed
    uint8_t num_lock;            ///< Num lock
    uint8_t caps_lock;           ///< Caps lock
    uint8_t scroll_lock;         ///< Scroll lock
    uint8_t command;             ///< Last command
    uint8_t expecting_data;      ///< Expecting data byte
    uint8_t scanning;            ///< Scanning enabled
    uint8_t auxactive;           ///< Aux port active
    uint8_t scheduled;           ///< Event scheduled
    uint8_t auxchanged;          ///< Aux data changed
    uint8_t pending_key_state;   ///< Pending key state
    uint8_t cb_override_inhibit; ///< CB override inhibit
    uint8_t cb_irq12;            ///< CB IRQ12 (PS/2 mouse)
    uint8_t cb_irq1;             ///< CB IRQ1 (keyboard)
    uint8_t cb_xlat;             ///< CB scancode translation
    uint8_t cb_sys;              ///< CB system flag
    uint8_t ps2_mouse_enabled;   ///< PS/2 mouse enabled
    uint8_t a20_gate;            ///< A20 gate via keyboard
    uint8_t leftalt_pressed;     ///< Left Alt pressed
    uint8_t rightalt_pressed;    ///< Right Alt pressed
    uint8_t leftctrl_pressed;    ///< Left Ctrl pressed
    uint8_t rightctrl_pressed;   ///< Right Ctrl pressed
    uint8_t leftshift_pressed;   ///< Left Shift pressed
    uint8_t rightshift_pressed;  ///< Right Shift pressed
    uint8_t _pad[2];             ///< Pad to 4-byte boundary
};
static_assert(sizeof(EngineStateKeyboard) == 264, "EngineStateKeyboard must be 264 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// CPU State Section [V2]
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized CPU state.
 *
 * Corresponds to DOSBoxContext::cpu_state (CpuState).
 * Includes cycle counters and NMI state — all determinism-relevant.
 */
struct EngineStateCpu {
    int64_t cycles;              ///< CPU_Cycles - current cycle counter
    int64_t cycle_left;          ///< CPU_CycleLeft - remaining in timeslice
    int64_t cycle_max;           ///< CPU_CycleMax - max per timeslice
    int64_t cycle_old_max;       ///< CPU_OldCycleMax - previous max
    int64_t cycle_percent_used;  ///< CPU_CyclePercUsed - percentage used
    int64_t cycle_limit;         ///< CPU_CycleLimit - hard limit (-1 = none)
    int64_t cycle_up;            ///< CPU_CycleUp - upward adjustment
    int64_t cycle_down;          ///< CPU_CycleDown - downward adjustment
    int64_t cycles_set;          ///< CPU_CyclesSet - configured cycles
    int64_t io_delay_removed;    ///< CPU_IODelayRemoved - IO compensation
    uint32_t extflags_toggle;    ///< CPU_extflags_toggle - ID/AC toggles
    uint8_t cycle_auto_adjust;   ///< CPU_CycleAutoAdjust
    uint8_t skip_cycle_auto_adjust; ///< CPU_SkipCycleAutoAdjust
    uint8_t nmi_gate;            ///< CPU_NMI_gate
    uint8_t nmi_active;          ///< CPU_NMI_active
    uint8_t nmi_pending;         ///< CPU_NMI_pending
    uint8_t halted;              ///< CPU in HLT state
    uint8_t _pad[6];
};
static_assert(sizeof(EngineStateCpu) == 96, "EngineStateCpu must be 96 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// Memory State Section [V2]
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized memory configuration state.
 *
 * Corresponds to DOSBoxContext::memory (MemoryState).
 * Includes page config, A20 gate, and LFB regions.
 * Does NOT include raw memory contents (too large for fast mode).
 */
struct EngineStateMemory {
    uint64_t size;                      ///< Allocated memory size in bytes
    uint32_t pages;                     ///< Total memory pages
    uint32_t handler_pages;             ///< Page handler entries
    uint32_t reported_pages;            ///< Pages reported to guest
    uint32_t reported_pages_4gb;        ///< Pages above 4GB
    uint32_t lfb_start_page;            ///< VGA LFB start page
    uint32_t lfb_end_page;              ///< VGA LFB end page
    uint32_t lfb_pages;                 ///< VGA LFB page count
    uint32_t lfb_mmio_start_page;       ///< VGA MMIO start page
    uint32_t lfb_mmio_end_page;         ///< VGA MMIO end page
    uint32_t lfb_mmio_pages;            ///< VGA MMIO page count
    uint32_t mem_alias_pagemask;        ///< Page mask for aliasing
    uint32_t mem_alias_pagemask_active; ///< Active alias mask (A20 dependent)
    uint32_t address_bits;              ///< Address bus width
    uint32_t hw_next_assign;            ///< Next hardware assignment address
    uint8_t a20_enabled;                ///< A20 gate enabled
    uint8_t a20_controlport;            ///< A20 control port value
    uint8_t _pad[6];
};
static_assert(sizeof(EngineStateMemory) == 72, "EngineStateMemory must be 72 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// Total Size Calculation
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Total size needed for engine state.
 */
constexpr size_t ENGINE_STATE_SIZE =
    sizeof(EngineStateHeader) +
    sizeof(EngineStateTiming) +
    sizeof(EngineStatePic) +
    sizeof(EngineStateKeyboard) +
    sizeof(EngineStateCpu) +
    sizeof(EngineStateMemory);

static_assert(ENGINE_STATE_SIZE == 544, "ENGINE_STATE_SIZE should be 544 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// CRC32 Helper
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Compute CRC32 checksum.
 *
 * Uses standard CRC32 polynomial 0xEDB88320.
 *
 * @param data Data buffer
 * @param size Size in bytes
 * @return CRC32 checksum
 */
uint32_t compute_crc32(const void* data, size_t size);

} // namespace dosbox

#endif // DOSBOX_ENGINE_STATE_H
