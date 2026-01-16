/**
 * @file engine_state.h
 * @brief Engine state serialization format for save/load.
 *
 * Defines the binary format used by dosbox_lib_save_state() and
 * dosbox_lib_load_state() to serialize the DOSBoxContext state.
 *
 * Format version 1 includes:
 * - Header with magic, version, checksums
 * - Timing state
 * - PIC state (interrupt controller)
 * - Keyboard state (essential fields only)
 *
 * Note: This serializes only the determinism-critical state.
 * VGA/Mixer state is mostly configuration and less critical for replay.
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
constexpr uint32_t ENGINE_STATE_VERSION = 1;

// ═══════════════════════════════════════════════════════════════════════════════
// Engine State Header
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Header for serialized engine state.
 *
 * Fixed at 32 bytes for alignment. Contains magic number,
 * version, total size, and checksum.
 */
struct EngineStateHeader {
    uint32_t magic;              ///< ENGINE_STATE_MAGIC
    uint32_t version;            ///< ENGINE_STATE_VERSION
    uint32_t total_size;         ///< Total size including header
    uint32_t checksum;           ///< CRC32 of data after header
    uint32_t timing_offset;      ///< Offset to EngineStateTiming
    uint32_t pic_offset;         ///< Offset to EngineStatePic
    uint32_t keyboard_offset;    ///< Offset to EngineStateKeyboard
    uint32_t _reserved;          ///< Reserved for future use
};
static_assert(sizeof(EngineStateHeader) == 32, "EngineStateHeader must be 32 bytes");

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
 * Only essential fields for determinism.
 */
struct EngineStateKeyboard {
    uint8_t scanset;             ///< Current scan code set
    uint8_t enabled;             ///< Keyboard enabled
    uint8_t active;              ///< Keyboard active
    uint8_t command;             ///< Last command
    uint8_t p60data;             ///< Port 0x60 data
    uint8_t p60changed;          ///< Port 0x60 changed
    uint8_t scanning;            ///< Scanning enabled
    uint8_t scheduled;           ///< Event scheduled
    uint32_t buffer_used;        ///< Bytes in keyboard buffer
    uint32_t buffer_pos;         ///< Buffer read position
    uint32_t led_state;          ///< LED state
    uint8_t num_lock;            ///< Num lock
    uint8_t caps_lock;           ///< Caps lock
    uint8_t scroll_lock;         ///< Scroll lock
    uint8_t cb_xlat;             ///< Scancode translation
};
static_assert(sizeof(EngineStateKeyboard) == 24, "EngineStateKeyboard must be 24 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// Total Size Calculation
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Calculate total size needed for engine state.
 */
constexpr size_t ENGINE_STATE_SIZE =
    sizeof(EngineStateHeader) +
    sizeof(EngineStateTiming) +
    sizeof(EngineStatePic) +
    sizeof(EngineStateKeyboard);

static_assert(ENGINE_STATE_SIZE == 120, "ENGINE_STATE_SIZE should be 120 bytes");

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
