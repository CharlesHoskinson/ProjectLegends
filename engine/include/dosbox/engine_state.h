/**
 * @file engine_state.h
 * @brief Engine state serialization format for save/load.
 *
 * Defines the binary format used by dosbox_lib_save_state() and
 * dosbox_lib_load_state() to serialize the DOSBoxContext state.
 *
 * Format version 4 includes:
 * - Header with magic, version, checksums
 * - Timing state
 * - PIC state with full controller registers [V4]
 * - Keyboard state (full 96-entry buffer) [V3]
 * - CPU state (cycle counters, NMI, halt) [V2]
 * - Memory state (page config, A20 gate, LFB) [V2]
 * - Mixer state (audio config) [V4]
 * - VGA state (display config) [V4]
 * - DOS state (kernel config) [V4]
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
/// V5: CPU GPR serialization (REQ-SR-002)
constexpr uint32_t ENGINE_STATE_VERSION = 5;

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
    uint32_t mixer_offset;       ///< Offset to EngineStateMixer [V4]
    uint32_t vga_offset;         ///< Offset to EngineStateVga [V4]
    uint32_t dos_offset;         ///< Offset to EngineStateDos [V4]
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
 * @brief Serialized PIC controller state (one per 8259A chip).
 *
 * All 18 fields from PicController, packed for wire format.
 * V4: replaces the abbreviated V3 PIC format.
 */
struct EngineStatePicController {
    uint32_t icw_words;          ///< ICW words expected
    uint32_t icw_index;          ///< Current ICW index
    uint8_t  special;            ///< Special mask mode
    uint8_t  auto_eoi;           ///< Automatic EOI
    uint8_t  rotate_on_auto_eoi; ///< Rotate on auto EOI
    uint8_t  single;             ///< Single PIC mode
    uint8_t  request_issr;       ///< Reading ISR vs IRR
    uint8_t  vector_base;        ///< Base interrupt vector
    uint8_t  input;              ///< Input signal state
    uint8_t  edge;               ///< Edge trigger mask
    uint8_t  irr;                ///< Interrupt Request Register
    uint8_t  imr;                ///< Interrupt Mask Register
    uint8_t  imrr;               ///< IMR reversed
    uint8_t  isr;                ///< In-Service Register
    uint8_t  isrr;               ///< ISR reversed
    uint8_t  isr_ignore;         ///< ISR ignore mask
    uint8_t  active_irq;         ///< Active IRQ (8 = none)
    uint8_t  controller_index;   ///< 0 = master, 1 = slave
};
static_assert(sizeof(EngineStatePicController) == 24, "EngineStatePicController must be 24 bytes");

/**
 * @brief Serialized PIC (interrupt controller) state.
 *
 * V4: includes full controller state for both master and slave.
 * V3 backward compat: old 24-byte format loaded via EngineStatePicV3.
 */
struct EngineStatePic {
    uint64_t ticks;              ///< PIC tick counter
    uint32_t irq_check;          ///< Pending IRQ bitmap
    uint32_t irq_check_pending;  ///< Deferred IRQ check
    int8_t   master_cascade_irq; ///< Cascade IRQ line (usually 2)
    uint8_t  in_event_service;   ///< Currently servicing event
    uint8_t  enable_slave_pic;   ///< Slave PIC enabled
    uint8_t  _pad[5];           ///< Align controllers to 8-byte boundary
    EngineStatePicController controllers[2]; ///< Full controller state [V4]
};
static_assert(sizeof(EngineStatePic) == 72, "EngineStatePic must be 72 bytes");

/**
 * @brief V3 PIC format for backward compatibility loading.
 */
struct EngineStatePicV3 {
    uint64_t ticks;
    uint32_t irq_check;
    uint32_t irq_check_pending;
    int8_t   master_cascade_irq;
    uint8_t  master_imr;
    uint8_t  slave_imr;
    uint8_t  master_isr;
    uint8_t  slave_isr;
    uint8_t  auto_eoi;
    uint8_t  in_event_service;
    uint8_t  _pad;
};
static_assert(sizeof(EngineStatePicV3) == 24, "EngineStatePicV3 must be 24 bytes");

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

    // CPU General Purpose Registers (REQ-SR-002)
    uint32_t reg_eax = 0;
    uint32_t reg_ecx = 0;
    uint32_t reg_edx = 0;
    uint32_t reg_ebx = 0;
    uint32_t reg_esp = 0;
    uint32_t reg_ebp = 0;
    uint32_t reg_esi = 0;
    uint32_t reg_edi = 0;
    uint32_t reg_eip = 0;
    uint32_t reg_eflags = 0;

    // Segment Registers
    uint16_t seg_cs = 0;
    uint16_t seg_ds = 0;
    uint16_t seg_es = 0;
    uint16_t seg_fs = 0;
    uint16_t seg_gs = 0;
    uint16_t seg_ss = 0;

    uint8_t _pad[10];
};
static_assert(sizeof(EngineStateCpu) == 152, "EngineStateCpu must be 152 bytes");

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
// Mixer State Section [V4]
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized mixer/audio state.
 *
 * Corresponds to DOSBoxContext::mixer (MixerState).
 * Captures determinism-relevant audio configuration.
 */
struct EngineStateMixer {
    uint32_t freq;               ///< Sample rate in Hz
    uint32_t blocksize;          ///< SDL audio block size
    float    master_vol[2];      ///< Master volume L/R
    float    record_vol[2];      ///< Recording volume L/R
    uint32_t samples;            ///< Prebuffer samples
    uint8_t  enabled;            ///< Mixer enabled
    uint8_t  nosound;            ///< No sound mode
    uint8_t  swapstereo;         ///< Swap L/R
    uint8_t  mute;               ///< Muted
    uint8_t  sampleaccurate;     ///< Sample-accurate mixing
    uint8_t  _pad[3];
};
static_assert(sizeof(EngineStateMixer) == 36, "EngineStateMixer must be 36 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// VGA State Section [V4]
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized VGA display configuration state.
 *
 * Corresponds to DOSBoxContext::vga (VgaState).
 * Captures display mode and determinism-relevant config flags.
 * Excludes the ~20KB VGA_Type hardware state.
 */
struct EngineStateVga {
    uint16_t width;              ///< Display width
    uint16_t height;             ///< Display height
    uint8_t  bpp;                ///< Bits per pixel
    uint8_t  mode;               ///< VgaMode enum
    uint8_t  svga_chip;          ///< SvgaChip enum
    uint8_t  render_on_demand;   ///< On-demand rendering
    double   refresh_rate;       ///< Refresh rate Hz
    uint32_t frame_counter;      ///< Total frames rendered
    uint8_t  dac_8bit;           ///< 8-bit DAC
    uint8_t  vbe_enabled;        ///< VESA extensions
    uint8_t  text_mode;          ///< In text mode
    uint8_t  cga_snow;           ///< CGA snow effect
    uint8_t  vesa_flags;         ///< Packed: 32/24/16/15/8/4bpp + lowres + hd
    uint8_t  _pad[7];           ///< Align to 8-byte boundary (for double)
};
static_assert(sizeof(EngineStateVga) == 32, "EngineStateVga must be 32 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// DOS State Section [V4]
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized DOS kernel state.
 *
 * Corresponds to DOSBoxContext::dos (DosState).
 */
struct EngineStateDos {
    uint16_t psp_segment;        ///< Current PSP segment
    uint16_t dta_segment;        ///< DTA segment
    uint16_t dta_offset;         ///< DTA offset
    uint8_t  version_major;      ///< DOS version major
    uint8_t  version_minor;      ///< DOS version minor
    uint8_t  current_drive;      ///< Active drive (0=A)
    uint8_t  verify;             ///< Verify flag
    uint8_t  return_code;        ///< ERRORLEVEL
    uint8_t  return_mode;        ///< Return mode
    uint16_t country;            ///< Country code
    uint16_t codepage;           ///< Code page
    uint8_t  kernel_disabled;    ///< Kernel disabled
    uint8_t  kernel_running;     ///< Kernel running
    uint8_t  _pad[2];
};
static_assert(sizeof(EngineStateDos) == 20, "EngineStateDos must be 20 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// CPU GPR State Section [V5] (REQ-SR-002)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief V5 extension header, appended after V4 data at offset ENGINE_STATE_SIZE_V4.
 *
 * V4 loaders reject V5 data via version check. V5 loaders read V4 data
 * normally, then read this extension header at offset 736.
 */
struct EngineStateV5ExtHeader {
    uint32_t ext_magic;          ///< ENGINE_STATE_V5_EXT_MAGIC
    uint32_t ext_size;           ///< Total extension size (header + payload)
};
static_assert(sizeof(EngineStateV5ExtHeader) == 8, "EngineStateV5ExtHeader must be 8 bytes");

/// V5 extension magic: "V5EX" in little-endian
constexpr uint32_t ENGINE_STATE_V5_EXT_MAGIC = 0x58455635;

/**
 * @brief Serialized CPU general-purpose register state.
 *
 * Captures the full x86 register file: 8 GPRs, EIP, EFLAGS,
 * and 6 segment registers (val/phys/limit) for ES, CS, SS, DS, FS, GS.
 * Stored as fixed-width uint32_t/uint16_t for cross-platform portability.
 */
struct EngineStateCpuGpr {
    uint32_t gpr[8];             ///< EAX(0), ECX(1), EDX(2), EBX(3), ESP(4), EBP(5), ESI(6), EDI(7)
    uint32_t eip;                ///< Instruction pointer
    uint32_t eflags;             ///< Flags register
    uint16_t seg_val[6];         ///< Segment selectors: ES(0), CS(1), SS(2), DS(3), FS(4), GS(5)
    uint16_t _pad1;              ///< Alignment padding
    uint16_t _pad2;              ///< Alignment padding
    uint32_t seg_phys[6];        ///< Segment physical bases
    uint32_t seg_limit[6];       ///< Segment limits
};
static_assert(sizeof(EngineStateCpuGpr) == 104, "EngineStateCpuGpr must be 104 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// V5 Sub-Block Directory [Phase 3: RAM + VGA Serialization]
// ═══════════════════════════════════════════════════════════════════════════════

/// Sub-block directory magic: "V5BD" in little-endian
constexpr uint32_t V5_DIR_MAGIC = 0x44423556;

/// Sub-block tags for the V5 directory
constexpr uint16_t V5_SUBTAG_RAM     = 2;  ///< Guest RAM contents (zero-RLE compressed)
constexpr uint16_t V5_SUBTAG_VGA_REG = 3;  ///< VGA hardware registers (flat struct)
constexpr uint16_t V5_SUBTAG_VRAM    = 4;  ///< VGA VRAM contents (zero-RLE compressed)

/// Flags for V5DirEntry
constexpr uint16_t V5_BLOCK_FLAG_COMPRESSED = 0x0001;  ///< Block is zero-RLE compressed

/**
 * @brief V5 sub-block directory header, placed at offset 848 (after CpuGpr).
 *
 * Contains magic and entry count. Unknown tags are skipped via offset+size.
 */
struct V5SubBlockDir {
    uint32_t dir_magic;    ///< V5_DIR_MAGIC
    uint16_t entry_count;  ///< Number of V5DirEntry records following
    uint16_t _pad;
};
static_assert(sizeof(V5SubBlockDir) == 8, "V5SubBlockDir must be 8 bytes");

/**
 * @brief Single entry in the V5 sub-block directory.
 *
 * Points to a data blob at a given offset with known size.
 * Unknown tags can be skipped by advancing offset+size.
 */
struct V5DirEntry {
    uint16_t tag;          ///< V5_SUBTAG_* identifier
    uint16_t flags;        ///< V5_BLOCK_FLAG_* flags
    uint32_t offset;       ///< Byte offset from start of state buffer
    uint32_t size;         ///< Compressed/stored size in bytes
    uint32_t orig_size;    ///< Original uncompressed size in bytes
};
static_assert(sizeof(V5DirEntry) == 16, "V5DirEntry must be 16 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// VGA Hardware Register State [Phase 3] (REQ-SR-003)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Serialized VGA hardware register state.
 *
 * Captures the full VGA register file: sequencer, attribute controller,
 * CRTC, graphics controller, DAC (palette + translation tables), latch,
 * VGA config subset, SVGA bank state, and memory metadata.
 *
 * All platform-dependent Bitu fields are stored as fixed-width uint32_t.
 * Stored uncompressed in the V5 sub-block directory.
 *
 * After loading, call VGA_DetermineMode() + VGA_SetupHandlers() to
 * recompute derived rendering state.
 */
struct EngineStateVgaRegisters {
    // ── Misc output register (3C2h/3CCh) ────────────────────────────────
    uint8_t misc_output;           ///< Miscellaneous output register
    uint8_t internal_attrindex;    ///< VGA_Internal::attrindex
    uint8_t _pad0[2];

    // ── Sequencer (VGA_Seq: 6 registers) ────────────────────────────────
    uint8_t seq_index;
    uint8_t seq_reset;
    uint8_t seq_clocking_mode;
    uint8_t seq_map_mask;
    uint8_t seq_character_map_select;
    uint8_t seq_memory_mode;
    uint8_t _pad_seq[2];

    // ── Attribute controller (VGA_Attr: 23 bytes) ───────────────────────
    uint8_t attr_palette[16];
    uint8_t attr_mode_control;
    uint8_t attr_horizontal_pel_panning;
    uint8_t attr_overscan_color;
    uint8_t attr_color_plane_enable;
    uint8_t attr_color_select;
    uint8_t attr_index;
    uint8_t attr_disabled;
    uint8_t _pad_attr;

    // ── CRTC (VGA_Crtc: 25 named registers + index + read_only) ────────
    uint8_t crtc_horizontal_total;
    uint8_t crtc_horizontal_display_end;
    uint8_t crtc_start_horizontal_blanking;
    uint8_t crtc_end_horizontal_blanking;
    uint8_t crtc_start_horizontal_retrace;
    uint8_t crtc_end_horizontal_retrace;
    uint8_t crtc_vertical_total;
    uint8_t crtc_overflow;
    uint8_t crtc_preset_row_scan;
    uint8_t crtc_maximum_scan_line;
    uint8_t crtc_cursor_start;
    uint8_t crtc_cursor_end;
    uint8_t crtc_start_address_high;
    uint8_t crtc_start_address_low;
    uint8_t crtc_cursor_location_high;
    uint8_t crtc_cursor_location_low;
    uint8_t crtc_vertical_retrace_start;
    uint8_t crtc_vertical_retrace_end;
    uint8_t crtc_vertical_display_end;
    uint8_t crtc_offset;
    uint8_t crtc_underline_location;
    uint8_t crtc_start_vertical_blanking;
    uint8_t crtc_end_vertical_blanking;
    uint8_t crtc_mode_control;
    uint8_t crtc_line_compare;
    uint8_t crtc_index;
    uint8_t crtc_read_only;
    uint8_t _pad_crtc;

    // ── Graphics controller (VGA_Gfx: 10 registers) ────────────────────
    uint8_t gfx_index;
    uint8_t gfx_set_reset;
    uint8_t gfx_enable_set_reset;
    uint8_t gfx_color_compare;
    uint8_t gfx_data_rotate;
    uint8_t gfx_read_map_select;
    uint8_t gfx_mode;
    uint8_t gfx_miscellaneous;
    uint8_t gfx_color_dont_care;
    uint8_t gfx_bit_mask;
    uint8_t _pad_gfx[2];

    // ── DAC (VGA_Dac) ───────────────────────────────────────────────────
    uint8_t  dac_bits;
    uint8_t  dac_pel_mask;
    uint8_t  dac_pel_index;
    uint8_t  dac_state;
    uint8_t  dac_write_index;
    uint8_t  dac_read_index;
    uint8_t  dac_hidac_counter;
    uint8_t  dac_reg02;
    uint32_t dac_first_changed;    ///< Bitu → uint32_t
    uint8_t  dac_combine[16];
    uint8_t  dac_rgb[768];         ///< RGBEntry[256] as R,G,B triplets
    uint16_t dac_xlat16[256];      ///< 16-bit translation table
    uint32_t dac_xlat32[256];      ///< 32-bit translation table

    // ── VGA latch ───────────────────────────────────────────────────────
    uint32_t latch;

    // ── VGA_Config (display-critical fields, Bitu → uint32_t) ──────────
    uint32_t config_display_start;
    uint32_t config_real_start;
    uint32_t config_scan_len;
    uint32_t config_cursor_start;
    uint32_t config_line_compare;
    uint32_t config_full_bit_mask;
    uint32_t config_full_map_mask;
    uint32_t config_full_not_map_mask;
    uint32_t config_full_set_reset;
    uint32_t config_full_not_enable_set_reset;
    uint32_t config_full_enable_set_reset;
    uint32_t config_full_enable_and_set_reset;
    uint8_t  config_retrace;
    uint8_t  config_chained;
    uint8_t  config_compatible_chain4;
    uint8_t  config_pel_panning;
    uint8_t  config_hlines_skip;
    uint8_t  config_bytes_skip;
    uint8_t  config_addr_shift;
    uint8_t  config_read_mode;
    uint8_t  config_write_mode;
    uint8_t  config_read_map_select;
    uint8_t  config_color_dont_care;
    uint8_t  config_color_compare;
    uint8_t  config_data_rotate;
    uint8_t  config_raster_op;
    uint8_t  _pad_config[2];

    // ── SVGA bank state (VGA_SVGA, Bitu → uint32_t) ────────────────────
    uint32_t svga_read_start;
    uint32_t svga_write_start;
    uint32_t svga_bank_mask_full;  ///< bankMask (Bitu → uint32_t)
    uint32_t svga_bank_read_full;
    uint32_t svga_bank_write_full;
    uint8_t  svga_bank_read;
    uint8_t  svga_bank_write;
    uint16_t svga_bank_mask;
    uint32_t svga_bank_size;

    // ── VGA memory metadata (not VRAM data) ─────────────────────────────
    uint32_t mem_memsize;
    uint32_t mem_memmask;
    uint32_t mem_memmask_crtc;
    uint32_t mem_memsize_original;
    uint32_t mem_vbe_memsize;

    // ── End padding ─────────────────────────────────────────────────────
    uint8_t  _pad_end[4];
};
static_assert(sizeof(EngineStateVgaRegisters) == 2528,
    "EngineStateVgaRegisters must be 2528 bytes");

// ═══════════════════════════════════════════════════════════════════════════════
// Total Size Calculation
// ═══════════════════════════════════════════════════════════════════════════════

/// V3 size for backward compat (5 sections, old 24-byte PIC)
constexpr size_t ENGINE_STATE_SIZE_V3 =
    sizeof(EngineStateHeader) +
    sizeof(EngineStateTiming) +
    sizeof(EngineStatePicV3) +
    sizeof(EngineStateKeyboard) +
    sizeof(EngineStateCpu) +
    sizeof(EngineStateMemory);

static_assert(ENGINE_STATE_SIZE_V3 == 600, "V3 size must be 600 bytes");

/**
 * @brief Total size for V4 engine state (backward compat baseline).
 */
constexpr size_t ENGINE_STATE_SIZE_V4 =
    sizeof(EngineStateHeader) +
    sizeof(EngineStateTiming) +
    sizeof(EngineStatePic) +
    sizeof(EngineStateKeyboard) +
    sizeof(EngineStateCpu) +
    sizeof(EngineStateMemory) +
    sizeof(EngineStateMixer) +
    sizeof(EngineStateVga) +
    sizeof(EngineStateDos);

static_assert(ENGINE_STATE_SIZE_V4 == 736, "ENGINE_STATE_SIZE_V4 must be 736 bytes");

/**
 * @brief Minimum V5 state size (V4 + GPR extension, no sub-block blobs).
 *
 * Old V5 states without RAM/VGA blobs are exactly this size.
 * With Phase 3 blobs, actual size is dynamic (queried via nullptr call).
 */
constexpr size_t ENGINE_STATE_SIZE_V5_BASE =
    ENGINE_STATE_SIZE_V4 +
    sizeof(EngineStateV5ExtHeader) +
    sizeof(EngineStateCpuGpr);

static_assert(ENGINE_STATE_SIZE_V5_BASE == 848, "ENGINE_STATE_SIZE_V5_BASE must be 848 bytes");

/// @deprecated Use ENGINE_STATE_SIZE_V5_BASE for compile-time minimum.
/// Actual V5 size is dynamic — query via dosbox_lib_save_state(nullptr).
constexpr size_t ENGINE_STATE_SIZE = ENGINE_STATE_SIZE_V5_BASE;

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
