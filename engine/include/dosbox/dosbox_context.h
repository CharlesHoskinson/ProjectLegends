/**
 * @file dosbox_context.h
 * @brief Master DOSBox context for library mode.
 *
 * Implements PR #9 requirements:
 * - Master context struct with subsystem state structs
 * - Thread-local current_context() for transitional access
 * - Integration with InstanceRegistry (PR #8)
 *
 * This provides a bridge between the library-mode handle system and
 * the internal aibox::MachineContext implementation.
 *
 * Usage:
 *   // Create via handle system
 *   auto handle = dosbox::create_instance(config);
 *
 *   // Get context from handle
 *   auto* ctx = dosbox::get_context(handle);
 *
 *   // Or use current_context() in transitional code
 *   dosbox::ContextGuard guard(handle);
 *   auto& ctx = dosbox::current_context();
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_DOSBOX_CONTEXT_H
#define DOSBOX_DOSBOX_CONTEXT_H

#include "dosbox/error_model.h"
#include "dosbox/instance_handle.h"
#include "dosbox/platform/timing.h"
#include "dosbox/platform/display.h"
#include "dosbox/platform/audio.h"
#include "dosbox/platform/headless.h"

#include <cstdint>
#include <memory>

#ifdef __cplusplus
extern "C" {
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C API - Context Management
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Configuration for DOSBox instance creation.
 */
typedef struct dosbox_config {
    /** Memory size in bytes (default 16MB) */
    size_t memory_size;

    /** CPU cycles per millisecond (default 3000) */
    uint32_t cpu_cycles;

    /** Enable deterministic mode for testing */
    int deterministic;

    /** Enable sound subsystem */
    int sound_enabled;

    /** Enable debug features */
    int debug_mode;
} dosbox_config;

/**
 * @brief Initialize config with default values.
 */
void dosbox_config_init(dosbox_config* config);

/**
 * @brief Create a new DOSBox instance.
 *
 * @param config Configuration (NULL for defaults)
 * @return Handle to instance, or NULL on failure
 */
dosbox_handle_t dosbox_create(const dosbox_config* config);

/**
 * @brief Initialize a created instance.
 *
 * Must be called before step/run.
 *
 * @param handle Instance handle
 * @return DOSBOX_OK on success, error code on failure
 */
int dosbox_init(dosbox_handle_t handle);

/**
 * @brief Execute emulation for specified duration.
 *
 * @param handle Instance handle
 * @param ms Milliseconds of emulated time
 * @return DOSBOX_OK on success, error code on failure
 */
int dosbox_step(dosbox_handle_t handle, uint32_t ms);

/**
 * @brief Pause execution.
 *
 * @param handle Instance handle
 * @return DOSBOX_OK on success, error code on failure
 */
int dosbox_pause(dosbox_handle_t handle);

/**
 * @brief Resume paused execution.
 *
 * @param handle Instance handle
 * @return DOSBOX_OK on success, error code on failure
 */
int dosbox_resume(dosbox_handle_t handle);

/**
 * @brief Shutdown instance (prepare for destroy).
 *
 * @param handle Instance handle
 * @return DOSBOX_OK on success, error code on failure
 */
int dosbox_shutdown(dosbox_handle_t handle);

/**
 * @brief Destroy instance and release resources.
 *
 * @param handle Instance handle
 * @return DOSBOX_OK on success, error code on failure
 */
int dosbox_destroy(dosbox_handle_t handle);

/**
 * @brief Reset instance to initial state.
 *
 * @param handle Instance handle
 * @return DOSBOX_OK on success, error code on failure
 */
int dosbox_reset(dosbox_handle_t handle);

#ifdef __cplusplus
} /* extern "C" */
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C++ API
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef __cplusplus

#include <atomic>
#include <optional>
#include <string>

namespace dosbox {

// Forward declarations
class DOSBoxContext;
class HashBuilder;  // from state_hash.h

// ─────────────────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Configuration for DOSBox instance (C++ wrapper).
 */
struct ContextConfig {
    size_t memory_size = 16 * 1024 * 1024;  ///< Guest RAM (default 16MB)
    uint32_t cpu_cycles = 3000;              ///< Cycles per millisecond
    bool deterministic = false;              ///< Deterministic mode for testing
    bool sound_enabled = true;               ///< Enable sound subsystem
    bool debug_mode = false;                 ///< Enable debug features

    /**
     * @brief Create minimal configuration for testing.
     */
    [[nodiscard]] static ContextConfig minimal() noexcept {
        ContextConfig config;
        config.memory_size = 1024 * 1024;    // 1MB
        config.sound_enabled = false;
        config.deterministic = true;
        return config;
    }

    /**
     * @brief Create default configuration.
     */
    [[nodiscard]] static ContextConfig defaults() noexcept {
        return ContextConfig{};
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Subsystem State Stubs
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Timing subsystem state.
 *
 * Holds migrated timing globals from src/dosbox.cpp.
 * These control the emulation timing and auto-cycle adjustment.
 *
 * Migration status: PR #10
 * Original globals: ticksDone, ticksScheduled, ticksLast, etc.
 */
struct TimingState {
    // ─────────────────────────────────────────────────────────────────────────
    // Core Timing Counters
    // ─────────────────────────────────────────────────────────────────────────

    uint64_t total_cycles = 0;       ///< Total CPU cycles executed (all time)
    uint32_t virtual_ticks_ms = 0;   ///< Emulated milliseconds since init

    // ─────────────────────────────────────────────────────────────────────────
    // Frame Timing (from dosbox.cpp)
    // ─────────────────────────────────────────────────────────────────────────

    int32_t ticks_done = 0;          ///< Ticks completed this frame
    uint32_t ticks_scheduled = 0;    ///< Ticks scheduled this frame
    uint32_t ticks_remain = 0;       ///< Remaining ticks for current step
    uint32_t ticks_added = 0;        ///< Ticks added this cycle

    // ─────────────────────────────────────────────────────────────────────────
    // Wall-Clock Tracking (determinism: use virtual time instead)
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t ticks_last = 0;         ///< Last GetTicks() value
    uint32_t ticks_last_frame = 0;   ///< Tick at last frame counter update
    uint32_t ticks_last_rt = 0;      ///< Tick at last RT counter update
    double   ticks_last_rt_time = 0; ///< PIC time at last RT update

    // ─────────────────────────────────────────────────────────────────────────
    // SDL Timing (for periodic logging)
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t sdl_ticks_last = 0;     ///< Last SDL tick value
    uint32_t sdl_ticks_next = 0;     ///< Next SDL tick target

    // ─────────────────────────────────────────────────────────────────────────
    // Timing Control
    // ─────────────────────────────────────────────────────────────────────────

    bool locked = false;             ///< Ticks locked (turbo mode)
    uint32_t frame_ticks = 0;        ///< Ticks for current frame

    /**
     * @brief Reset to initial state.
     */
    void reset() noexcept {
        total_cycles = 0;
        virtual_ticks_ms = 0;
        ticks_done = 0;
        ticks_scheduled = 0;
        ticks_remain = 0;
        ticks_added = 0;
        ticks_last = 0;
        ticks_last_frame = 0;
        ticks_last_rt = 0;
        ticks_last_rt_time = 0.0;
        sdl_ticks_last = 0;
        sdl_ticks_next = 0;
        locked = false;
        frame_ticks = 0;
    }

    /**
     * @brief Hash the timing state for determinism verification.
     *
     * Only includes determinism-relevant fields (not wall-clock).
     */
    void hash_into(class HashBuilder& builder) const;
};

/**
 * @brief CPU subsystem state.
 *
 * Holds migrated CPU globals from src/cpu/cpu.cpp.
 * These control cycle counting and CPU execution.
 *
 * Migration status: PR #11
 * Original globals: CPU_Cycles, CPU_CycleMax, CPU_CycleLeft, etc.
 *
 * Note: Full register state is in aibox::CpuContext. This struct
 * holds the cycle management and control state.
 */
struct CpuState {
    // ─────────────────────────────────────────────────────────────────────────
    // Cycle Counters (from cpu.cpp lines 205-214)
    // Type: cpu_cycles_count_t (int64_t)
    // ─────────────────────────────────────────────────────────────────────────

    int64_t cycles = 0;              ///< CPU_Cycles - current cycle counter
    int64_t cycle_left = 3000;       ///< CPU_CycleLeft - remaining in timeslice
    int64_t cycle_max = 3000;        ///< CPU_CycleMax - max cycles per timeslice
    int64_t cycle_old_max = 3000;    ///< CPU_OldCycleMax - previous max
    int64_t cycle_percent_used = 100;///< CPU_CyclePercUsed - percentage used
    int64_t cycle_limit = -1;        ///< CPU_CycleLimit - hard limit (-1 = none)
    int64_t cycle_up = 0;            ///< CPU_CycleUp - upward adjustment
    int64_t cycle_down = 0;          ///< CPU_CycleDown - downward adjustment
    int64_t cycles_set = 3000;       ///< CPU_CyclesSet - configured cycles
    int64_t io_delay_removed = 0;    ///< CPU_IODelayRemoved - IO compensation

    // ─────────────────────────────────────────────────────────────────────────
    // Cycle Auto-Adjustment (from cpu.cpp lines 217-218)
    // ─────────────────────────────────────────────────────────────────────────

    bool cycle_auto_adjust = false;       ///< CPU_CycleAutoAdjust
    bool skip_cycle_auto_adjust = false;  ///< CPU_SkipCycleAutoAdjust

    // ─────────────────────────────────────────────────────────────────────────
    // NMI State (from cpu.cpp lines 75-77)
    // ─────────────────────────────────────────────────────────────────────────

    bool nmi_gate = true;            ///< CPU_NMI_gate - NMI enabled
    bool nmi_active = false;         ///< CPU_NMI_active - NMI in progress
    bool nmi_pending = false;        ///< CPU_NMI_pending - NMI waiting

    // ─────────────────────────────────────────────────────────────────────────
    // CPU Flags and State
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t extflags_toggle = 0;    ///< CPU_extflags_toggle - ID/AC toggles
    bool halted = false;             ///< CPU in HLT state

    /**
     * @brief Reset to initial state.
     */
    void reset() noexcept {
        cycles = 0;
        cycle_left = 3000;
        cycle_max = 3000;
        cycle_old_max = 3000;
        cycle_percent_used = 100;
        cycle_limit = -1;
        cycle_up = 0;
        cycle_down = 0;
        cycles_set = 3000;
        io_delay_removed = 0;
        cycle_auto_adjust = false;
        skip_cycle_auto_adjust = false;
        nmi_gate = true;
        nmi_active = false;
        nmi_pending = false;
        extflags_toggle = 0;
        halted = false;
    }

    /**
     * @brief Hash the CPU state for determinism verification.
     */
    void hash_into(class HashBuilder& builder) const;
};

/**
 * @brief Mixed fraction for sample rate calculations.
 *
 * Used to track fractional samples across frame boundaries
 * without floating-point drift.
 *
 * From mixer.cpp lines 82-85.
 */
struct MixedFraction {
    uint32_t whole = 0;      ///< Whole samples
    uint32_t numerator = 0;  ///< Fractional numerator
    uint32_t denominator = 1;///< Fractional denominator (never 0)

    void reset() noexcept {
        whole = 0;
        numerator = 0;
        denominator = 1;
    }
};

/**
 * @brief Mixer/audio subsystem state.
 *
 * Holds migrated mixer globals from src/hardware/mixer.cpp.
 * Controls audio mixing, sample rate, and buffer management.
 *
 * Migration status: PR #12
 * Original globals: mixer struct (lines 87-105), mixer_sample_counter, etc.
 *
 * ## Thread Safety
 * The audio callback runs on a separate thread and accesses some of these
 * fields. Fields marked [CALLBACK] may be read by the audio callback.
 * The producer/consumer model ensures core writes during step(), callback reads.
 *
 * For now, we document which fields are callback-accessible.
 * Full thread-safe access patterns will be implemented in future PRs.
 */
struct MixerState {
    // ─────────────────────────────────────────────────────────────────────────
    // Core Configuration (from mixer struct, lines 94-95)
    // Set during init, read-only during execution
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t freq = 44100;           ///< Sample rate in Hz [CALLBACK reads]
    uint32_t blocksize = 1024;       ///< SDL audio block size in samples

    // ─────────────────────────────────────────────────────────────────────────
    // Volume Controls (from mixer struct, lines 91-92)
    // ─────────────────────────────────────────────────────────────────────────

    float mastervol[2] = {1.0f, 1.0f};  ///< Master volume (L/R)
    float recordvol[2] = {1.0f, 1.0f};  ///< Recording volume (L/R)

    // ─────────────────────────────────────────────────────────────────────────
    // Ring Buffer State (from mixer struct, lines 89-90)
    // These track the producer/consumer positions in the work buffer.
    // [CALLBACK] marks fields read by audio callback thread.
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t work_in = 0;            ///< Write position (producer) [CALLBACK reads]
    uint32_t work_out = 0;           ///< Read position (consumer) [CALLBACK writes]
    uint32_t work_wrap = 0;          ///< Buffer wrap point
    uint32_t pos = 0;                ///< Current playback position
    uint32_t done = 0;               ///< Samples completed this frame

    // ─────────────────────────────────────────────────────────────────────────
    // Fractional Sample Tracking (from mixer struct, lines 96-98)
    // Used to accurately track samples across frame boundaries.
    // ─────────────────────────────────────────────────────────────────────────

    MixedFraction samples_per_ms;    ///< Samples per millisecond (fractional)
    MixedFraction samples_this_ms;   ///< Samples rendered this ms
    MixedFraction samples_rendered;  ///< Total samples rendered (fractional)

    // ─────────────────────────────────────────────────────────────────────────
    // Configuration Flags (from mixer struct, lines 99-104)
    // ─────────────────────────────────────────────────────────────────────────

    bool enabled = false;            ///< Mixer is enabled (sound_enabled config)
    bool nosound = false;            ///< No sound output mode
    bool swapstereo = false;         ///< Swap L/R channels
    bool sampleaccurate = false;     ///< Sample-accurate mixing mode
    bool prebuffer_wait = false;     ///< Waiting for prebuffer to fill
    bool mute = false;               ///< Output muted

    // ─────────────────────────────────────────────────────────────────────────
    // Prebuffer State (from mixer struct, line 103)
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t prebuffer_samples = 0;  ///< Samples to prebuffer before playback

    // ─────────────────────────────────────────────────────────────────────────
    // Statistics (from mixer.cpp lines 666-667)
    // ─────────────────────────────────────────────────────────────────────────

    uint64_t sample_counter = 0;     ///< Total samples rendered since start
    double start_pic_time = 0.0;     ///< PIC timer value at mixer init

    /**
     * @brief Reset to initial state.
     */
    void reset() noexcept {
        freq = 44100;
        blocksize = 1024;
        mastervol[0] = mastervol[1] = 1.0f;
        recordvol[0] = recordvol[1] = 1.0f;
        work_in = 0;
        work_out = 0;
        work_wrap = 0;
        pos = 0;
        done = 0;
        samples_per_ms.reset();
        samples_this_ms.reset();
        samples_rendered.reset();
        enabled = false;
        nosound = false;
        swapstereo = false;
        sampleaccurate = false;
        prebuffer_wait = false;
        mute = false;
        prebuffer_samples = 0;
        sample_counter = 0;
        start_pic_time = 0.0;
    }

    /**
     * @brief Hash the mixer state for determinism verification.
     *
     * Includes configuration and ring buffer state (determinism-relevant).
     * Excludes start_pic_time (wall-clock dependent).
     */
    void hash_into(class HashBuilder& builder) const;
};

/**
 * @brief VGA display mode enumeration.
 *
 * Represents the current VGA hardware mode type.
 * From vga.h M_* constants.
 */
enum class VgaMode : uint8_t {
    Text = 0,       ///< Text mode (CGA/EGA/VGA text)
    CGA2 = 1,       ///< CGA 2-color graphics (640x200)
    CGA4 = 2,       ///< CGA 4-color graphics (320x200)
    EGA = 3,        ///< EGA 16-color graphics
    VGA = 4,        ///< VGA 256-color graphics (mode 13h)
    LIN4 = 5,       ///< Linear 4-color (planar)
    LIN8 = 6,       ///< Linear 8-bit (256 color)
    LIN15 = 7,      ///< Linear 15-bit (32768 colors)
    LIN16 = 8,      ///< Linear 16-bit (65536 colors)
    LIN24 = 9,      ///< Linear 24-bit (16M colors)
    LIN32 = 10,     ///< Linear 32-bit (16M colors + alpha)
    Herc = 11,      ///< Hercules graphics
    Tandy = 12,     ///< Tandy graphics
    PC98 = 13,      ///< PC-98 graphics mode
    Error = 255     ///< Invalid/error mode
};

/**
 * @brief SVGA chip type enumeration.
 *
 * From vga.h SVGA_* constants.
 */
enum class SvgaChip : uint8_t {
    None = 0,           ///< No SVGA (standard VGA)
    S3Trio = 1,         ///< S3 Trio64
    TsengET4K = 2,      ///< Tseng ET4000
    TsengET3K = 3,      ///< Tseng ET3000
    ParadisePVGA1A = 4, ///< Paradise PVGA1A
    Other = 255         ///< Other/unknown
};

/**
 * @brief VGA/display subsystem state.
 *
 * Holds migrated VGA globals from src/hardware/vga*.cpp.
 * Controls display output, mode configuration, and rendering.
 *
 * Migration status: PR #13
 * Original globals: vga struct, svga driver, rendering flags
 *
 * ## Note on Full VGA State
 * The full VGA hardware state (registers, VRAM, etc.) is very large.
 * This struct captures the determinism-relevant display configuration.
 * Full register state will be migrated incrementally in future PRs.
 */
struct VgaState {
    // ─────────────────────────────────────────────────────────────────────────
    // Display Mode Configuration
    // ─────────────────────────────────────────────────────────────────────────

    uint16_t width = 640;            ///< Display width in pixels
    uint16_t height = 480;           ///< Display height in pixels
    uint8_t bpp = 8;                 ///< Bits per pixel
    VgaMode mode = VgaMode::VGA;     ///< Current VGA mode type
    SvgaChip svga_chip = SvgaChip::None; ///< SVGA chip emulation type

    // ─────────────────────────────────────────────────────────────────────────
    // Timing / Refresh (from vga.cpp, vga_draw.cpp)
    // ─────────────────────────────────────────────────────────────────────────

    double refresh_rate = 70.0;      ///< Refresh rate in Hz (vga_force_refresh_rate)
    double fps = 0.0;                ///< Current frames per second
    uint32_t frame_counter = 0;      ///< Total frames rendered

    // ─────────────────────────────────────────────────────────────────────────
    // Rendering Flags (from vga.cpp lines 193-195)
    // ─────────────────────────────────────────────────────────────────────────

    bool render_on_demand = false;   ///< On-demand rendering (vga_render_on_demand)
    bool render_wait_for_changes = false; ///< Skip render unless changed

    // ─────────────────────────────────────────────────────────────────────────
    // Hardware Configuration Flags
    // ─────────────────────────────────────────────────────────────────────────

    bool dac_8bit = false;           ///< 8-bit DAC enabled (vga_8bit_dac)
    bool pci_enabled = false;        ///< PCI VGA enabled (enable_pci_vga)
    bool vbe_enabled = true;         ///< VESA BIOS Extensions enabled

    // ─────────────────────────────────────────────────────────────────────────
    // VESA/SVGA Mode Capabilities (from vga.cpp lines 251-257)
    // ─────────────────────────────────────────────────────────────────────────

    bool vesa_32bpp = true;          ///< Allow 32bpp VESA modes
    bool vesa_24bpp = true;          ///< Allow 24bpp VESA modes
    bool vesa_16bpp = true;          ///< Allow 16bpp VESA modes
    bool vesa_15bpp = true;          ///< Allow 15bpp VESA modes
    bool vesa_8bpp = true;           ///< Allow 8bpp VESA modes
    bool vesa_4bpp = true;           ///< Allow 4bpp VESA modes
    bool vesa_lowres = true;         ///< Allow low-resolution VESA modes
    bool vesa_hd = false;            ///< Allow HD resolution VESA modes

    // ─────────────────────────────────────────────────────────────────────────
    // Display State Flags
    // ─────────────────────────────────────────────────────────────────────────

    bool text_mode = true;           ///< Currently in text mode
    bool page_flip_occurred = false; ///< Page flip event flag
    bool retrace_poll = false;       ///< Vertical retrace being polled

    // ─────────────────────────────────────────────────────────────────────────
    // CGA/EGA Compatibility
    // ─────────────────────────────────────────────────────────────────────────

    bool cga_snow = false;           ///< CGA snow effect enabled
    bool ega_mode = false;           ///< EGA compatibility mode

    /**
     * @brief Reset to initial state.
     */
    void reset() noexcept {
        width = 640;
        height = 480;
        bpp = 8;
        mode = VgaMode::VGA;
        svga_chip = SvgaChip::None;
        refresh_rate = 70.0;
        fps = 0.0;
        frame_counter = 0;
        render_on_demand = false;
        render_wait_for_changes = false;
        dac_8bit = false;
        pci_enabled = false;
        vbe_enabled = true;
        vesa_32bpp = true;
        vesa_24bpp = true;
        vesa_16bpp = true;
        vesa_15bpp = true;
        vesa_8bpp = true;
        vesa_4bpp = true;
        vesa_lowres = true;
        vesa_hd = false;
        text_mode = true;
        page_flip_occurred = false;
        retrace_poll = false;
        cga_snow = false;
        ega_mode = false;
    }

    /**
     * @brief Hash the VGA state for determinism verification.
     *
     * Includes display mode, configuration, and frame counter.
     * Excludes fps (derived from timing).
     */
    void hash_into(class HashBuilder& builder) const;
};

/**
 * @brief PIC (Programmable Interrupt Controller) state.
 *
 * Holds migrated PIC globals from src/hardware/pic.cpp.
 * Controls interrupt handling and timing events.
 *
 * Migration status: PR #14
 * Original globals: pics, PIC_Ticks, PIC_IRQCheck, etc.
 *
 * ## Note on Full PIC State
 * The full PIC controller state includes ISR, IMR, IRR registers.
 * This struct captures the determinism-relevant control state.
 */
struct PicState {
    // ─────────────────────────────────────────────────────────────────────────
    // Tick Counter (from pic.cpp line 116)
    // ─────────────────────────────────────────────────────────────────────────

    uint64_t ticks = 0;              ///< PIC_Ticks - PIC tick counter

    // ─────────────────────────────────────────────────────────────────────────
    // IRQ State (from pic.cpp lines 117-118)
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t irq_check = 0;          ///< PIC_IRQCheck - pending IRQ bitmap
    uint32_t irq_check_pending = 0;  ///< PIC_IRQCheckPending - deferred IRQ check

    // ─────────────────────────────────────────────────────────────────────────
    // Cascade Configuration (from pic.cpp line 112)
    // ─────────────────────────────────────────────────────────────────────────

    int8_t master_cascade_irq = 2;   ///< IRQ line for slave PIC (usually IRQ2)

    // ─────────────────────────────────────────────────────────────────────────
    // Event Service State (from pic.cpp lines 654-655)
    // ─────────────────────────────────────────────────────────────────────────

    bool in_event_service = false;   ///< Currently servicing PIC event
    double srv_lag = 0.0;            ///< Service lag time (pic_tickindex_t)

    // ─────────────────────────────────────────────────────────────────────────
    // IRQ Timing (from pic.cpp line 37)
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t irq_delay_ns = 0;       ///< IRQ propagation delay in nanoseconds

    // ─────────────────────────────────────────────────────────────────────────
    // Controller State Summary (from pics[] array)
    // Full register state is large; we track key flags here.
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t master_imr = 0xFF;       ///< Master PIC interrupt mask register
    uint8_t slave_imr = 0xFF;        ///< Slave PIC interrupt mask register
    uint8_t master_isr = 0;          ///< Master PIC in-service register
    uint8_t slave_isr = 0;           ///< Slave PIC in-service register
    bool auto_eoi = false;           ///< Auto end-of-interrupt mode

    /**
     * @brief Reset to initial state.
     */
    void reset() noexcept {
        ticks = 0;
        irq_check = 0;
        irq_check_pending = 0;
        master_cascade_irq = 2;
        in_event_service = false;
        srv_lag = 0.0;
        irq_delay_ns = 0;
        master_imr = 0xFF;
        slave_imr = 0xFF;
        master_isr = 0;
        slave_isr = 0;
        auto_eoi = false;
    }

    /**
     * @brief Hash the PIC state for determinism verification.
     */
    void hash_into(class HashBuilder& builder) const;
};

/**
 * @brief Keyboard controller state.
 *
 * Holds migrated keyboard globals from src/hardware/keyboard.cpp.
 * Controls keyboard input handling and scan code translation.
 *
 * Migration status: PR #14
 * Original globals: keyb struct
 */
struct KeyboardState {
    // ─────────────────────────────────────────────────────────────────────────
    // Scan Code State
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t scanset = 2;             ///< Current scan code set (1, 2, or 3)
    bool enabled = true;             ///< Keyboard enabled
    bool active = true;              ///< Keyboard active (not reset)

    // ─────────────────────────────────────────────────────────────────────────
    // Buffer State
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t buffer_size = 0;         ///< Number of bytes in buffer
    uint8_t buffer_pos = 0;          ///< Current buffer read position

    // ─────────────────────────────────────────────────────────────────────────
    // Lock State (modifier keys)
    // ─────────────────────────────────────────────────────────────────────────

    bool num_lock = false;           ///< Num Lock state
    bool caps_lock = false;          ///< Caps Lock state
    bool scroll_lock = false;        ///< Scroll Lock state

    // ─────────────────────────────────────────────────────────────────────────
    // Command State
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t command = 0;             ///< Last command received
    bool expecting_data = false;     ///< Expecting data byte after command

    // ─────────────────────────────────────────────────────────────────────────
    // PS/2 Controller State
    // ─────────────────────────────────────────────────────────────────────────

    bool ps2_mouse_enabled = false;  ///< PS/2 mouse port enabled
    bool a20_gate = true;            ///< A20 gate state

    /**
     * @brief Reset to initial state.
     */
    void reset() noexcept {
        scanset = 2;
        enabled = true;
        active = true;
        buffer_size = 0;
        buffer_pos = 0;
        num_lock = false;
        caps_lock = false;
        scroll_lock = false;
        command = 0;
        expecting_data = false;
        ps2_mouse_enabled = false;
        a20_gate = true;
    }

    /**
     * @brief Hash the keyboard state for determinism verification.
     */
    void hash_into(class HashBuilder& builder) const;
};

/**
 * @brief Input capture state.
 *
 * Tracks host input state that was captured when entering emulation.
 * Used to restore host state when releasing input.
 *
 * Migration status: PR #14
 * Original globals: on_capture_num_lock_was_on, on_capture_caps_lock_was_on
 */
struct InputCaptureState {
    bool captured_num_lock = false;   ///< Num Lock was on when captured
    bool captured_caps_lock = false;  ///< Caps Lock was on when captured
    bool input_captured = false;      ///< Input is currently captured

    void reset() noexcept {
        captured_num_lock = false;
        captured_caps_lock = false;
        input_captured = false;
    }

    void hash_into(class HashBuilder& builder) const;
};

// Forward declarations for memory types (avoid circular includes)
class PageHandler;
using MemHandle = int32_t;

/**
 * @brief Linear framebuffer region configuration.
 *
 * Describes a memory region mapped for video framebuffer access.
 * Used for VGA LFB and MMIO regions.
 */
struct LfbRegion {
    size_t start_page = 0;       ///< Starting page number (Bitu compatible)
    size_t end_page = 0;         ///< Ending page number (exclusive)
    size_t pages = 0;            ///< Number of pages in region
    PageHandler* handler = nullptr; ///< Page handler for this region

    void reset() noexcept {
        start_page = 0;
        end_page = 0;
        pages = 0;
        handler = nullptr;
    }
};

/**
 * @brief A20 gate state.
 *
 * Controls the A20 address line behavior for legacy compatibility.
 * When disabled, addresses wrap at 1MB boundary (8086 compatibility).
 */
struct A20State {
    bool enabled = true;         ///< A20 gate enabled (default: enabled)
    uint8_t controlport = 0;     ///< Control port value (port 92h state)

    void reset() noexcept {
        enabled = true;
        controlport = 0;
    }
};

/**
 * @brief Memory subsystem state.
 *
 * Holds migrated memory globals from src/hardware/memory.cpp.
 * Controls guest RAM allocation, page handling, and A20 gate.
 *
 * Migration status: PR #24 (Sprint 2 Phase 2)
 * Original globals: MemBase, memory struct
 *
 * ## Memory Layout
 * The base pointer points to the allocated guest RAM buffer.
 * Page handlers provide virtualized access to different memory regions.
 * The A20 gate controls address line 20 for 8086 compatibility.
 *
 * ## Ownership
 * - base: Owned, allocated/freed by context
 * - phandlers/mhandles: Not yet migrated (Phase 2 partial)
 *
 * ## Thread Safety
 * Not thread-safe. Use from emulation thread only.
 */
struct MemoryState {
    // ─────────────────────────────────────────────────────────────────────────
    // Core Memory (from memory.cpp lines 261-262)
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t* base = nullptr;     ///< Guest RAM base pointer (replaces MemBase)
    size_t size = 0;             ///< Allocated size in bytes (replaces MemSize)

    // ─────────────────────────────────────────────────────────────────────────
    // Page Configuration (from MemoryBlock struct, lines 216-219)
    // Using size_t (Bitu) for compatibility with existing code
    // ─────────────────────────────────────────────────────────────────────────

    size_t pages = 0;              ///< Total memory pages
    size_t handler_pages = 0;      ///< Number of page handler entries
    size_t reported_pages = 0;     ///< Pages reported to guest
    size_t reported_pages_4gb = 0; ///< Pages reported above 4GB

    // ─────────────────────────────────────────────────────────────────────────
    // Page Handlers and Memory Handles (from MemoryBlock lines 220-221)
    // ─────────────────────────────────────────────────────────────────────────

    PageHandler** phandlers = nullptr;  ///< Per-page handler array
    MemHandle* mhandles = nullptr;      ///< Memory handle array for EMS/XMS

    // ─────────────────────────────────────────────────────────────────────────
    // Linear Framebuffer Regions (from MemoryBlock lines 222-233)
    // ─────────────────────────────────────────────────────────────────────────

    LfbRegion lfb;               ///< VGA linear framebuffer region
    LfbRegion lfb_mmio;          ///< VGA MMIO region

    // ─────────────────────────────────────────────────────────────────────────
    // A20 Gate State (from MemoryBlock lines 234-237)
    // ─────────────────────────────────────────────────────────────────────────

    A20State a20;                ///< A20 gate state

    // ─────────────────────────────────────────────────────────────────────────
    // Address Masking (from MemoryBlock lines 238-241)
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t mem_alias_pagemask = 0;        ///< Page mask for aliasing
    uint32_t mem_alias_pagemask_active = 0; ///< Active alias mask (A20 dependent)
    uint32_t address_bits = 20;              ///< Address bus width (default 20 for 8086)
    uint32_t hw_next_assign = 0;             ///< Next hardware assignment address

    /**
     * @brief Reset to initial state.
     *
     * Does NOT deallocate memory. Use cleanup() for full deallocation.
     */
    void reset() noexcept {
        // Don't reset base/size - those are managed by init/cleanup
        // Don't reset phandlers/mhandles - those are managed separately
        pages = 0;
        handler_pages = 0;
        reported_pages = 0;
        reported_pages_4gb = 0;
        lfb.reset();
        lfb_mmio.reset();
        a20.reset();
        mem_alias_pagemask = 0;
        mem_alias_pagemask_active = 0;
        address_bits = 20;
        hw_next_assign = 0;
    }

    /**
     * @brief Full cleanup including dynamic allocations.
     */
    void cleanup() noexcept {
        if (phandlers) {
            delete[] phandlers;
            phandlers = nullptr;
        }
        if (mhandles) {
            delete[] mhandles;
            mhandles = nullptr;
        }
        if (base) {
            delete[] base;
            base = nullptr;
        }
        size = 0;
        reset();
    }

    /**
     * @brief Hash the memory state for determinism verification.
     *
     * Includes configuration and A20 state (determinism-relevant).
     * Excludes raw memory content (too large, use Full mode for content).
     */
    void hash_into(class HashBuilder& builder) const;
};

// ─────────────────────────────────────────────────────────────────────────────
// DOSBox Context
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Master DOSBox context for library mode.
 *
 * This is the central state container for a DOSBox instance.
 * All mutable emulator state will eventually live here, organized
 * by subsystem.
 *
 * ## Subsystem State
 * State is organized into subsystem structs:
 * - timing: Cycle counts, virtual ticks
 * - cpu: CPU registers and mode (stub, full impl in aibox::CpuContext)
 * - mixer: Audio subsystem
 * - vga: Display subsystem
 * - pic: Programmable Interrupt Controller
 * - keyboard: Keyboard controller
 * - input: Input capture state
 *
 * ## Lifecycle
 * Managed by InstanceRegistry (PR #8):
 * 1. Create: allocate in registry, construct context
 * 2. Initialize: init subsystems
 * 3. Run: step execution
 * 4. Shutdown: cleanup
 * 5. Destroy: free from registry
 *
 * ## Thread Safety
 * Not thread-safe. Use from emulation thread only.
 * Exception: request_stop() is atomic.
 */
class DOSBoxContext {
public:
    /**
     * @brief Construct with configuration.
     */
    explicit DOSBoxContext(const ContextConfig& config = ContextConfig::defaults());

    /**
     * @brief Destructor.
     */
    ~DOSBoxContext();

    // Non-copyable
    DOSBoxContext(const DOSBoxContext&) = delete;
    DOSBoxContext& operator=(const DOSBoxContext&) = delete;

    // Movable
    DOSBoxContext(DOSBoxContext&& other) noexcept;
    DOSBoxContext& operator=(DOSBoxContext&& other) noexcept;

    // ─────────────────────────────────────────────────────────────────────────
    // Lifecycle Operations
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Initialize all subsystems.
     */
    [[nodiscard]] Result<void> initialize();

    /**
     * @brief Execute emulation for specified duration.
     */
    [[nodiscard]] Result<uint32_t> step(uint32_t ms);

    /**
     * @brief Pause execution.
     */
    [[nodiscard]] Result<void> pause();

    /**
     * @brief Resume execution.
     */
    [[nodiscard]] Result<void> resume();

    /**
     * @brief Shutdown all subsystems.
     */
    void shutdown() noexcept;

    /**
     * @brief Reset to initial state.
     */
    [[nodiscard]] Result<void> reset();

    /**
     * @brief Request stop (thread-safe).
     */
    void request_stop() noexcept;

    // ─────────────────────────────────────────────────────────────────────────
    // Subsystem State (Public for Migration)
    // ─────────────────────────────────────────────────────────────────────────

    /** @brief Timing state */
    TimingState timing;

    /** @brief CPU state stub (for migration tracking) */
    CpuState cpu_state;

    /** @brief Mixer state */
    MixerState mixer;

    /** @brief VGA state */
    VgaState vga;

    /** @brief PIC (interrupt controller) state */
    PicState pic;

    /** @brief Keyboard controller state */
    KeyboardState keyboard;

    /** @brief Input capture state */
    InputCaptureState input;

    /** @brief Memory subsystem state (Sprint 2 Phase 2) */
    MemoryState memory;

    // ─────────────────────────────────────────────────────────────────────────
    // Platform Timing (PR #17)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set the platform timing provider.
     *
     * When set, this context will use the provided timing interface
     * for SDL_GetTicks/SDL_Delay calls when it is the current context.
     *
     * @param timing Timing provider (context does not own)
     */
    void set_timing_provider(platform::ITiming* timing) noexcept;

    /**
     * @brief Get the platform timing provider.
     */
    [[nodiscard]] platform::ITiming* get_timing_provider() const noexcept {
        return timing_provider_;
    }

    /**
     * @brief Get the built-in virtual timing.
     *
     * Use this if you need direct access to the virtual timing,
     * e.g., for advancing time during step().
     */
    [[nodiscard]] platform::VirtualTiming& virtual_timing() noexcept {
        return virtual_timing_;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Platform Display (PR #18)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set the platform display provider.
     *
     * When set, this context will use the provided display interface
     * for GFX_* calls when it is the current context.
     *
     * @param display Display provider (context does not own)
     */
    void set_display_provider(platform::IDisplay* display) noexcept;

    /**
     * @brief Get the platform display provider.
     */
    [[nodiscard]] platform::IDisplay* get_display_provider() const noexcept {
        return display_provider_;
    }

    /**
     * @brief Get the built-in headless display.
     *
     * Use this if you need direct access to the headless display,
     * e.g., for frame capture.
     */
    [[nodiscard]] platform::HeadlessDisplay& headless_display() noexcept {
        return headless_display_;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Platform Input (PR #19)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set the platform input provider.
     *
     * When set, this context will use the provided input interface
     * for event handling when it is the current context.
     *
     * @param input Input provider (context does not own)
     */
    void set_input_provider(platform::IInput* input) noexcept;

    /**
     * @brief Get the platform input provider.
     */
    [[nodiscard]] platform::IInput* get_input_provider() const noexcept {
        return input_provider_;
    }

    /**
     * @brief Get the built-in thread-safe input queue.
     *
     * Use this if you need direct access to the input queue,
     * e.g., for injecting events.
     */
    [[nodiscard]] platform::ThreadSafeInput& thread_safe_input() noexcept {
        return thread_safe_input_;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Platform Audio (PR #20)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set the platform audio provider.
     *
     * When set, this context will use the provided audio interface
     * for sound output when it is the current context.
     *
     * @param audio Audio provider (context does not own)
     */
    void set_audio_provider(platform::IAudio* audio) noexcept;

    /**
     * @brief Get the platform audio provider.
     */
    [[nodiscard]] platform::IAudio* get_audio_provider() const noexcept {
        return audio_provider_;
    }

    /**
     * @brief Get the built-in buffer audio.
     *
     * Use this if you need direct access to the audio buffer,
     * e.g., for capturing audio samples.
     */
    [[nodiscard]] platform::BufferAudio& buffer_audio() noexcept {
        return buffer_audio_;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // State Queries
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get configuration.
     */
    [[nodiscard]] const ContextConfig& config() const noexcept { return config_; }

    /**
     * @brief Check if initialized.
     */
    [[nodiscard]] bool is_initialized() const noexcept { return initialized_; }

    /**
     * @brief Check if stop requested.
     */
    [[nodiscard]] bool stop_requested() const noexcept {
        return stop_requested_.load(std::memory_order_acquire);
    }

    /**
     * @brief Get last error.
     */
    [[nodiscard]] const std::optional<Error>& last_error() const noexcept {
        return last_error_;
    }

private:
    ContextConfig config_;
    bool initialized_ = false;
    std::atomic<bool> stop_requested_{false};
    std::optional<Error> last_error_;

    // Platform timing (PR #17)
    platform::VirtualTiming virtual_timing_;      ///< Built-in deterministic timing
    platform::ITiming* timing_provider_ = nullptr; ///< Custom timing provider (not owned)

    // Platform display (PR #18)
    platform::HeadlessDisplay headless_display_;  ///< Built-in headless display
    platform::IDisplay* display_provider_ = nullptr; ///< Custom display provider (not owned)

    // Platform input (PR #19)
    platform::ThreadSafeInput thread_safe_input_;  ///< Built-in thread-safe input queue
    platform::IInput* input_provider_ = nullptr;   ///< Custom input provider (not owned)

    // Platform audio (PR #20)
    platform::BufferAudio buffer_audio_;           ///< Built-in buffer audio for capture
    platform::IAudio* audio_provider_ = nullptr;   ///< Custom audio provider (not owned)
};

// ─────────────────────────────────────────────────────────────────────────────
// Handle-Based API
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Create a new DOSBox instance.
 *
 * @param config Configuration
 * @return Handle and context, or error
 */
[[nodiscard]] Result<std::pair<InstanceHandle, DOSBoxContext*>>
create_instance(const ContextConfig& config = ContextConfig::defaults());

/**
 * @brief Get context from handle.
 *
 * @param handle Instance handle
 * @return Context pointer, or nullptr if invalid
 */
[[nodiscard]] DOSBoxContext* get_context(InstanceHandle handle);

/**
 * @brief Destroy an instance.
 *
 * @param handle Instance handle
 * @return Ok on success
 */
[[nodiscard]] Result<void> destroy_instance(InstanceHandle handle);

// ─────────────────────────────────────────────────────────────────────────────
// Thread-Local Current Context
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Set the current context for this thread.
 *
 * Used by transitional code that still relies on global context access.
 *
 * @param ctx Context to set (nullptr to clear)
 */
void set_current_context(DOSBoxContext* ctx) noexcept;

/**
 * @brief Get the current context for this thread.
 *
 * @return Reference to current context
 * @pre set_current_context() was called with non-null context
 *
 * @note Asserts in debug build if no context is set.
 */
[[nodiscard]] DOSBoxContext& current_context();

/**
 * @brief Get current context pointer (may be null).
 *
 * Safer than current_context() for code that can handle no context.
 */
[[nodiscard]] DOSBoxContext* current_context_ptr() noexcept;

/**
 * @brief Check if a current context is set.
 */
[[nodiscard]] bool has_current_context() noexcept;

// ─────────────────────────────────────────────────────────────────────────────
// Context Guard (RAII)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief RAII guard for setting current context.
 *
 * Sets the current context on construction and restores the previous
 * context on destruction.
 *
 * Usage:
 * @code
 *   {
 *       ContextGuard guard(my_context);
 *       // current_context() returns my_context here
 *       do_stuff();
 *   }
 *   // Previous context restored
 * @endcode
 */
class ContextGuard {
public:
    /**
     * @brief Set context and save previous.
     */
    explicit ContextGuard(DOSBoxContext& ctx) noexcept;

    /**
     * @brief Set context from handle.
     *
     * @param handle Instance handle
     * @throws std::runtime_error if handle is invalid
     */
    explicit ContextGuard(InstanceHandle handle);

    /**
     * @brief Restore previous context.
     */
    ~ContextGuard() noexcept;

    // Non-copyable, non-movable
    ContextGuard(const ContextGuard&) = delete;
    ContextGuard& operator=(const ContextGuard&) = delete;
    ContextGuard(ContextGuard&&) = delete;
    ContextGuard& operator=(ContextGuard&&) = delete;

    /**
     * @brief Check if guard is valid (has context).
     */
    [[nodiscard]] bool valid() const noexcept { return valid_; }

private:
    DOSBoxContext* previous_;
    bool valid_;
};

} // namespace dosbox

#endif /* __cplusplus */

#endif /* DOSBOX_DOSBOX_CONTEXT_H */
