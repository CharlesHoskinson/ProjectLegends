/**
 * @file legends_instance.h
 * @brief Per-instance state container (internal only)
 *
 * Defines struct legends_instance which owns all per-instance state.
 * The public API handle (legends_handle = legends_instance*) points
 * to one of these. Single-instance constraint is enforced via
 * g_active_instance atomic pointer in legends_embed_api.cpp.
 *
 * @warning INTERNAL HEADER - NOT part of the public API.
 */

#ifndef LEGENDS_INTERNAL_LEGENDS_INSTANCE_H
#define LEGENDS_INTERNAL_LEGENDS_INSTANCE_H

#include "instance_state.h"
#include "legends/machine_context.h"
#include <legends/legends_embed.h>

// Forward-declare the DOSBox-X engine handle type to avoid engine include dependency.
// The actual dosbox/dosbox_library.h is only needed by legends_embed_api.cpp.
struct dosbox_lib_instance;
typedef struct dosbox_lib_instance* dosbox_lib_handle_t;

#include <memory>
#include <thread>

/**
 * @brief Per-instance state container.
 *
 * Aggregates all state that was previously file-scope globals in
 * legends_embed_api.cpp. The legends_handle typedef in the public
 * header already declares `typedef struct legends_instance* legends_handle`,
 * so this struct definition makes that opaque pointer real.
 */
struct legends_instance {
    // ── Owner thread (for thread-affinity checks) ──────────────────────────
    std::thread::id owner_thread_id{};

    // ── Reentrancy guard (M1) ────────────────────────────────────────────
    bool in_step{false};

    // ── Configuration ──────────────────────────────────────────────────────
    legends_config_t config{};

    // Deep copies of config strings (M4) — config.config_path and
    // config.working_dir point into these owned buffers.
    std::string config_path_owned;
    std::string working_dir_owned;

    // ── Error state ────────────────────────────────────────────────────────
    std::string last_error;

    // ── Logging ────────────────────────────────────────────────────────────
    legends::internal::LogState log_state;

    // ── Machine context (C++ subsystem container) ──────────────────────────
    std::unique_ptr<legends::MachineContext> machine;

    // ── DOSBox-X engine handle ─────────────────────────────────────────────
    dosbox_lib_handle_t engine_handle{nullptr};

    // ── Time state ─────────────────────────────────────────────────────────
    legends::internal::TimeState time_state;

    // ── Frame state ────────────────────────────────────────────────────────
    legends::internal::FrameState frame_state;

    // ── Input state ────────────────────────────────────────────────────────
    legends::internal::InputState input_state;

    // ── Event queue ────────────────────────────────────────────────────────
    legends::internal::EventQueueState event_queue;

    // ── PIC state (master + slave) ─────────────────────────────────────────
    std::array<legends::internal::PICState, 2> pics = {{
        {0, 255, 0, 8, 2, {0, 0, 0}},    // Master: vector base 8
        {0, 255, 0, 112, 2, {0, 0, 0}}   // Slave: vector base 112
    }};

    // ── DMA state (8 channels) ─────────────────────────────────────────────
    std::array<legends::internal::DMAChannelState, 8> dma{};

    // ── Event callbacks (REQ-API-006) ───────────────────────────────────────
    struct EventCallback {
        legends_event_callback_t fn{nullptr};
        void* userdata{nullptr};
    };
    static constexpr int kMaxEventTypes = 5; // 1-based: indices 1..4
    std::array<EventCallback, kMaxEventTypes> event_callbacks{};

    // Constructor: set hardware-correct defaults that can't be expressed
    // as aggregate initializers (bitfield defaults).
    legends_instance() {
        for (auto& ch : dma) ch.masked = 1;
    }

    /**
     * @brief Reset all mutable state to initial values.
     *
     * Called during legends_reset() to restore deterministic starting state.
     * Does NOT destroy the machine context or engine handle.
     */
    void reset_state() {
        time_state.reset();
        frame_state.reset();
        input_state.reset();
        event_queue.reset();

        pics[0] = {0, 255, 0, 8, 2, {0, 0, 0}};
        pics[1] = {0, 255, 0, 112, 2, {0, 0, 0}};

        for (auto& ch : dma) {
            ch = legends::internal::DMAChannelState{};
            ch.masked = 1;
        }

        last_error.clear();
    }

    /**
     * @brief Full cleanup for destroy.
     *
     * Resets all state including log callback. Called during legends_destroy().
     */
    void destroy_cleanup() {
        reset_state();
        log_state.reset();
        owner_thread_id = std::thread::id{};
    }
};

#endif // LEGENDS_INTERNAL_LEGENDS_INSTANCE_H
