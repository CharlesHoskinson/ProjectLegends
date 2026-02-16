/**
 * @file pic_types.h
 * @brief Shared PIC controller type for context-based architecture.
 *
 * Contains the PicController struct (renamed from PIC_Controller) that
 * is shared between pic.cpp and DOSBoxContext. This enables embedding
 * the full controller state in PicState while preserving the existing
 * code structure.
 *
 * The controller_index member replaces pointer comparisons
 * (e.g., `this == &master`) that existed in the original code.
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_PIC_TYPES_H
#define DOSBOX_PIC_TYPES_H

#include <cstdint>

namespace dosbox {

class HashBuilder;

/**
 * @brief PIC controller state (one per 8259A chip).
 *
 * Mirrors the original PIC_Controller struct from pic.cpp.
 * Two instances exist per PIC subsystem: controllers[0] = master,
 * controllers[1] = slave.
 *
 * The controller_index field (0 or 1) replaces the original
 * `this == &master` pointer comparisons.
 */
struct PicController {
    // ─────────────────────────────────────────────────────────────────────────
    // ICW (Initialization Command Word) State
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t icw_words = 0;          ///< Number of ICW words expected
    uint32_t icw_index = 0;          ///< Current ICW index during init

    // ─────────────────────────────────────────────────────────────────────────
    // Mode Flags
    // ─────────────────────────────────────────────────────────────────────────

    bool special = false;            ///< Special mask mode
    bool auto_eoi = false;           ///< Automatic end-of-interrupt
    bool rotate_on_auto_eoi = false; ///< Rotate priority on auto EOI
    bool single = false;             ///< Single PIC mode (no cascade)
    bool request_issr = false;       ///< Reading ISR (true) or IRR (false)

    // ─────────────────────────────────────────────────────────────────────────
    // Vector Configuration
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t vector_base = 0;         ///< Base interrupt vector

    // ─────────────────────────────────────────────────────────────────────────
    // IRQ Signal State
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t input = 0;               ///< Input signal (set by raise/lower)
    uint8_t edge = 0;                ///< Edge trigger mask

    // ─────────────────────────────────────────────────────────────────────────
    // Core Registers
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t irr = 0;                 ///< Interrupt Request Register
    uint8_t imr = 0xFF;              ///< Interrupt Mask Register
    uint8_t imrr = 0;                ///< IMR reversed (for bit tests)
    uint8_t isr = 0;                 ///< In-Service Register
    uint8_t isrr = 0xFF;             ///< ISR reversed (for bit tests)
    uint8_t isr_ignore = 0;          ///< ISR bits to ignore

    // ─────────────────────────────────────────────────────────────────────────
    // Active IRQ Tracking
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t active_irq = 8;          ///< Currently active IRQ (8 = none)

    // ─────────────────────────────────────────────────────────────────────────
    // Controller Identity
    // ─────────────────────────────────────────────────────────────────────────

    uint8_t controller_index = 0;    ///< 0 = master, 1 = slave

    /**
     * @brief Reset controller to initial state.
     */
    void reset() noexcept {
        icw_words = 0;
        icw_index = 0;
        special = false;
        auto_eoi = false;
        rotate_on_auto_eoi = false;
        single = false;
        request_issr = false;
        vector_base = 0;
        input = 0;
        edge = 0;
        irr = 0;
        imr = 0xFF;
        imrr = 0;
        isr = 0;
        isrr = 0xFF;
        isr_ignore = 0;
        active_irq = 8;
        // controller_index is NOT reset - it's set at construction
    }

    /**
     * @brief Hash controller state for determinism verification.
     */
    void hash_into(HashBuilder& builder) const;
};

} // namespace dosbox

#endif /* DOSBOX_PIC_TYPES_H */
