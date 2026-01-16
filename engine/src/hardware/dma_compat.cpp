/**
 * @file dma_compat.cpp
 * @brief DMA compatibility shim for legacy code.
 *
 * Sprint 2 Phase 3: Provides backward-compatible API using current_context().
 *
 * These functions are on the CI allowlist for current_context() usage.
 * New code should use ctx.dma.get_channel() directly instead.
 *
 * Note: This file is excluded from headless builds since it requires the
 * full DOSBox-X environment with dma.h (which depends on config.h).
 *
 * @copyright GPL-2.0-or-later
 */

// Skip entire file in headless mode - requires full DOSBox-X environment
#ifndef AIBOX_HEADLESS

#include "dma.h"
#include "dosbox/dosbox_context.h"

// ═══════════════════════════════════════════════════════════════════════════════
// Legacy DMA API (uses current_context())
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef DOSBOX_LIBRARY_MODE

/**
 * @brief Get DMA channel by number (legacy API).
 *
 * This is a compatibility shim that retrieves the channel from the
 * current context. New code should use ctx.dma.get_channel() directly.
 *
 * @param chan Channel number (0-7)
 * @return Pointer to channel, or nullptr if unavailable
 */
DmaChannel* GetDMAChannel(uint8_t chan) {
    if (!dosbox::has_current_context()) {
        // Fallback to global for transitional period
        // This allows code that hasn't migrated yet to still work
        extern DmaController* DmaControllers[2];
        if (chan < 4) {
            if (!DmaControllers[0]) return nullptr;
            return DmaControllers[0]->GetChannel(chan);
        } else if (chan < 8) {
            if (!DmaControllers[1]) return nullptr;
            return DmaControllers[1]->GetChannel(chan - 4);
        }
        return nullptr;
    }

    return dosbox::current_context().dma.get_channel(chan);
}

/**
 * @brief Check if second DMA controller exists (legacy API).
 *
 * @return true if second controller is present
 */
bool SecondDMAControllerAvailable() {
    if (!dosbox::has_current_context()) {
        extern DmaController* DmaControllers[2];
        return DmaControllers[1] != nullptr;
    }

    return dosbox::current_context().dma.has_second_controller();
}

/**
 * @brief Close the second DMA controller (legacy API).
 *
 * Deallocates the second (16-bit) DMA controller.
 * Used for PC/XT compatibility mode.
 */
void CloseSecondDMAController() {
    if (!dosbox::has_current_context()) {
        extern DmaController* DmaControllers[2];
        if (DmaControllers[1]) {
            delete DmaControllers[1];
            DmaControllers[1] = nullptr;
        }
        return;
    }

    dosbox::current_context().dma.close_second_controller();
}

#endif // DOSBOX_LIBRARY_MODE

#endif // !AIBOX_HEADLESS
