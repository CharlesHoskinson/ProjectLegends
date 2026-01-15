// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Host Clock Interface

#pragma once

#include "pal/types.h"
#include <cstdint>

namespace pal {

/// Host wall-clock for UI timing and throttling
///
/// IMPORTANT: This is NOT emulated time!
///
/// Emulated time advances ONLY via stepping (stepMs/stepCycles).
/// Host clock is for:
///   - UI timestamps
///   - Frame throttling/pacing
///   - Performance measurement
///   - Sleep for host-side delays
///
/// NEVER use host clock values to calculate emulated time.
class IHostClock {
public:
    virtual ~IHostClock() = default;

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    /// Initialize the host clock
    /// @return Success, AlreadyInitialized
    virtual Result initialize() = 0;

    /// Shutdown the host clock (safe to call if not initialized)
    virtual void shutdown() = 0;

    /// Check if clock is initialized
    virtual bool isInitialized() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Time Query (Host Wall-Clock)
    // ═══════════════════════════════════════════════════════════════════════

    /// Get milliseconds since initialization
    /// @return Milliseconds since init, or 0 if not initialized
    /// @note Values increase monotonically (never decrease)
    virtual uint64_t getTicksMs() const = 0;

    /// Get microseconds since initialization
    /// @return Microseconds since init, or 0 if not initialized
    /// @note Values increase monotonically (never decrease)
    virtual uint64_t getTicksUs() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Sleep (Host-Side Delays)
    // ═══════════════════════════════════════════════════════════════════════

    /// Sleep for approximately ms milliseconds
    /// @note May sleep longer than requested, but never returns early
    /// @note Headless backend: non-blocking (returns immediately)
    virtual void sleepMs(uint32_t ms) = 0;

    /// Sleep for approximately us microseconds
    /// @note May sleep longer than requested, but never returns early
    /// @note Headless backend: non-blocking (returns immediately)
    virtual void sleepUs(uint64_t us) = 0;
};

} // namespace pal
