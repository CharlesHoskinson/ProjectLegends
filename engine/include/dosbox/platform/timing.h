/**
 * @file timing.h
 * @brief Platform-agnostic timing interface for DOSBox library mode.
 *
 * This interface abstracts host timing operations, allowing DOSBox to
 * run with real-time timing or deterministic stepping.
 *
 * ## Design Principles
 * 1. **Determinism Mode**: Emulation time is virtual, controlled by step()
 * 2. **Real-Time Mode**: Host time drives emulation (normal gameplay)
 * 3. **No SDL Dependencies**: Pure C++ interface
 *
 * ## Two Timing Models
 *
 * ### Deterministic (Library/Headless Mode)
 * - get_ticks() returns a fixed value or is driven by step_ms()
 * - delay() is a no-op
 * - Emulation runs as fast as possible
 *
 * ### Real-Time (GUI Mode)
 * - get_ticks() returns actual wall-clock time
 * - delay() actually sleeps
 * - Emulation throttled to match real time
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_PLATFORM_TIMING_H
#define DOSBOX_PLATFORM_TIMING_H

#include <cstdint>
#include <chrono>
#include <thread>

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// Timing Interface
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Abstract timing interface for DOSBox.
 *
 * Implementations:
 * - VirtualTiming: Deterministic, virtual time (headless)
 * - HostTiming: Real wall-clock time (GUI)
 * - SDL2Timing: Uses SDL2 timing functions
 *
 * ## Thread Safety
 * All methods are thread-safe (atomic reads/writes).
 */
class ITiming {
public:
    virtual ~ITiming() = default;

    // ─────────────────────────────────────────────────────────────────────────
    // Tick Counter
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get the current tick count in milliseconds.
     *
     * In deterministic mode, this is virtual time.
     * In real-time mode, this is wall-clock time since init.
     */
    virtual uint32_t get_ticks() const = 0;

    /**
     * @brief Get the current tick count in microseconds.
     *
     * Higher precision version for accurate timing.
     */
    virtual uint64_t get_ticks_us() const = 0;

    // ─────────────────────────────────────────────────────────────────────────
    // Delays
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Delay for the specified number of milliseconds.
     *
     * In deterministic mode, this is a no-op (instant return).
     * In real-time mode, this actually sleeps.
     *
     * @param ms Milliseconds to delay
     */
    virtual void delay(uint32_t ms) = 0;

    /**
     * @brief Delay for the specified number of microseconds.
     *
     * Higher precision delay for tight timing loops.
     *
     * @param us Microseconds to delay
     */
    virtual void delay_us(uint64_t us) {
        // Default: round up to ms
        delay(static_cast<uint32_t>((us + 999) / 1000));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Timing Mode
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Check if running in deterministic mode.
     *
     * In deterministic mode:
     * - get_ticks() returns virtual time
     * - delay() is a no-op
     * - Time advances only via advance_time()
     */
    virtual bool is_deterministic() const = 0;

    /**
     * @brief Advance virtual time (deterministic mode only).
     *
     * @param ms Milliseconds to advance
     */
    virtual void advance_time(uint32_t ms) {
        (void)ms;
        // No-op in real-time mode
    }

    /**
     * @brief Advance virtual time in microseconds (deterministic mode only).
     *
     * @param us Microseconds to advance
     */
    virtual void advance_time_us(uint64_t us) {
        advance_time(static_cast<uint32_t>((us + 999) / 1000));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Performance Counter (high resolution)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get high-resolution performance counter.
     *
     * Used for profiling and precise measurements.
     */
    virtual uint64_t get_performance_counter() const = 0;

    /**
     * @brief Get performance counter frequency (ticks per second).
     */
    virtual uint64_t get_performance_frequency() const = 0;

    /**
     * @brief Convert performance counter delta to microseconds.
     */
    uint64_t counter_to_us(uint64_t delta) const {
        uint64_t freq = get_performance_frequency();
        if (freq == 0) return 0;
        return (delta * 1000000ULL) / freq;
    }

    /**
     * @brief Convert performance counter delta to milliseconds.
     */
    uint32_t counter_to_ms(uint64_t delta) const {
        return static_cast<uint32_t>(counter_to_us(delta) / 1000);
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Virtual Timing (Deterministic)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Deterministic virtual timing implementation.
 *
 * Time advances only when advance_time() is called.
 * Ideal for headless/library mode, testing, and replay.
 */
class VirtualTiming : public ITiming {
public:
    uint32_t get_ticks() const override {
        return static_cast<uint32_t>(ticks_us_ / 1000);
    }

    uint64_t get_ticks_us() const override {
        return ticks_us_;
    }

    void delay(uint32_t /*ms*/) override {
        // No-op in deterministic mode
    }

    void delay_us(uint64_t /*us*/) override {
        // No-op in deterministic mode
    }

    bool is_deterministic() const override {
        return true;
    }

    void advance_time(uint32_t ms) override {
        ticks_us_ += static_cast<uint64_t>(ms) * 1000;
    }

    void advance_time_us(uint64_t us) override {
        ticks_us_ += us;
    }

    uint64_t get_performance_counter() const override {
        // Use virtual ticks as performance counter
        return ticks_us_;
    }

    uint64_t get_performance_frequency() const override {
        return 1000000;  // Microseconds
    }

    /// Reset to initial state
    void reset() {
        ticks_us_ = 0;
    }

    /// Set absolute time (for save/load)
    void set_ticks_us(uint64_t us) {
        ticks_us_ = us;
    }

private:
    uint64_t ticks_us_ = 0;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Host Timing (Real-Time)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Real wall-clock timing implementation.
 *
 * Uses std::chrono for portable high-resolution timing.
 * For SDL-based timing, use SDL2Timing backend instead.
 */
class HostTiming : public ITiming {
public:
    HostTiming() : start_time_(std::chrono::steady_clock::now()) {}

    uint32_t get_ticks() const override {
        auto now = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now - start_time_);
        return static_cast<uint32_t>(duration.count());
    }

    uint64_t get_ticks_us() const override {
        auto now = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(now - start_time_);
        return static_cast<uint64_t>(duration.count());
    }

    void delay(uint32_t ms) override {
        if (ms > 0) {
            std::this_thread::sleep_for(std::chrono::milliseconds(ms));
        }
    }

    void delay_us(uint64_t us) override {
        if (us > 0) {
            std::this_thread::sleep_for(std::chrono::microseconds(us));
        }
    }

    bool is_deterministic() const override {
        return false;
    }

    uint64_t get_performance_counter() const override {
        auto now = std::chrono::high_resolution_clock::now();
        return static_cast<uint64_t>(now.time_since_epoch().count());
    }

    uint64_t get_performance_frequency() const override {
        using period = std::chrono::high_resolution_clock::period;
        return static_cast<uint64_t>(period::den / period::num);
    }

    /// Reset start time
    void reset() {
        start_time_ = std::chrono::steady_clock::now();
    }

private:
    std::chrono::steady_clock::time_point start_time_;
};

} // namespace platform
} // namespace dosbox

// Need thread header for sleep_for
#include <thread>

#endif // DOSBOX_PLATFORM_TIMING_H
