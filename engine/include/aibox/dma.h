/**
 * @file dma.h
 * @brief RAII wrappers for DMA controller management.
 *
 * Provides:
 * - DmaChannel: Per-channel DMA state and transfer logic
 * - DmaController: Controller managing multiple channels
 * - DmaSubsystem: Top-level container for all DMA controllers
 *
 * Requirements implemented:
 * - REQ-MEM-001: RAII for dynamic resources
 * - REQ-MEM-003: Smart pointers for single-owner resources
 * - REQ-MEM-012: Validate DMA addresses before transfer
 * - REQ-MEM-051: Bounds validation during transfer
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include "memory.h"
#include "exceptions.h"

#include <array>
#include <memory>
#include <cstdint>
#include <functional>

namespace aibox {

// ─────────────────────────────────────────────────────────────────────────────
// DMA Transfer Types
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief DMA transfer mode.
 */
enum class DmaMode : uint8_t {
    Demand = 0,     ///< Transfer on demand
    Single = 1,     ///< Single transfer
    Block = 2,      ///< Block transfer
    Cascade = 3     ///< Cascade mode (for controller chaining)
};

/**
 * @brief DMA transfer direction.
 */
enum class DmaDirection : uint8_t {
    Verify = 0,     ///< Verify (pseudo-transfer)
    Write = 1,      ///< Write to memory (device -> memory)
    Read = 2        ///< Read from memory (memory -> device)
};

/**
 * @brief DMA transfer callback type.
 *
 * Called when a DMA transfer is requested. The callback should
 * perform the actual data transfer.
 *
 * @param channel Channel number (0-7)
 * @param buffer Pointer to transfer buffer
 * @param length Number of bytes to transfer
 * @return Number of bytes actually transferred
 */
using DmaCallback = std::function<size_t(uint8_t channel, uint8_t* buffer, size_t length)>;

// ─────────────────────────────────────────────────────────────────────────────
// DmaChannel - Per-channel state and operations
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief DMA channel state and transfer logic.
 *
 * Encapsulates per-channel DMA state. Each PC has 8 DMA channels:
 * - Channels 0-3: 8-bit transfers (controller 0)
 * - Channels 4-7: 16-bit transfers (controller 1, channel 4 is cascade)
 *
 * @note Non-copyable, non-movable (owned by DmaController).
 */
class DmaChannel {
public:
    /**
     * @brief Construct a DMA channel.
     * @param channel_num Global channel number (0-7)
     */
    explicit DmaChannel(uint8_t channel_num)
        : channel_(channel_num)
        , enabled_(false)
        , masked_(true)
        , mode_(DmaMode::Single)
        , direction_(DmaDirection::Write)
        , auto_init_(false)
        , address_decrement_(false)
        , base_address_(0)
        , base_count_(0)
        , current_address_(0)
        , current_count_(0)
        , page_(0)
    {}

    // Non-copyable, non-movable
    DmaChannel(const DmaChannel&) = delete;
    DmaChannel& operator=(const DmaChannel&) = delete;
    DmaChannel(DmaChannel&&) = delete;
    DmaChannel& operator=(DmaChannel&&) = delete;

    ~DmaChannel() = default;

    // ─────────────────────────────────────────────────────────────
    // Channel control
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Enable the channel.
     */
    void enable() noexcept { enabled_ = true; }

    /**
     * @brief Disable the channel.
     */
    void disable() noexcept { enabled_ = false; }

    /**
     * @brief Mask the channel (prevent transfers).
     */
    void mask() noexcept { masked_ = true; }

    /**
     * @brief Unmask the channel (allow transfers).
     */
    void unmask() noexcept { masked_ = false; }

    /**
     * @brief Reset the channel to initial state.
     */
    void reset() noexcept {
        enabled_ = false;
        masked_ = true;
        current_address_ = base_address_;
        current_count_ = base_count_;
    }

    // ─────────────────────────────────────────────────────────────
    // Configuration
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Set transfer mode.
     */
    void set_mode(DmaMode mode) noexcept { mode_ = mode; }

    /**
     * @brief Set transfer direction.
     */
    void set_direction(DmaDirection dir) noexcept { direction_ = dir; }

    /**
     * @brief Set auto-initialization flag.
     */
    void set_auto_init(bool enable) noexcept { auto_init_ = enable; }

    /**
     * @brief Set address decrement flag.
     */
    void set_address_decrement(bool enable) noexcept {
        address_decrement_ = enable;
    }

    /**
     * @brief Set base address (low 16 bits).
     */
    void set_base_address(uint16_t addr) noexcept {
        base_address_ = addr;
        current_address_ = addr;
    }

    /**
     * @brief Set transfer count (minus 1).
     */
    void set_base_count(uint16_t count) noexcept {
        base_count_ = count;
        current_count_ = count;
    }

    /**
     * @brief Set page register (high address bits).
     */
    void set_page(uint8_t page) noexcept { page_ = page; }

    /**
     * @brief Set transfer callback.
     */
    void set_callback(DmaCallback cb) { callback_ = std::move(cb); }

    // ─────────────────────────────────────────────────────────────
    // State accessors
    // ─────────────────────────────────────────────────────────────

    [[nodiscard]] uint8_t channel() const noexcept { return channel_; }
    [[nodiscard]] bool is_enabled() const noexcept { return enabled_; }
    [[nodiscard]] bool is_masked() const noexcept { return masked_; }
    [[nodiscard]] bool is_ready() const noexcept {
        return enabled_ && !masked_;
    }
    [[nodiscard]] DmaMode mode() const noexcept { return mode_; }
    [[nodiscard]] DmaDirection direction() const noexcept { return direction_; }
    [[nodiscard]] bool auto_init() const noexcept { return auto_init_; }
    [[nodiscard]] uint16_t base_address() const noexcept { return base_address_; }
    [[nodiscard]] uint16_t base_count() const noexcept { return base_count_; }
    [[nodiscard]] uint16_t current_address() const noexcept { return current_address_; }
    [[nodiscard]] uint16_t current_count() const noexcept { return current_count_; }
    [[nodiscard]] uint8_t page() const noexcept { return page_; }

    /**
     * @brief Get full physical address (page + address).
     */
    [[nodiscard]] uint32_t physical_address() const noexcept {
        // For 8-bit channels: page << 16 | address
        // For 16-bit channels: page << 17 | (address << 1)
        if (channel_ >= 4) {
            // 16-bit channel
            return (static_cast<uint32_t>(page_) << 17) |
                   (static_cast<uint32_t>(current_address_) << 1);
        } else {
            // 8-bit channel
            return (static_cast<uint32_t>(page_) << 16) |
                   static_cast<uint32_t>(current_address_);
        }
    }

    /**
     * @brief Get remaining transfer count.
     */
    [[nodiscard]] size_t remaining() const noexcept {
        return static_cast<size_t>(current_count_) + 1;
    }

    /**
     * @brief Check if transfer is complete.
     */
    [[nodiscard]] bool is_complete() const noexcept {
        return current_count_ == 0xFFFF;  // Wrapped around
    }

    // ─────────────────────────────────────────────────────────────
    // Transfer operations
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Perform DMA transfer with bounds validation.
     *
     * Validates addresses before transfer and invokes callback.
     *
     * @param mem Guest memory reference
     * @param length Maximum bytes to transfer (0 = use remaining count)
     * @return Number of bytes actually transferred
     * @throws MemoryAccessException if addresses out of bounds
     */
    size_t transfer(GuestMemory& mem, size_t length = 0) {
        if (!is_ready()) {
            return 0;
        }

        // Calculate transfer size
        size_t transfer_size = length > 0 ? length : remaining();
        if (transfer_size > remaining()) {
            transfer_size = remaining();
        }

        // Get physical address
        uint32_t addr = physical_address();

        // Validate address range (REQ-MEM-012, REQ-MEM-051)
        if (!mem.in_bounds(addr, transfer_size)) {
            throw MemoryAccessException(addr, transfer_size);
        }

        // Perform transfer via callback or direct memory access
        size_t transferred = 0;
        if (callback_) {
            transferred = callback_(channel_, mem.data() + addr, transfer_size);
        } else {
            // No callback - just update counters
            transferred = transfer_size;
        }

        // Update counters
        if (transferred > 0) {
            update_counters(transferred);
        }

        // Check for completion
        if (is_complete() && auto_init_) {
            // Reload from base values
            current_address_ = base_address_;
            current_count_ = base_count_;
        }

        return transferred;
    }

    /**
     * @brief Read single byte from memory via DMA.
     *
     * @param mem Guest memory
     * @return Byte read, or 0 if transfer not ready
     */
    uint8_t read_byte(GuestMemory& mem) {
        if (!is_ready() || remaining() == 0) {
            return 0;
        }

        uint32_t addr = physical_address();
        if (!mem.in_bounds(addr, 1)) {
            throw MemoryAccessException(addr, 1);
        }

        uint8_t value = mem.read8_unchecked(addr);
        update_counters(1);
        return value;
    }

    /**
     * @brief Write single byte to memory via DMA.
     *
     * @param mem Guest memory
     * @param value Byte to write
     */
    void write_byte(GuestMemory& mem, uint8_t value) {
        if (!is_ready() || remaining() == 0) {
            return;
        }

        uint32_t addr = physical_address();
        if (!mem.in_bounds(addr, 1)) {
            throw MemoryAccessException(addr, 1);
        }

        mem.write8_unchecked(addr, value);
        update_counters(1);
    }

private:
    uint8_t channel_;
    bool enabled_;
    bool masked_;
    DmaMode mode_;
    DmaDirection direction_;
    bool auto_init_;
    bool address_decrement_;
    uint16_t base_address_;
    uint16_t base_count_;
    uint16_t current_address_;
    uint16_t current_count_;
    uint8_t page_;
    DmaCallback callback_;

    /**
     * @brief Update address and count after transfer.
     */
    void update_counters(size_t bytes) noexcept {
        if (address_decrement_) {
            current_address_ -= static_cast<uint16_t>(bytes);
        } else {
            current_address_ += static_cast<uint16_t>(bytes);
        }
        current_count_ -= static_cast<uint16_t>(bytes);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// DmaController - Controller managing multiple channels
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief DMA controller managing multiple channels.
 *
 * A PC has two DMA controllers:
 * - Controller 0: Channels 0-3 (8-bit transfers)
 * - Controller 1: Channels 4-7 (16-bit transfers)
 *
 * @note Non-copyable. Use smart pointers for ownership.
 */
class DmaController {
public:
    static constexpr size_t NUM_CHANNELS = 4;

    /**
     * @brief Construct a DMA controller.
     * @param controller_num Controller number (0 or 1)
     */
    explicit DmaController(uint8_t controller_num)
        : controller_num_(controller_num)
        , command_reg_(0)
        , status_reg_(0)
        , request_reg_(0)
        , temp_reg_(0)
        , flip_flop_(false)
    {
        for (uint8_t i = 0; i < NUM_CHANNELS; i++) {
            uint8_t global_channel = controller_num * NUM_CHANNELS + i;
            channels_[i] = std::make_unique<DmaChannel>(global_channel);
        }
    }

    // Non-copyable
    DmaController(const DmaController&) = delete;
    DmaController& operator=(const DmaController&) = delete;

    // Movable
    DmaController(DmaController&&) = default;
    DmaController& operator=(DmaController&&) = default;

    ~DmaController() = default;

    // ─────────────────────────────────────────────────────────────
    // Channel access
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Get channel by local index (0-3).
     * @param local_index Channel index within this controller
     * @return Pointer to channel, or nullptr if invalid index
     */
    [[nodiscard]] DmaChannel* channel(uint8_t local_index) noexcept {
        if (local_index >= NUM_CHANNELS) {
            return nullptr;
        }
        return channels_[local_index].get();
    }

    /**
     * @brief Get const channel by local index.
     */
    [[nodiscard]] const DmaChannel* channel(uint8_t local_index) const noexcept {
        if (local_index >= NUM_CHANNELS) {
            return nullptr;
        }
        return channels_[local_index].get();
    }

    // ─────────────────────────────────────────────────────────────
    // Controller registers
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Reset all channels.
     */
    void reset() noexcept {
        for (auto& ch : channels_) {
            ch->reset();
        }
        command_reg_ = 0;
        status_reg_ = 0;
        request_reg_ = 0;
        temp_reg_ = 0;
        flip_flop_ = false;
    }

    /**
     * @brief Write command register.
     */
    void write_command(uint8_t value) noexcept {
        command_reg_ = value;
    }

    /**
     * @brief Read status register.
     */
    [[nodiscard]] uint8_t read_status() const noexcept {
        return status_reg_;
    }

    /**
     * @brief Write mode register for a channel.
     */
    void write_mode(uint8_t value) noexcept {
        uint8_t ch_idx = value & 0x03;
        if (ch_idx < NUM_CHANNELS) {
            DmaChannel* ch = channels_[ch_idx].get();
            ch->set_mode(static_cast<DmaMode>((value >> 6) & 0x03));
            ch->set_direction(static_cast<DmaDirection>((value >> 2) & 0x03));
            ch->set_auto_init((value & 0x10) != 0);
            ch->set_address_decrement((value & 0x20) != 0);
        }
    }

    /**
     * @brief Write single mask register.
     */
    void write_single_mask(uint8_t value) noexcept {
        uint8_t ch_idx = value & 0x03;
        if (ch_idx < NUM_CHANNELS) {
            if (value & 0x04) {
                channels_[ch_idx]->mask();
            } else {
                channels_[ch_idx]->unmask();
            }
        }
    }

    /**
     * @brief Write all mask register.
     */
    void write_all_mask(uint8_t value) noexcept {
        for (size_t i = 0; i < NUM_CHANNELS; i++) {
            if (value & (1 << i)) {
                channels_[i]->mask();
            } else {
                channels_[i]->unmask();
            }
        }
    }

    /**
     * @brief Clear flip-flop.
     */
    void clear_flip_flop() noexcept {
        flip_flop_ = false;
    }

    /**
     * @brief Get flip-flop state and toggle.
     */
    bool flip_flop() noexcept {
        bool val = flip_flop_;
        flip_flop_ = !flip_flop_;
        return val;
    }

    /**
     * @brief Get controller number.
     */
    [[nodiscard]] uint8_t controller_num() const noexcept {
        return controller_num_;
    }

private:
    uint8_t controller_num_;
    std::array<std::unique_ptr<DmaChannel>, NUM_CHANNELS> channels_;
    uint8_t command_reg_;
    uint8_t status_reg_;
    uint8_t request_reg_;
    uint8_t temp_reg_;
    bool flip_flop_;
};

// ─────────────────────────────────────────────────────────────────────────────
// DmaSubsystem - Top-level container
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief RAII container for all DMA controllers.
 *
 * Replaces global `DmaController* DmaControllers[2]` with an
 * RAII-managed container.
 *
 * @note Non-copyable. Use smart pointers for ownership.
 */
class DmaSubsystem {
public:
    static constexpr size_t NUM_CONTROLLERS = 2;
    static constexpr size_t TOTAL_CHANNELS = NUM_CONTROLLERS * DmaController::NUM_CHANNELS;

    /**
     * @brief Construct DMA subsystem with both controllers.
     */
    DmaSubsystem() {
        for (uint8_t i = 0; i < NUM_CONTROLLERS; i++) {
            controllers_[i] = std::make_unique<DmaController>(i);
        }
    }

    // Non-copyable
    DmaSubsystem(const DmaSubsystem&) = delete;
    DmaSubsystem& operator=(const DmaSubsystem&) = delete;

    // Movable
    DmaSubsystem(DmaSubsystem&&) = default;
    DmaSubsystem& operator=(DmaSubsystem&&) = default;

    ~DmaSubsystem() = default;

    // ─────────────────────────────────────────────────────────────
    // Controller access
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Get controller by index.
     * @param index Controller index (0 or 1)
     * @return Pointer to controller, or nullptr if invalid
     */
    [[nodiscard]] DmaController* controller(uint8_t index) noexcept {
        if (index >= NUM_CONTROLLERS) {
            return nullptr;
        }
        return controllers_[index].get();
    }

    /**
     * @brief Get const controller by index.
     */
    [[nodiscard]] const DmaController* controller(uint8_t index) const noexcept {
        if (index >= NUM_CONTROLLERS) {
            return nullptr;
        }
        return controllers_[index].get();
    }

    // ─────────────────────────────────────────────────────────────
    // Global channel access
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Get channel by global channel number (0-7).
     * @param global_channel Channel number
     * @return Pointer to channel, or nullptr if invalid
     */
    [[nodiscard]] DmaChannel* channel(uint8_t global_channel) noexcept {
        if (global_channel >= TOTAL_CHANNELS) {
            return nullptr;
        }
        uint8_t ctrl_idx = global_channel / DmaController::NUM_CHANNELS;
        uint8_t chan_idx = global_channel % DmaController::NUM_CHANNELS;
        return controllers_[ctrl_idx]->channel(chan_idx);
    }

    /**
     * @brief Get const channel by global channel number.
     */
    [[nodiscard]] const DmaChannel* channel(uint8_t global_channel) const noexcept {
        if (global_channel >= TOTAL_CHANNELS) {
            return nullptr;
        }
        uint8_t ctrl_idx = global_channel / DmaController::NUM_CHANNELS;
        uint8_t chan_idx = global_channel % DmaController::NUM_CHANNELS;
        return controllers_[ctrl_idx]->channel(chan_idx);
    }

    // ─────────────────────────────────────────────────────────────
    // Operations
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Reset all controllers and channels.
     */
    void reset() noexcept {
        for (auto& ctrl : controllers_) {
            ctrl->reset();
        }
    }

private:
    std::array<std::unique_ptr<DmaController>, NUM_CONTROLLERS> controllers_;
};

} // namespace aibox
