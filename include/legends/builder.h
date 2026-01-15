/**
 * @file builder.h
 * @brief Fluent builder patterns for configuration.
 *
 * Provides chainable configuration builders with validation.
 * User-defined literals for memory sizes are also included.
 */

#pragma once

#include "machine_context.h"
#include "enums.h"
#include <vector>
#include <string>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// User-Defined Literals for Memory Sizes
// ─────────────────────────────────────────────────────────────────────────────

namespace literals {

/**
 * @brief User-defined literal for kilobytes.
 * @code
 *   size_t mem = 64_KB;  // 65536
 * @endcode
 */
constexpr size_t operator""_KB(unsigned long long kb) noexcept {
    return static_cast<size_t>(kb) * 1024;
}

/**
 * @brief User-defined literal for megabytes.
 * @code
 *   size_t mem = 16_MB;  // 16777216
 * @endcode
 */
constexpr size_t operator""_MB(unsigned long long mb) noexcept {
    return static_cast<size_t>(mb) * 1024 * 1024;
}

/**
 * @brief User-defined literal for gigabytes.
 * @code
 *   size_t mem = 1_GB;  // 1073741824
 * @endcode
 */
constexpr size_t operator""_GB(unsigned long long gb) noexcept {
    return static_cast<size_t>(gb) * 1024 * 1024 * 1024;
}

/**
 * @brief User-defined literal for cycles per millisecond.
 * @code
 *   uint32_t cycles = 3000_cycles;
 * @endcode
 */
constexpr uint32_t operator""_cycles(unsigned long long c) noexcept {
    return static_cast<uint32_t>(c);
}

} // namespace literals

// ─────────────────────────────────────────────────────────────────────────────
// MachineBuilder
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Fluent builder for MachineConfig.
 *
 * Provides a chainable API for constructing validated configurations.
 * Validates all parameters on build() and returns errors if invalid.
 *
 * Example:
 * @code
 *   using namespace legends::literals;
 *
 *   auto result = MachineBuilder()
 *       .with_memory(16_MB)
 *       .with_vga_memory(1_MB)
 *       .with_cycles(10000)
 *       .with_machine_type(MachineType::VGA)
 *       .deterministic()
 *       .with_sound(false)
 *       .build();
 *
 *   if (result.has_value()) {
 *       MachineContext ctx(result.value());
 *       ctx.initialize();
 *   } else {
 *       std::cerr << "Error: " << result.error().message() << "\n";
 *   }
 * @endcode
 */
class MachineBuilder {
public:
    MachineBuilder() = default;

    // ─────────────────────────────────────────────────────────────────────────
    // Memory Configuration
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set guest memory size.
     * @param bytes Memory size in bytes (1MB to 256MB)
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_memory(size_t bytes) noexcept {
        config_.memory_size = bytes;
        return *this;
    }

    /**
     * @brief Set VGA memory size.
     * @param bytes VGA memory in bytes (64KB to 16MB)
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_vga_memory(size_t bytes) noexcept {
        config_.vga_memory = bytes;
        return *this;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // CPU Configuration
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set CPU cycles per millisecond.
     * @param cycles Cycles (100 to 1000000)
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_cycles(uint32_t cycles) noexcept {
        config_.cpu_cycles = cycles;
        return *this;
    }

    /**
     * @brief Enable/disable dynamic recompiler.
     * @param enabled Whether to use dynamic core
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_dynamic_core(bool enabled = true) noexcept {
        config_.cpu_dynamic_core = enabled;
        return *this;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Machine Type
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Set emulated machine type.
     * @param type Machine type
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_machine_type(MachineType type) noexcept {
        config_.machine_type = type;
        return *this;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Timing
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Enable deterministic mode (for testing/replay).
     * @param enabled Whether to enable deterministic timing
     * @return Reference to this builder for chaining
     */
    MachineBuilder& deterministic(bool enabled = true) noexcept {
        config_.deterministic = enabled;
        return *this;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Peripherals
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Enable/disable sound subsystem.
     * @param enabled Whether to enable sound
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_sound(bool enabled = true) noexcept {
        config_.sound_enabled = enabled;
        return *this;
    }

    /**
     * @brief Enable/disable Sound Blaster 16.
     * @param enabled Whether to enable SB16
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_sb16(bool enabled = true) noexcept {
        config_.sb16_enabled = enabled;
        return *this;
    }

    /**
     * @brief Enable/disable AdLib/OPL.
     * @param enabled Whether to enable AdLib
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_adlib(bool enabled = true) noexcept {
        config_.adlib_enabled = enabled;
        return *this;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Debug
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Enable/disable debug mode.
     * @param enabled Whether to enable debug features
     * @return Reference to this builder for chaining
     */
    MachineBuilder& with_debug(bool enabled = true) noexcept {
        config_.debug_mode = enabled;
        return *this;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Presets
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Configure for minimal testing.
     * @return Reference to this builder for chaining
     */
    MachineBuilder& minimal() noexcept {
        config_.memory_size = 1024 * 1024;   // 1MB
        config_.vga_memory = 64 * 1024;      // 64KB
        config_.sound_enabled = false;
        config_.deterministic = true;
        return *this;
    }

    /**
     * @brief Configure for standard VGA machine.
     * @return Reference to this builder for chaining
     */
    MachineBuilder& vga_standard() noexcept {
        config_ = MachineConfig::vga_default();
        return *this;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Build
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Validate and build configuration.
     *
     * Validates all parameters and returns either the valid
     * configuration or an error describing what went wrong.
     *
     * @return Result with valid config or error
     */
    [[nodiscard]] Result<MachineConfig> build() {
        errors_.clear();

        // Validate memory size
        if (config_.memory_size < 1024 * 1024) {
            errors_.push_back("Memory must be at least 1MB");
        }
        if (config_.memory_size > 256 * 1024 * 1024) {
            errors_.push_back("Memory cannot exceed 256MB");
        }

        // Validate VGA memory
        if (config_.vga_memory < 64 * 1024) {
            errors_.push_back("VGA memory must be at least 64KB");
        }
        if (config_.vga_memory > 16 * 1024 * 1024) {
            errors_.push_back("VGA memory cannot exceed 16MB");
        }

        // Validate cycles
        if (config_.cpu_cycles < 100) {
            errors_.push_back("CPU cycles must be at least 100");
        }
        if (config_.cpu_cycles > 1000000) {
            errors_.push_back("CPU cycles cannot exceed 1000000");
        }

        // Validate machine type
        if (!legends::is_valid(config_.machine_type)) {
            errors_.push_back("Invalid machine type");
        }

        // Validate SVGA memory requirement
        if (config_.machine_type == MachineType::SVGA_S3 &&
            config_.vga_memory < 1024 * 1024) {
            errors_.push_back("SVGA mode requires at least 1MB VGA memory");
        }

        // Return error if validation failed
        if (!errors_.empty()) {
            std::string msg = "Configuration validation failed:";
            for (const auto& err : errors_) {
                msg += "\n  - " + err;
            }
            return Err(Error(ErrorCode::ConfigValueInvalid, msg));
        }

        return Ok(config_);
    }

    /**
     * @brief Build or throw on error.
     *
     * Convenience method that throws on validation failure.
     *
     * @return Valid configuration
     * @throws std::runtime_error if validation fails
     */
    [[nodiscard]] MachineConfig build_or_throw() {
        auto result = build();
        if (!result.has_value()) {
            throw std::runtime_error(result.error().message());
        }
        return result.value();
    }

    /**
     * @brief Check if current configuration would be valid.
     * @return true if build() would succeed
     */
    [[nodiscard]] bool is_valid() const {
        // Use const_cast to call build() which is non-const due to errors_
        return const_cast<MachineBuilder*>(this)->build().has_value();
    }

    /**
     * @brief Get validation errors from last build() call.
     * @return Reference to error list
     */
    [[nodiscard]] const std::vector<std::string>& errors() const noexcept {
        return errors_;
    }

    /**
     * @brief Get current configuration (without validation).
     * @return Reference to configuration being built
     */
    [[nodiscard]] const MachineConfig& current_config() const noexcept {
        return config_;
    }

private:
    MachineConfig config_;
    std::vector<std::string> errors_;
};

} // namespace legends
