/**
 * @file enums.h
 * @brief Type-safe enumerations with utilities.
 *
 * Provides to_string(), is_valid(), and parse_*() utilities
 * for all enum types. Also defines additional enums not covered
 * by other headers.
 */

#pragma once

#include <array>
#include <optional>
#include <string_view>
#include <cstdint>
#include <utility>

// Include existing enum definitions
#include "cpu_context.h"
#include "machine_context.h"

namespace aibox {

// ─────────────────────────────────────────────────────────────────────────────
// VGA Mode Enumeration
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief VGA display mode.
 *
 * Standard VGA mode numbers from the BIOS INT 10h interface.
 */
enum class VgaMode : uint8_t {
    Text40x25_Mono = 0x00,   ///< 40x25 text, monochrome
    Text40x25_Color = 0x01,  ///< 40x25 text, 16 colors
    Text80x25_Mono = 0x02,   ///< 80x25 text, monochrome
    Text80x25_Color = 0x03,  ///< 80x25 text, 16 colors
    Cga320x200_4 = 0x04,     ///< CGA 320x200, 4 colors
    Cga320x200_4Mono = 0x05, ///< CGA 320x200, 4 grays
    Cga640x200_2 = 0x06,     ///< CGA 640x200, 2 colors
    Mda80x25 = 0x07,         ///< MDA 80x25 text, monochrome
    Ega320x200 = 0x0D,       ///< EGA 320x200, 16 colors
    Ega640x200 = 0x0E,       ///< EGA 640x200, 16 colors
    Ega640x350_Mono = 0x0F,  ///< EGA 640x350, monochrome
    Ega640x350 = 0x10,       ///< EGA 640x350, 16 colors
    Vga640x480_2 = 0x11,     ///< VGA 640x480, 2 colors
    Vga640x480 = 0x12,       ///< VGA 640x480, 16 colors
    Vga320x200_256 = 0x13,   ///< VGA 320x200, 256 colors (Mode 13h)
};

/**
 * @brief Convert VgaMode to string.
 */
[[nodiscard]] constexpr const char* to_string(VgaMode mode) noexcept {
    switch (mode) {
        case VgaMode::Text40x25_Mono:    return "Text40x25_Mono";
        case VgaMode::Text40x25_Color:   return "Text40x25_Color";
        case VgaMode::Text80x25_Mono:    return "Text80x25_Mono";
        case VgaMode::Text80x25_Color:   return "Text80x25_Color";
        case VgaMode::Cga320x200_4:      return "Cga320x200_4";
        case VgaMode::Cga320x200_4Mono:  return "Cga320x200_4Mono";
        case VgaMode::Cga640x200_2:      return "Cga640x200_2";
        case VgaMode::Mda80x25:          return "Mda80x25";
        case VgaMode::Ega320x200:        return "Ega320x200";
        case VgaMode::Ega640x200:        return "Ega640x200";
        case VgaMode::Ega640x350_Mono:   return "Ega640x350_Mono";
        case VgaMode::Ega640x350:        return "Ega640x350";
        case VgaMode::Vga640x480_2:      return "Vga640x480_2";
        case VgaMode::Vga640x480:        return "Vga640x480";
        case VgaMode::Vga320x200_256:    return "Vga320x200_256";
        default: return "Unknown";
    }
}

/**
 * @brief Check if VgaMode value is valid.
 */
[[nodiscard]] constexpr bool is_valid(VgaMode mode) noexcept {
    switch (mode) {
        case VgaMode::Text40x25_Mono:
        case VgaMode::Text40x25_Color:
        case VgaMode::Text80x25_Mono:
        case VgaMode::Text80x25_Color:
        case VgaMode::Cga320x200_4:
        case VgaMode::Cga320x200_4Mono:
        case VgaMode::Cga640x200_2:
        case VgaMode::Mda80x25:
        case VgaMode::Ega320x200:
        case VgaMode::Ega640x200:
        case VgaMode::Ega640x350_Mono:
        case VgaMode::Ega640x350:
        case VgaMode::Vga640x480_2:
        case VgaMode::Vga640x480:
        case VgaMode::Vga320x200_256:
            return true;
        default:
            return false;
    }
}

/**
 * @brief Parse VgaMode from string.
 */
[[nodiscard]] inline std::optional<VgaMode> parse_vga_mode(
    std::string_view s) noexcept
{
    if (s == "Text40x25_Mono" || s == "0x00") return VgaMode::Text40x25_Mono;
    if (s == "Text40x25_Color" || s == "0x01") return VgaMode::Text40x25_Color;
    if (s == "Text80x25_Mono" || s == "0x02") return VgaMode::Text80x25_Mono;
    if (s == "Text80x25_Color" || s == "0x03") return VgaMode::Text80x25_Color;
    if (s == "Cga320x200_4" || s == "0x04") return VgaMode::Cga320x200_4;
    if (s == "Cga320x200_4Mono" || s == "0x05") return VgaMode::Cga320x200_4Mono;
    if (s == "Cga640x200_2" || s == "0x06") return VgaMode::Cga640x200_2;
    if (s == "Mda80x25" || s == "0x07") return VgaMode::Mda80x25;
    if (s == "Ega320x200" || s == "0x0D") return VgaMode::Ega320x200;
    if (s == "Ega640x200" || s == "0x0E") return VgaMode::Ega640x200;
    if (s == "Ega640x350_Mono" || s == "0x0F") return VgaMode::Ega640x350_Mono;
    if (s == "Ega640x350" || s == "0x10") return VgaMode::Ega640x350;
    if (s == "Vga640x480_2" || s == "0x11") return VgaMode::Vga640x480_2;
    if (s == "Vga640x480" || s == "0x12") return VgaMode::Vga640x480;
    if (s == "Vga320x200_256" || s == "0x13" || s == "Mode13h") return VgaMode::Vga320x200_256;
    return std::nullopt;
}

/**
 * @brief Get mode dimensions.
 * @return {width, height} or {0, 0} for invalid mode
 */
[[nodiscard]] constexpr std::pair<uint16_t, uint16_t>
get_mode_dimensions(VgaMode mode) noexcept {
    switch (mode) {
        case VgaMode::Text40x25_Mono:
        case VgaMode::Text40x25_Color:
            return {40, 25};  // Text columns x rows
        case VgaMode::Text80x25_Mono:
        case VgaMode::Text80x25_Color:
        case VgaMode::Mda80x25:
            return {80, 25};  // Text columns x rows
        case VgaMode::Cga320x200_4:
        case VgaMode::Cga320x200_4Mono:
            return {320, 200};
        case VgaMode::Cga640x200_2:
            return {640, 200};
        case VgaMode::Ega320x200:
            return {320, 200};
        case VgaMode::Ega640x200:
            return {640, 200};
        case VgaMode::Ega640x350_Mono:
        case VgaMode::Ega640x350:
            return {640, 350};
        case VgaMode::Vga640x480_2:
        case VgaMode::Vga640x480:
            return {640, 480};
        case VgaMode::Vga320x200_256:
            return {320, 200};
        default:
            return {0, 0};
    }
}

/**
 * @brief Get bits per pixel for mode.
 */
[[nodiscard]] constexpr uint8_t get_mode_bpp(VgaMode mode) noexcept {
    switch (mode) {
        case VgaMode::Text40x25_Mono:
        case VgaMode::Text80x25_Mono:
        case VgaMode::Mda80x25:
        case VgaMode::Ega640x350_Mono:
        case VgaMode::Vga640x480_2:
            return 1;
        case VgaMode::Cga640x200_2:
            return 1;
        case VgaMode::Cga320x200_4:
        case VgaMode::Cga320x200_4Mono:
            return 2;
        case VgaMode::Text40x25_Color:
        case VgaMode::Text80x25_Color:
        case VgaMode::Ega320x200:
        case VgaMode::Ega640x200:
        case VgaMode::Ega640x350:
        case VgaMode::Vga640x480:
            return 4;
        case VgaMode::Vga320x200_256:
            return 8;
        default:
            return 0;
    }
}

/**
 * @brief Check if mode is a text mode.
 */
[[nodiscard]] constexpr bool is_text_mode(VgaMode mode) noexcept {
    switch (mode) {
        case VgaMode::Text40x25_Mono:
        case VgaMode::Text40x25_Color:
        case VgaMode::Text80x25_Mono:
        case VgaMode::Text80x25_Color:
        case VgaMode::Mda80x25:
            return true;
        default:
            return false;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// CpuMode Utilities (enum defined in cpu_context.h)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Convert CpuMode to string.
 */
[[nodiscard]] constexpr const char* to_string(CpuMode mode) noexcept {
    switch (mode) {
        case CpuMode::Real:        return "Real";
        case CpuMode::Protected16: return "Protected16";
        case CpuMode::Protected32: return "Protected32";
        case CpuMode::Virtual8086: return "Virtual8086";
        default: return "Unknown";
    }
}

/**
 * @brief Check if CpuMode value is valid.
 */
[[nodiscard]] constexpr bool is_valid(CpuMode mode) noexcept {
    switch (mode) {
        case CpuMode::Real:
        case CpuMode::Protected16:
        case CpuMode::Protected32:
        case CpuMode::Virtual8086:
            return true;
        default:
            return false;
    }
}

/**
 * @brief Parse CpuMode from string.
 */
[[nodiscard]] inline std::optional<CpuMode> parse_cpu_mode(
    std::string_view s) noexcept
{
    if (s == "Real") return CpuMode::Real;
    if (s == "Protected16") return CpuMode::Protected16;
    if (s == "Protected32") return CpuMode::Protected32;
    if (s == "Virtual8086" || s == "V86") return CpuMode::Virtual8086;
    return std::nullopt;
}

/**
 * @brief Get default address size for CPU mode.
 */
[[nodiscard]] constexpr int default_address_size(CpuMode mode) noexcept {
    switch (mode) {
        case CpuMode::Real:
        case CpuMode::Protected16:
        case CpuMode::Virtual8086:
            return 16;
        case CpuMode::Protected32:
            return 32;
        default:
            return 16;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// MachineType Utilities (enum defined in machine_context.h)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Convert MachineType to string.
 */
[[nodiscard]] constexpr const char* to_string(MachineType type) noexcept {
    switch (type) {
        case MachineType::PC:       return "PC";
        case MachineType::Tandy:    return "Tandy";
        case MachineType::PCjr:     return "PCjr";
        case MachineType::Hercules: return "Hercules";
        case MachineType::CGA:      return "CGA";
        case MachineType::EGA:      return "EGA";
        case MachineType::VGA:      return "VGA";
        case MachineType::SVGA_S3:  return "SVGA_S3";
        case MachineType::PC98:     return "PC98";
        default: return "Unknown";
    }
}

/**
 * @brief Check if MachineType value is valid.
 */
[[nodiscard]] constexpr bool is_valid(MachineType type) noexcept {
    switch (type) {
        case MachineType::PC:
        case MachineType::Tandy:
        case MachineType::PCjr:
        case MachineType::Hercules:
        case MachineType::CGA:
        case MachineType::EGA:
        case MachineType::VGA:
        case MachineType::SVGA_S3:
        case MachineType::PC98:
            return true;
        default:
            return false;
    }
}

/**
 * @brief Parse MachineType from string.
 */
[[nodiscard]] inline std::optional<MachineType> parse_machine_type(
    std::string_view s) noexcept
{
    if (s == "PC") return MachineType::PC;
    if (s == "Tandy") return MachineType::Tandy;
    if (s == "PCjr") return MachineType::PCjr;
    if (s == "Hercules") return MachineType::Hercules;
    if (s == "CGA") return MachineType::CGA;
    if (s == "EGA") return MachineType::EGA;
    if (s == "VGA") return MachineType::VGA;
    if (s == "SVGA_S3" || s == "S3") return MachineType::SVGA_S3;
    if (s == "PC98") return MachineType::PC98;
    return std::nullopt;
}

// ─────────────────────────────────────────────────────────────────────────────
// MachineState Utilities (enum defined in machine_context.h)
// NOTE: to_string already defined in machine_context.h
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Check if MachineState value is valid.
 */
[[nodiscard]] constexpr bool is_valid(MachineState state) noexcept {
    switch (state) {
        case MachineState::Created:
        case MachineState::Initialized:
        case MachineState::Running:
        case MachineState::Paused:
        case MachineState::Stopped:
        case MachineState::Shutdown:
        case MachineState::Destroyed:
            return true;
        default:
            return false;
    }
}

/**
 * @brief Parse MachineState from string.
 */
[[nodiscard]] inline std::optional<MachineState> parse_machine_state(
    std::string_view s) noexcept
{
    if (s == "Created") return MachineState::Created;
    if (s == "Initialized") return MachineState::Initialized;
    if (s == "Running") return MachineState::Running;
    if (s == "Paused") return MachineState::Paused;
    if (s == "Stopped") return MachineState::Stopped;
    if (s == "Shutdown") return MachineState::Shutdown;
    if (s == "Destroyed") return MachineState::Destroyed;
    return std::nullopt;
}

// ─────────────────────────────────────────────────────────────────────────────
// Enum Iteration Support
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief All standard VGA modes for iteration.
 */
inline constexpr std::array<VgaMode, 15> all_vga_modes = {
    VgaMode::Text40x25_Mono,
    VgaMode::Text40x25_Color,
    VgaMode::Text80x25_Mono,
    VgaMode::Text80x25_Color,
    VgaMode::Cga320x200_4,
    VgaMode::Cga320x200_4Mono,
    VgaMode::Cga640x200_2,
    VgaMode::Mda80x25,
    VgaMode::Ega320x200,
    VgaMode::Ega640x200,
    VgaMode::Ega640x350_Mono,
    VgaMode::Ega640x350,
    VgaMode::Vga640x480_2,
    VgaMode::Vga640x480,
    VgaMode::Vga320x200_256,
};

/**
 * @brief All CPU modes for iteration.
 */
inline constexpr std::array<CpuMode, 4> all_cpu_modes = {
    CpuMode::Real,
    CpuMode::Protected16,
    CpuMode::Protected32,
    CpuMode::Virtual8086,
};

/**
 * @brief All machine types for iteration.
 */
inline constexpr std::array<MachineType, 9> all_machine_types = {
    MachineType::PC,
    MachineType::Tandy,
    MachineType::PCjr,
    MachineType::Hercules,
    MachineType::CGA,
    MachineType::EGA,
    MachineType::VGA,
    MachineType::SVGA_S3,
    MachineType::PC98,
};

/**
 * @brief All machine states for iteration.
 */
inline constexpr std::array<MachineState, 7> all_machine_states = {
    MachineState::Created,
    MachineState::Initialized,
    MachineState::Running,
    MachineState::Paused,
    MachineState::Stopped,
    MachineState::Shutdown,
    MachineState::Destroyed,
};

} // namespace aibox
