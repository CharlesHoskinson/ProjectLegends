// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MIDI configuration from [midi] config section.

#pragma once

#include <string>
#include <string_view>
#include <cstdint>

namespace legends {

class ConfigParser;

/// MIDI device backend selection.
enum class MIDIDevice : uint8_t {
    None = 0,       ///< No MIDI device (inactive).
    FluidSynth,     ///< FluidSynth software synthesizer.
    MT32,           ///< Roland MT-32 emulation.
    Synth,          ///< Built-in synth.
};

/// MIDI configuration loaded from the [midi] config section.
struct MIDIConfig {
    MIDIDevice device = MIDIDevice::None;   ///< Active MIDI backend.
    std::string soundfont_path;             ///< FluidSynth .sf2 soundfont path.
    std::string mt32_romdir;                ///< MT-32 ROM directory.
    uint32_t sample_rate = 44100;           ///< Audio sample rate in Hz.
    float volume = 1.0f;                    ///< Volume multiplier (0.0–1.0).

    /// Load settings from the [midi] section of a ConfigParser.
    /// @param config  Parsed configuration source.
    void loadFrom(const ConfigParser& config);

    [[nodiscard]] static MIDIDevice parseDeviceName(std::string_view name);

    /// Get the canonical string name for a MIDIDevice enum value.
    /// @param device  The device enum.
    /// @return Null-terminated device name string.
    [[nodiscard]] static const char* deviceName(MIDIDevice device);

    /// Validate that required fields are present for the selected device.
    /// @return true if the configuration is usable.
    [[nodiscard]] bool isValid() const;
};

} // namespace legends
