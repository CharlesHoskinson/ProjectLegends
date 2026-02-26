// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// MIDI configuration implementation.

#include "app/midi_config.h"
#include "app/config_parser.h"

#include <algorithm>
#include <cctype>
#include <string>

namespace legends {

namespace {

std::string toLowerStr(const std::string& s) {
    std::string result = s;
    std::transform(result.begin(), result.end(), result.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return result;
}

} // namespace

void MIDIConfig::loadFrom(const ConfigParser& config) {
    if (!config.hasSection("midi")) {
        return;
    }

    std::string dev_str = config.get("midi", "mididevice", "none");
    device = parseDeviceName(dev_str);

    soundfont_path = config.get("midi", "fluid.soundfont", soundfont_path);
    mt32_romdir = config.get("midi", "mt32.romdir", mt32_romdir);

    sample_rate = static_cast<uint32_t>(
        config.getInt("midi", "samplerate", static_cast<int>(sample_rate)));

    // Volume: read as integer percentage 0-100, convert to float 0.0-1.0;
    // or read as-is if stored as int (default 100 = 1.0).
    int vol_int = config.getInt("midi", "volume", 100);
    volume = static_cast<float>(vol_int) / 100.0f;
}

MIDIDevice MIDIConfig::parseDeviceName(const std::string& name) {
    std::string lower = toLowerStr(name);
    if (lower == "fluidsynth" || lower == "fluid") {
        return MIDIDevice::FluidSynth;
    }
    if (lower == "mt32" || lower == "mt-32") {
        return MIDIDevice::MT32;
    }
    if (lower == "synth") {
        return MIDIDevice::Synth;
    }
    // "none" or any unrecognised string
    return MIDIDevice::None;
}

const char* MIDIConfig::deviceName(MIDIDevice device) {
    switch (device) {
        case MIDIDevice::FluidSynth: return "fluidsynth";
        case MIDIDevice::MT32:       return "mt32";
        case MIDIDevice::Synth:      return "synth";
        default:                     return "none";
    }
}

bool MIDIConfig::isValid() const {
    switch (device) {
        case MIDIDevice::None:
            // No MIDI device configured — valid (just inactive).
            return true;
        case MIDIDevice::FluidSynth:
            return !soundfont_path.empty();
        case MIDIDevice::MT32:
            return !mt32_romdir.empty();
        case MIDIDevice::Synth:
            return true;
        default:
            return false;
    }
}

} // namespace legends
