// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for MIDIConfig.

#include <gtest/gtest.h>
#include "app/midi_config.h"

#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Default values
// ═══════════════════════════════════════════════════════════════════════════

TEST(MIDIConfigTest, DefaultDeviceIsNone) {
    MIDIConfig config;
    EXPECT_EQ(config.device, MIDIDevice::None);
}

TEST(MIDIConfigTest, DefaultSampleRate) {
    MIDIConfig config;
    EXPECT_EQ(config.sample_rate, 44100u);
}

TEST(MIDIConfigTest, DefaultVolume) {
    MIDIConfig config;
    EXPECT_FLOAT_EQ(config.volume, 1.0f);
}

TEST(MIDIConfigTest, DefaultSoundfontPathEmpty) {
    MIDIConfig config;
    EXPECT_TRUE(config.soundfont_path.empty());
}

TEST(MIDIConfigTest, DefaultMT32RomdirEmpty) {
    MIDIConfig config;
    EXPECT_TRUE(config.mt32_romdir.empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// parseDeviceName
// ═══════════════════════════════════════════════════════════════════════════

TEST(MIDIConfigTest, ParseDeviceName_None) {
    EXPECT_EQ(MIDIConfig::parseDeviceName("none"), MIDIDevice::None);
}

TEST(MIDIConfigTest, ParseDeviceName_FluidSynth) {
    EXPECT_EQ(MIDIConfig::parseDeviceName("fluidsynth"), MIDIDevice::FluidSynth);
}

TEST(MIDIConfigTest, ParseDeviceName_MT32) {
    EXPECT_EQ(MIDIConfig::parseDeviceName("mt32"), MIDIDevice::MT32);
}

TEST(MIDIConfigTest, ParseDeviceName_Synth) {
    EXPECT_EQ(MIDIConfig::parseDeviceName("synth"), MIDIDevice::Synth);
}

TEST(MIDIConfigTest, ParseDeviceName_CaseInsensitive) {
    EXPECT_EQ(MIDIConfig::parseDeviceName("FluidSynth"), MIDIDevice::FluidSynth);
    EXPECT_EQ(MIDIConfig::parseDeviceName("FLUIDSYNTH"), MIDIDevice::FluidSynth);
    EXPECT_EQ(MIDIConfig::parseDeviceName("MT32"), MIDIDevice::MT32);
    EXPECT_EQ(MIDIConfig::parseDeviceName("Synth"), MIDIDevice::Synth);
    EXPECT_EQ(MIDIConfig::parseDeviceName("NONE"), MIDIDevice::None);
}

TEST(MIDIConfigTest, ParseDeviceName_UnknownReturnsNone) {
    EXPECT_EQ(MIDIConfig::parseDeviceName("unknown"), MIDIDevice::None);
    EXPECT_EQ(MIDIConfig::parseDeviceName("garbage"), MIDIDevice::None);
    EXPECT_EQ(MIDIConfig::parseDeviceName(""), MIDIDevice::None);
}

// ═══════════════════════════════════════════════════════════════════════════
// deviceName
// ═══════════════════════════════════════════════════════════════════════════

TEST(MIDIConfigTest, DeviceName_None) {
    EXPECT_STREQ(MIDIConfig::deviceName(MIDIDevice::None), "none");
}

TEST(MIDIConfigTest, DeviceName_RoundTrip) {
    auto check = [](MIDIDevice dev) {
        const char* name = MIDIConfig::deviceName(dev);
        EXPECT_EQ(MIDIConfig::parseDeviceName(name), dev)
            << "Round-trip failed for: " << name;
    };
    check(MIDIDevice::None);
    check(MIDIDevice::FluidSynth);
    check(MIDIDevice::MT32);
    check(MIDIDevice::Synth);
}

// ═══════════════════════════════════════════════════════════════════════════
// isValid
// ═══════════════════════════════════════════════════════════════════════════

TEST(MIDIConfigTest, IsValid_NoneDevice_ReturnsTrue) {
    MIDIConfig config;
    config.device = MIDIDevice::None;
    EXPECT_TRUE(config.isValid());
}

TEST(MIDIConfigTest, IsValid_FluidSynth_WithSoundfont) {
    MIDIConfig config;
    config.device = MIDIDevice::FluidSynth;
    config.soundfont_path = "/path/to/soundfont.sf2";
    EXPECT_TRUE(config.isValid());
}

TEST(MIDIConfigTest, IsValid_FluidSynth_WithoutSoundfont) {
    MIDIConfig config;
    config.device = MIDIDevice::FluidSynth;
    config.soundfont_path.clear();
    EXPECT_FALSE(config.isValid());
}

TEST(MIDIConfigTest, IsValid_MT32_WithRomdir) {
    MIDIConfig config;
    config.device = MIDIDevice::MT32;
    config.mt32_romdir = "/path/to/roms";
    EXPECT_TRUE(config.isValid());
}

TEST(MIDIConfigTest, IsValid_MT32_WithoutRomdir) {
    MIDIConfig config;
    config.device = MIDIDevice::MT32;
    config.mt32_romdir.clear();
    EXPECT_FALSE(config.isValid());
}

TEST(MIDIConfigTest, IsValid_Synth_AlwaysValid) {
    MIDIConfig config;
    config.device = MIDIDevice::Synth;
    EXPECT_TRUE(config.isValid());
}

// ═══════════════════════════════════════════════════════════════════════════
// Multiple config loads
// ═══════════════════════════════════════════════════════════════════════════

TEST(MIDIConfigTest, MultipleConfigsIndependent) {
    MIDIConfig a;
    a.device = MIDIDevice::FluidSynth;
    a.soundfont_path = "/a.sf2";

    MIDIConfig b;
    b.device = MIDIDevice::MT32;
    b.mt32_romdir = "/b/roms";

    EXPECT_EQ(a.device, MIDIDevice::FluidSynth);
    EXPECT_EQ(b.device, MIDIDevice::MT32);
    EXPECT_EQ(a.soundfont_path, "/a.sf2");
    EXPECT_TRUE(b.soundfont_path.empty());
}

} // namespace
} // namespace legends
