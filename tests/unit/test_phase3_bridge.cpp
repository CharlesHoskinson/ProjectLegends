// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for Phase 3 Enhanced Features bridge layer.
// Tests the legends_*() C API functions that bridge to dosbox_lib_*() functions.

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <cstdint>

// ═══════════════════════════════════════════════════════════════════════════════
// PC-98 Machine Type
// ═══════════════════════════════════════════════════════════════════════════════

TEST(Phase3BridgeTest, SetPC98_NullHandle) {
    EXPECT_EQ(legends_set_machine_pc98(nullptr, 1), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, IsPC98_NullHandle) {
    int out = 0;
    EXPECT_EQ(legends_is_pc98_mode(nullptr, &out), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, IsPC98_NullPointer) {
    EXPECT_EQ(legends_is_pc98_mode(nullptr, nullptr), LEGENDS_ERR_NULL_HANDLE);
}

// ═══════════════════════════════════════════════════════════════════════════════
// 3dfx Glide
// ═══════════════════════════════════════════════════════════════════════════════

TEST(Phase3BridgeTest, GlideEnable_NullHandle) {
    EXPECT_EQ(legends_glide_enable(nullptr, 1), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, GlideSetResolution_NullHandle) {
    EXPECT_EQ(legends_glide_set_resolution(nullptr, 800, 600), LEGENDS_ERR_NULL_HANDLE);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Printer
// ═══════════════════════════════════════════════════════════════════════════════

TEST(Phase3BridgeTest, PrinterSetOutput_NullHandle) {
    EXPECT_EQ(legends_printer_set_output(nullptr, "/tmp/out"), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, PrinterSetOutput_NullPath) {
    EXPECT_EQ(legends_printer_set_output(nullptr, nullptr), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, PrinterIsActive_NullHandle) {
    int out = 0;
    EXPECT_EQ(legends_printer_is_active(nullptr, &out), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, PrinterIsActive_NullPointer) {
    EXPECT_EQ(legends_printer_is_active(nullptr, nullptr), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, PrinterFlush_NullHandle) {
    EXPECT_EQ(legends_printer_flush(nullptr), LEGENDS_ERR_NULL_HANDLE);
}

// ═══════════════════════════════════════════════════════════════════════════════
// IPX Networking
// ═══════════════════════════════════════════════════════════════════════════════

TEST(Phase3BridgeTest, IPXEnable_NullHandle) {
    EXPECT_EQ(legends_ipx_enable(nullptr, 1), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, IPXConnect_NullHandle) {
    EXPECT_EQ(legends_ipx_connect(nullptr, "localhost", 213), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, IPXConnect_NullServer) {
    EXPECT_EQ(legends_ipx_connect(nullptr, nullptr, 213), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, IPXDisconnect_NullHandle) {
    EXPECT_EQ(legends_ipx_disconnect(nullptr), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, IPXIsConnected_NullHandle) {
    int out = 0;
    EXPECT_EQ(legends_ipx_is_connected(nullptr, &out), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, IPXIsConnected_NullPointer) {
    EXPECT_EQ(legends_ipx_is_connected(nullptr, nullptr), LEGENDS_ERR_NULL_HANDLE);
}

// ═══════════════════════════════════════════════════════════════════════════════
// MIDI & Synthesis
// ═══════════════════════════════════════════════════════════════════════════════

TEST(Phase3BridgeTest, MIDISetDevice_NullHandle) {
    EXPECT_EQ(legends_midi_set_device(nullptr, "fluidsynth"), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, MIDISetDevice_NullDevice) {
    EXPECT_EQ(legends_midi_set_device(nullptr, nullptr), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, MIDISetSoundfont_NullHandle) {
    EXPECT_EQ(legends_midi_set_soundfont(nullptr, "/path/to/sf2"), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, MIDISetSoundfont_NullPath) {
    EXPECT_EQ(legends_midi_set_soundfont(nullptr, nullptr), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, MIDISetRomdir_NullHandle) {
    EXPECT_EQ(legends_midi_set_romdir(nullptr, "/path/to/roms"), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, MIDICapture_NullHandle) {
    size_t out = 0;
    EXPECT_EQ(legends_capture_midi_audio(nullptr, nullptr, 0, &out), LEGENDS_ERR_NULL_HANDLE);
}

TEST(Phase3BridgeTest, MIDICapture_NullOut) {
    EXPECT_EQ(legends_capture_midi_audio(nullptr, nullptr, 0, nullptr), LEGENDS_ERR_NULL_HANDLE);
}
