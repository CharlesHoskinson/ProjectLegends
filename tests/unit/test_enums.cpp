/**
 * @file test_enums.cpp
 * @brief Unit tests for type-safe enum utilities.
 */

#include <gtest/gtest.h>
#include <legends/enums.h>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// VgaMode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VgaModeTest, ToStringReturnsCorrectName) {
    EXPECT_STREQ(to_string(VgaMode::Text80x25_Color), "Text80x25_Color");
    EXPECT_STREQ(to_string(VgaMode::Vga320x200_256), "Vga320x200_256");
    EXPECT_STREQ(to_string(VgaMode::Vga640x480), "Vga640x480");
}

TEST(VgaModeTest, ToStringHandlesInvalid) {
    EXPECT_STREQ(to_string(static_cast<VgaMode>(0xFF)), "Unknown");
}

TEST(VgaModeTest, IsValidForValidModes) {
    EXPECT_TRUE(is_valid(VgaMode::Text80x25_Color));
    EXPECT_TRUE(is_valid(VgaMode::Vga320x200_256));
    EXPECT_TRUE(is_valid(VgaMode::Cga320x200_4));
}

TEST(VgaModeTest, IsValidForInvalidModes) {
    EXPECT_FALSE(is_valid(static_cast<VgaMode>(0xFF)));
    EXPECT_FALSE(is_valid(static_cast<VgaMode>(0x20)));
}

TEST(VgaModeTest, ParseReturnsCorrectMode) {
    auto mode = parse_vga_mode("Vga320x200_256");
    EXPECT_TRUE(mode.has_value());
    EXPECT_EQ(*mode, VgaMode::Vga320x200_256);
}

TEST(VgaModeTest, ParseFromHexCode) {
    auto mode = parse_vga_mode("0x13");
    EXPECT_TRUE(mode.has_value());
    EXPECT_EQ(*mode, VgaMode::Vga320x200_256);
}

TEST(VgaModeTest, ParseMode13hAlias) {
    auto mode = parse_vga_mode("Mode13h");
    EXPECT_TRUE(mode.has_value());
    EXPECT_EQ(*mode, VgaMode::Vga320x200_256);
}

TEST(VgaModeTest, ParseReturnsNulloptForInvalid) {
    auto mode = parse_vga_mode("InvalidMode");
    EXPECT_FALSE(mode.has_value());
}

TEST(VgaModeTest, DimensionsForGraphicsModes) {
    auto [w, h] = get_mode_dimensions(VgaMode::Vga320x200_256);
    EXPECT_EQ(w, 320);
    EXPECT_EQ(h, 200);

    auto [w2, h2] = get_mode_dimensions(VgaMode::Vga640x480);
    EXPECT_EQ(w2, 640);
    EXPECT_EQ(h2, 480);
}

TEST(VgaModeTest, DimensionsForTextModes) {
    auto [w, h] = get_mode_dimensions(VgaMode::Text80x25_Color);
    EXPECT_EQ(w, 80);
    EXPECT_EQ(h, 25);
}

TEST(VgaModeTest, DimensionsForInvalidMode) {
    auto [w, h] = get_mode_dimensions(static_cast<VgaMode>(0xFF));
    EXPECT_EQ(w, 0);
    EXPECT_EQ(h, 0);
}

TEST(VgaModeTest, BppForModes) {
    EXPECT_EQ(get_mode_bpp(VgaMode::Vga320x200_256), 8);
    EXPECT_EQ(get_mode_bpp(VgaMode::Vga640x480), 4);
    EXPECT_EQ(get_mode_bpp(VgaMode::Cga320x200_4), 2);
}

TEST(VgaModeTest, IsTextModeForTextModes) {
    EXPECT_TRUE(is_text_mode(VgaMode::Text80x25_Color));
    EXPECT_TRUE(is_text_mode(VgaMode::Text40x25_Mono));
    EXPECT_TRUE(is_text_mode(VgaMode::Mda80x25));
}

TEST(VgaModeTest, IsTextModeForGraphicsModes) {
    EXPECT_FALSE(is_text_mode(VgaMode::Vga320x200_256));
    EXPECT_FALSE(is_text_mode(VgaMode::Cga320x200_4));
}

TEST(VgaModeTest, AllModesIteration) {
    for (auto mode : all_vga_modes) {
        EXPECT_TRUE(is_valid(mode)) << to_string(mode);
    }
    EXPECT_EQ(all_vga_modes.size(), 15u);
}

// ─────────────────────────────────────────────────────────────────────────────
// CpuMode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CpuModeEnumTest, ToStringReturnsCorrectName) {
    EXPECT_STREQ(to_string(CpuMode::Real), "Real");
    EXPECT_STREQ(to_string(CpuMode::Protected16), "Protected16");
    EXPECT_STREQ(to_string(CpuMode::Protected32), "Protected32");
    EXPECT_STREQ(to_string(CpuMode::Virtual8086), "Virtual8086");
}

TEST(CpuModeEnumTest, IsValidForValidModes) {
    EXPECT_TRUE(is_valid(CpuMode::Real));
    EXPECT_TRUE(is_valid(CpuMode::Protected16));
    EXPECT_TRUE(is_valid(CpuMode::Protected32));
    EXPECT_TRUE(is_valid(CpuMode::Virtual8086));
}

TEST(CpuModeEnumTest, ParseReturnsCorrectMode) {
    auto mode = parse_cpu_mode("Real");
    EXPECT_TRUE(mode.has_value());
    EXPECT_EQ(*mode, CpuMode::Real);
}

TEST(CpuModeEnumTest, ParseV86Alias) {
    auto mode = parse_cpu_mode("V86");
    EXPECT_TRUE(mode.has_value());
    EXPECT_EQ(*mode, CpuMode::Virtual8086);
}

TEST(CpuModeEnumTest, DefaultAddressSizeFor16BitModes) {
    EXPECT_EQ(default_address_size(CpuMode::Real), 16);
    EXPECT_EQ(default_address_size(CpuMode::Protected16), 16);
    EXPECT_EQ(default_address_size(CpuMode::Virtual8086), 16);
}

TEST(CpuModeEnumTest, DefaultAddressSizeFor32BitMode) {
    EXPECT_EQ(default_address_size(CpuMode::Protected32), 32);
}

TEST(CpuModeEnumTest, AllModesIteration) {
    for (auto mode : all_cpu_modes) {
        EXPECT_TRUE(is_valid(mode)) << to_string(mode);
    }
    EXPECT_EQ(all_cpu_modes.size(), 4u);
}

// ─────────────────────────────────────────────────────────────────────────────
// MachineType Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineTypeEnumTest, ToStringReturnsCorrectName) {
    EXPECT_STREQ(to_string(MachineType::VGA), "VGA");
    EXPECT_STREQ(to_string(MachineType::EGA), "EGA");
    EXPECT_STREQ(to_string(MachineType::CGA), "CGA");
    EXPECT_STREQ(to_string(MachineType::PC98), "PC98");
}

TEST(MachineTypeEnumTest, IsValidForValidTypes) {
    EXPECT_TRUE(is_valid(MachineType::VGA));
    EXPECT_TRUE(is_valid(MachineType::SVGA_S3));
    EXPECT_TRUE(is_valid(MachineType::Hercules));
}

TEST(MachineTypeEnumTest, ParseReturnsCorrectType) {
    auto type = parse_machine_type("VGA");
    EXPECT_TRUE(type.has_value());
    EXPECT_EQ(*type, MachineType::VGA);
}

TEST(MachineTypeEnumTest, ParseS3Alias) {
    auto type = parse_machine_type("S3");
    EXPECT_TRUE(type.has_value());
    EXPECT_EQ(*type, MachineType::SVGA_S3);
}

TEST(MachineTypeEnumTest, AllTypesIteration) {
    for (auto type : all_machine_types) {
        EXPECT_TRUE(is_valid(type)) << to_string(type);
    }
    EXPECT_EQ(all_machine_types.size(), 9u);
}

// ─────────────────────────────────────────────────────────────────────────────
// MachineState Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineStateEnumTest, ToStringReturnsCorrectName) {
    // Note: to_string already tested in test_machine_context.cpp
    EXPECT_STREQ(to_string(MachineState::Created), "Created");
    EXPECT_STREQ(to_string(MachineState::Running), "Running");
}

TEST(MachineStateEnumTest, IsValidForValidStates) {
    EXPECT_TRUE(is_valid(MachineState::Created));
    EXPECT_TRUE(is_valid(MachineState::Initialized));
    EXPECT_TRUE(is_valid(MachineState::Running));
    EXPECT_TRUE(is_valid(MachineState::Shutdown));
}

TEST(MachineStateEnumTest, ParseReturnsCorrectState) {
    auto state = parse_machine_state("Running");
    EXPECT_TRUE(state.has_value());
    EXPECT_EQ(*state, MachineState::Running);
}

TEST(MachineStateEnumTest, AllStatesIteration) {
    for (auto state : all_machine_states) {
        EXPECT_TRUE(is_valid(state)) << to_string(state);
    }
    EXPECT_EQ(all_machine_states.size(), 7u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Constexpr Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(EnumConstexprTest, ToStringIsConstexpr) {
    constexpr const char* name = to_string(VgaMode::Vga320x200_256);
    EXPECT_STREQ(name, "Vga320x200_256");
}

TEST(EnumConstexprTest, IsValidIsConstexpr) {
    constexpr bool valid = is_valid(CpuMode::Real);
    EXPECT_TRUE(valid);
}

TEST(EnumConstexprTest, DimensionsAreConstexpr) {
    constexpr auto dims = get_mode_dimensions(VgaMode::Vga320x200_256);
    EXPECT_EQ(dims.first, 320);
    EXPECT_EQ(dims.second, 200);
}

TEST(EnumConstexprTest, DefaultAddressSizeIsConstexpr) {
    constexpr int size = default_address_size(CpuMode::Protected32);
    EXPECT_EQ(size, 32);
}

TEST(EnumConstexprTest, AllArraysAreConstexpr) {
    constexpr auto first_mode = all_vga_modes[0];
    EXPECT_EQ(first_mode, VgaMode::Text40x25_Mono);
}
