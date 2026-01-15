/**
 * @file test_dosbox_vga.cpp
 * @brief Unit tests for DOSBox VGA state migration (PR #13).
 *
 * Tests:
 * - VgaMode and SvgaChip enumerations
 * - VgaState struct fields
 * - VGA state reset
 * - State hash includes VGA state
 * - Determinism: same VGA state = same hash
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Enumeration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(VgaModeTest, EnumValues) {
    // Verify enum values match expected constants
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::Text), 0);
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::CGA2), 1);
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::CGA4), 2);
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::EGA), 3);
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::VGA), 4);
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::LIN8), 6);
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::LIN32), 10);
    EXPECT_EQ(static_cast<uint8_t>(VgaMode::Error), 255);
}

TEST(SvgaChipTest, EnumValues) {
    EXPECT_EQ(static_cast<uint8_t>(SvgaChip::None), 0);
    EXPECT_EQ(static_cast<uint8_t>(SvgaChip::S3Trio), 1);
    EXPECT_EQ(static_cast<uint8_t>(SvgaChip::TsengET4K), 2);
    EXPECT_EQ(static_cast<uint8_t>(SvgaChip::Other), 255);
}

// ═══════════════════════════════════════════════════════════════════════════════
// VgaState Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(VgaStateTest, DefaultValues) {
    VgaState vga;

    // Display mode configuration
    EXPECT_EQ(vga.width, 640);
    EXPECT_EQ(vga.height, 480);
    EXPECT_EQ(vga.bpp, 8);
    EXPECT_EQ(vga.mode, VgaMode::VGA);
    EXPECT_EQ(vga.svga_chip, SvgaChip::None);

    // Timing
    EXPECT_DOUBLE_EQ(vga.refresh_rate, 70.0);
    EXPECT_DOUBLE_EQ(vga.fps, 0.0);
    EXPECT_EQ(vga.frame_counter, 0u);

    // Rendering flags
    EXPECT_FALSE(vga.render_on_demand);
    EXPECT_FALSE(vga.render_wait_for_changes);

    // Hardware configuration
    EXPECT_FALSE(vga.dac_8bit);
    EXPECT_FALSE(vga.pci_enabled);
    EXPECT_TRUE(vga.vbe_enabled);

    // VESA capabilities (all true by default except hd)
    EXPECT_TRUE(vga.vesa_32bpp);
    EXPECT_TRUE(vga.vesa_24bpp);
    EXPECT_TRUE(vga.vesa_16bpp);
    EXPECT_TRUE(vga.vesa_15bpp);
    EXPECT_TRUE(vga.vesa_8bpp);
    EXPECT_TRUE(vga.vesa_4bpp);
    EXPECT_TRUE(vga.vesa_lowres);
    EXPECT_FALSE(vga.vesa_hd);

    // Display state
    EXPECT_TRUE(vga.text_mode);
    EXPECT_FALSE(vga.page_flip_occurred);
    EXPECT_FALSE(vga.retrace_poll);

    // CGA/EGA
    EXPECT_FALSE(vga.cga_snow);
    EXPECT_FALSE(vga.ega_mode);
}

TEST(VgaStateTest, Reset) {
    VgaState vga;

    // Set non-default values
    vga.width = 1920;
    vga.height = 1080;
    vga.bpp = 32;
    vga.mode = VgaMode::LIN32;
    vga.svga_chip = SvgaChip::S3Trio;
    vga.refresh_rate = 60.0;
    vga.fps = 59.94;
    vga.frame_counter = 10000;
    vga.render_on_demand = true;
    vga.render_wait_for_changes = true;
    vga.dac_8bit = true;
    vga.pci_enabled = true;
    vga.vbe_enabled = false;
    vga.vesa_32bpp = false;
    vga.vesa_hd = true;
    vga.text_mode = false;
    vga.page_flip_occurred = true;
    vga.retrace_poll = true;
    vga.cga_snow = true;
    vga.ega_mode = true;

    // Reset
    vga.reset();

    // Verify all fields reset to defaults
    EXPECT_EQ(vga.width, 640);
    EXPECT_EQ(vga.height, 480);
    EXPECT_EQ(vga.bpp, 8);
    EXPECT_EQ(vga.mode, VgaMode::VGA);
    EXPECT_EQ(vga.svga_chip, SvgaChip::None);
    EXPECT_DOUBLE_EQ(vga.refresh_rate, 70.0);
    EXPECT_DOUBLE_EQ(vga.fps, 0.0);
    EXPECT_EQ(vga.frame_counter, 0u);
    EXPECT_FALSE(vga.render_on_demand);
    EXPECT_FALSE(vga.render_wait_for_changes);
    EXPECT_FALSE(vga.dac_8bit);
    EXPECT_FALSE(vga.pci_enabled);
    EXPECT_TRUE(vga.vbe_enabled);
    EXPECT_TRUE(vga.vesa_32bpp);
    EXPECT_FALSE(vga.vesa_hd);
    EXPECT_TRUE(vga.text_mode);
    EXPECT_FALSE(vga.page_flip_occurred);
    EXPECT_FALSE(vga.retrace_poll);
    EXPECT_FALSE(vga.cga_snow);
    EXPECT_FALSE(vga.ega_mode);
}

TEST(VgaStateTest, HashInto) {
    VgaState vga1;
    VgaState vga2;

    vga1.width = 800;
    vga1.height = 600;
    vga1.mode = VgaMode::LIN8;
    vga1.frame_counter = 100;

    vga2.width = 800;
    vga2.height = 600;
    vga2.mode = VgaMode::LIN8;
    vga2.frame_counter = 100;

    // Same state should produce same hash
    HashBuilder builder1;
    vga1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    vga2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);

    // Different state should produce different hash
    vga2.frame_counter = 200;

    HashBuilder builder3;
    vga2.hash_into(builder3);
    auto hash3 = builder3.finalize();

    EXPECT_NE(hash1, hash3);
}

TEST(VgaStateTest, HashExcludesFps) {
    VgaState vga1;
    VgaState vga2;

    // Same determinism-relevant state
    vga1.width = 800;
    vga1.height = 600;
    vga1.frame_counter = 100;

    vga2.width = 800;
    vga2.height = 600;
    vga2.frame_counter = 100;

    // Different fps (should NOT affect hash - derived from timing)
    vga1.fps = 60.0;
    vga2.fps = 59.94;

    // Hashes should be the same (fps excluded)
    HashBuilder builder1;
    vga1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    vga2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);
}

TEST(VgaStateTest, HashIncludesAllDeterminismFields) {
    VgaState base;
    base.width = 640;
    base.height = 480;

    HashBuilder base_builder;
    base.hash_into(base_builder);
    auto base_hash = base_builder.finalize();

    auto test_field_affects_hash = [&base, &base_hash](auto modifier) {
        VgaState modified = base;
        modifier(modified);

        HashBuilder builder;
        modified.hash_into(builder);
        auto hash = builder.finalize();

        EXPECT_NE(base_hash, hash);
    };

    // Test display mode
    test_field_affects_hash([](VgaState& v) { v.width++; });
    test_field_affects_hash([](VgaState& v) { v.height++; });
    test_field_affects_hash([](VgaState& v) { v.bpp++; });
    test_field_affects_hash([](VgaState& v) { v.mode = VgaMode::EGA; });
    test_field_affects_hash([](VgaState& v) { v.svga_chip = SvgaChip::S3Trio; });

    // Test timing
    test_field_affects_hash([](VgaState& v) { v.refresh_rate += 1.0; });
    test_field_affects_hash([](VgaState& v) { v.frame_counter++; });

    // Test rendering flags
    test_field_affects_hash([](VgaState& v) { v.render_on_demand = !v.render_on_demand; });
    test_field_affects_hash([](VgaState& v) { v.render_wait_for_changes = !v.render_wait_for_changes; });

    // Test hardware config
    test_field_affects_hash([](VgaState& v) { v.dac_8bit = !v.dac_8bit; });
    test_field_affects_hash([](VgaState& v) { v.pci_enabled = !v.pci_enabled; });
    test_field_affects_hash([](VgaState& v) { v.vbe_enabled = !v.vbe_enabled; });

    // Test VESA capabilities
    test_field_affects_hash([](VgaState& v) { v.vesa_32bpp = !v.vesa_32bpp; });
    test_field_affects_hash([](VgaState& v) { v.vesa_24bpp = !v.vesa_24bpp; });
    test_field_affects_hash([](VgaState& v) { v.vesa_16bpp = !v.vesa_16bpp; });
    test_field_affects_hash([](VgaState& v) { v.vesa_15bpp = !v.vesa_15bpp; });
    test_field_affects_hash([](VgaState& v) { v.vesa_8bpp = !v.vesa_8bpp; });
    test_field_affects_hash([](VgaState& v) { v.vesa_4bpp = !v.vesa_4bpp; });
    test_field_affects_hash([](VgaState& v) { v.vesa_lowres = !v.vesa_lowres; });
    test_field_affects_hash([](VgaState& v) { v.vesa_hd = !v.vesa_hd; });

    // Test display state
    test_field_affects_hash([](VgaState& v) { v.text_mode = !v.text_mode; });
    test_field_affects_hash([](VgaState& v) { v.page_flip_occurred = !v.page_flip_occurred; });
    test_field_affects_hash([](VgaState& v) { v.retrace_poll = !v.retrace_poll; });

    // Test CGA/EGA
    test_field_affects_hash([](VgaState& v) { v.cga_snow = !v.cga_snow; });
    test_field_affects_hash([](VgaState& v) { v.ega_mode = !v.ega_mode; });
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash with VGA Context Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(VgaHashTest, HashChangesWithVgaState) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    // Get initial hash
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify VGA state
    ctx.vga.width = 800;
    ctx.vga.height = 600;
    ctx.vga.frame_counter = 100;

    // Get new hash
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    // Hashes should be different
    EXPECT_NE(hash1, hash2);
}

TEST(VgaHashTest, SameVgaStateProducesSameHash) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;

    ctx1.initialize();
    ctx2.initialize();

    // Set same VGA values
    ctx1.vga.width = 1024;
    ctx1.vga.height = 768;
    ctx1.vga.mode = VgaMode::LIN8;
    ctx1.vga.frame_counter = 500;

    ctx2.vga.width = 1024;
    ctx2.vga.height = 768;
    ctx2.vga.mode = VgaMode::LIN8;
    ctx2.vga.frame_counter = 500;

    // Get hash with ctx1
    {
        ContextGuard guard(ctx1);
        auto result1 = get_state_hash(HashMode::Fast);
        ASSERT_TRUE(result1.has_value());

        // Get hash with ctx2
        set_current_context(&ctx2);
        auto result2 = get_state_hash(HashMode::Fast);
        ASSERT_TRUE(result2.has_value());

        // Should be same
        EXPECT_EQ(result1.value(), result2.value());
    }
}

TEST(VgaHashTest, ModeChangeAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    // Start in text mode
    ctx.vga.mode = VgaMode::Text;
    ctx.vga.text_mode = true;

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Switch to graphics mode
    ctx.vga.mode = VgaMode::VGA;
    ctx.vga.text_mode = false;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

TEST(VgaHashTest, VesaConfigAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Disable 32bpp VESA
    ctx.vga.vesa_32bpp = false;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context VGA Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextVgaTest, ResetClearsVgaState) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Modify VGA state
    ctx.vga.width = 1920;
    ctx.vga.height = 1080;
    ctx.vga.mode = VgaMode::LIN32;
    ctx.vga.frame_counter = 10000;
    ctx.vga.page_flip_occurred = true;

    // Reset
    ctx.reset();

    // VGA state should be reset
    EXPECT_EQ(ctx.vga.width, 640);
    EXPECT_EQ(ctx.vga.height, 480);
    EXPECT_EQ(ctx.vga.mode, VgaMode::VGA);
    EXPECT_EQ(ctx.vga.frame_counter, 0u);
    EXPECT_FALSE(ctx.vga.page_flip_occurred);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Combined All Subsystems Hash Test
// ═══════════════════════════════════════════════════════════════════════════════

TEST(CombinedHashTest, AllFourSubsystemsAffectHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify only timing
    ctx.timing.total_cycles += 1000;
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();
    EXPECT_NE(hash1, hash2);

    // Reset timing, modify only CPU
    ctx.timing.total_cycles -= 1000;
    ctx.cpu_state.cycles += 1000;
    auto result3 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result3.has_value());
    auto hash3 = result3.value();
    EXPECT_NE(hash1, hash3);

    // Reset CPU, modify only mixer
    ctx.cpu_state.cycles -= 1000;
    ctx.mixer.sample_counter += 1000;
    auto result4 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result4.has_value());
    auto hash4 = result4.value();
    EXPECT_NE(hash1, hash4);

    // Reset mixer, modify only VGA
    ctx.mixer.sample_counter -= 1000;
    ctx.vga.frame_counter += 100;
    auto result5 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result5.has_value());
    auto hash5 = result5.value();
    EXPECT_NE(hash1, hash5);

    // All hashes should be different
    EXPECT_NE(hash2, hash3);
    EXPECT_NE(hash2, hash4);
    EXPECT_NE(hash2, hash5);
    EXPECT_NE(hash3, hash4);
    EXPECT_NE(hash3, hash5);
    EXPECT_NE(hash4, hash5);
}

TEST(CombinedHashTest, DeterministicWithAllFourSubsystems) {
    ContextConfig config;
    config.cpu_cycles = 3000;
    config.sound_enabled = true;

    // Create two contexts with same config
    DOSBoxContext ctx1(config);
    DOSBoxContext ctx2(config);

    ctx1.initialize();
    ctx2.initialize();

    // Set same state in all subsystems
    ctx1.timing.total_cycles = 10000;
    ctx1.cpu_state.cycles = 5000;
    ctx1.mixer.sample_counter = 2000;
    ctx1.vga.frame_counter = 100;
    ctx1.vga.width = 800;
    ctx1.vga.height = 600;

    ctx2.timing.total_cycles = 10000;
    ctx2.cpu_state.cycles = 5000;
    ctx2.mixer.sample_counter = 2000;
    ctx2.vga.frame_counter = 100;
    ctx2.vga.width = 800;
    ctx2.vga.height = 600;

    // Get hashes
    set_current_context(&ctx1);
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());

    set_current_context(&ctx2);
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());

    // Hashes should be identical (deterministic)
    EXPECT_EQ(result1.value(), result2.value());

    // Clean up
    set_current_context(nullptr);
}
