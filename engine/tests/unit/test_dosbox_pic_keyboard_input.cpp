/**
 * @file test_dosbox_pic_keyboard_input.cpp
 * @brief Unit tests for DOSBox PIC, Keyboard, and Input state migration (PR #14).
 *
 * Tests:
 * - PicState struct fields and reset
 * - KeyboardState struct fields and reset
 * - InputCaptureState struct fields and reset
 * - State hash includes all three subsystems
 * - Determinism: same state = same hash
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// PicState Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(PicStateTest, DefaultValues) {
    PicState pic;

    // Tick counter
    EXPECT_EQ(pic.ticks, 0u);

    // IRQ state
    EXPECT_EQ(pic.irq_check, 0u);
    EXPECT_EQ(pic.irq_check_pending, 0u);

    // Cascade configuration
    EXPECT_EQ(pic.master_cascade_irq, 2);

    // Event service state
    EXPECT_FALSE(pic.in_event_service);
    EXPECT_DOUBLE_EQ(pic.srv_lag, 0.0);

    // IRQ timing
    EXPECT_EQ(pic.irq_delay_ns, 0u);

    // Controller state
    EXPECT_EQ(pic.master_imr, 0xFF);
    EXPECT_EQ(pic.slave_imr, 0xFF);
    EXPECT_EQ(pic.master_isr, 0);
    EXPECT_EQ(pic.slave_isr, 0);
    EXPECT_FALSE(pic.auto_eoi);
}

TEST(PicStateTest, Reset) {
    PicState pic;

    // Set non-default values
    pic.ticks = 100000;
    pic.irq_check = 0x1234;
    pic.irq_check_pending = 0x5678;
    pic.master_cascade_irq = 4;
    pic.in_event_service = true;
    pic.srv_lag = 123.456;
    pic.irq_delay_ns = 1000;
    pic.master_imr = 0x00;
    pic.slave_imr = 0x00;
    pic.master_isr = 0x80;
    pic.slave_isr = 0x40;
    pic.auto_eoi = true;

    // Reset
    pic.reset();

    // Verify all fields reset to defaults
    EXPECT_EQ(pic.ticks, 0u);
    EXPECT_EQ(pic.irq_check, 0u);
    EXPECT_EQ(pic.irq_check_pending, 0u);
    EXPECT_EQ(pic.master_cascade_irq, 2);
    EXPECT_FALSE(pic.in_event_service);
    EXPECT_DOUBLE_EQ(pic.srv_lag, 0.0);
    EXPECT_EQ(pic.irq_delay_ns, 0u);
    EXPECT_EQ(pic.master_imr, 0xFF);
    EXPECT_EQ(pic.slave_imr, 0xFF);
    EXPECT_EQ(pic.master_isr, 0);
    EXPECT_EQ(pic.slave_isr, 0);
    EXPECT_FALSE(pic.auto_eoi);
}

TEST(PicStateTest, HashInto) {
    PicState pic1;
    PicState pic2;

    pic1.ticks = 1000;
    pic1.irq_check = 0x01;
    pic1.master_imr = 0xFE;

    pic2.ticks = 1000;
    pic2.irq_check = 0x01;
    pic2.master_imr = 0xFE;

    // Same state should produce same hash
    HashBuilder builder1;
    pic1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    pic2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);

    // Different state should produce different hash
    pic2.ticks = 2000;

    HashBuilder builder3;
    pic2.hash_into(builder3);
    auto hash3 = builder3.finalize();

    EXPECT_NE(hash1, hash3);
}

TEST(PicStateTest, HashIncludesAllFields) {
    PicState base;

    HashBuilder base_builder;
    base.hash_into(base_builder);
    auto base_hash = base_builder.finalize();

    auto test_field_affects_hash = [&base, &base_hash](auto modifier) {
        PicState modified = base;
        modifier(modified);

        HashBuilder builder;
        modified.hash_into(builder);
        auto hash = builder.finalize();

        EXPECT_NE(base_hash, hash);
    };

    // Test all fields
    test_field_affects_hash([](PicState& p) { p.ticks++; });
    test_field_affects_hash([](PicState& p) { p.irq_check++; });
    test_field_affects_hash([](PicState& p) { p.irq_check_pending++; });
    test_field_affects_hash([](PicState& p) { p.master_cascade_irq++; });
    test_field_affects_hash([](PicState& p) { p.in_event_service = !p.in_event_service; });
    test_field_affects_hash([](PicState& p) { p.srv_lag += 1.0; });
    test_field_affects_hash([](PicState& p) { p.irq_delay_ns++; });
    test_field_affects_hash([](PicState& p) { p.master_imr--; });
    test_field_affects_hash([](PicState& p) { p.slave_imr--; });
    test_field_affects_hash([](PicState& p) { p.master_isr++; });
    test_field_affects_hash([](PicState& p) { p.slave_isr++; });
    test_field_affects_hash([](PicState& p) { p.auto_eoi = !p.auto_eoi; });
}

// ═══════════════════════════════════════════════════════════════════════════════
// KeyboardState Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(KeyboardStateTest, DefaultValues) {
    KeyboardState kb;

    // Scan code state
    EXPECT_EQ(kb.scanset, 2);
    EXPECT_TRUE(kb.enabled);
    EXPECT_TRUE(kb.active);

    // Buffer state
    EXPECT_EQ(kb.buffer_size, 0);
    EXPECT_EQ(kb.buffer_pos, 0);

    // Lock state
    EXPECT_FALSE(kb.num_lock);
    EXPECT_FALSE(kb.caps_lock);
    EXPECT_FALSE(kb.scroll_lock);

    // Command state
    EXPECT_EQ(kb.command, 0);
    EXPECT_FALSE(kb.expecting_data);

    // PS/2 controller state
    EXPECT_FALSE(kb.ps2_mouse_enabled);
    EXPECT_TRUE(kb.a20_gate);
}

TEST(KeyboardStateTest, Reset) {
    KeyboardState kb;

    // Set non-default values
    kb.scanset = 1;
    kb.enabled = false;
    kb.active = false;
    kb.buffer_size = 16;
    kb.buffer_pos = 8;
    kb.num_lock = true;
    kb.caps_lock = true;
    kb.scroll_lock = true;
    kb.command = 0xF0;
    kb.expecting_data = true;
    kb.ps2_mouse_enabled = true;
    kb.a20_gate = false;

    // Reset
    kb.reset();

    // Verify all fields reset to defaults
    EXPECT_EQ(kb.scanset, 2);
    EXPECT_TRUE(kb.enabled);
    EXPECT_TRUE(kb.active);
    EXPECT_EQ(kb.buffer_size, 0);
    EXPECT_EQ(kb.buffer_pos, 0);
    EXPECT_FALSE(kb.num_lock);
    EXPECT_FALSE(kb.caps_lock);
    EXPECT_FALSE(kb.scroll_lock);
    EXPECT_EQ(kb.command, 0);
    EXPECT_FALSE(kb.expecting_data);
    EXPECT_FALSE(kb.ps2_mouse_enabled);
    EXPECT_TRUE(kb.a20_gate);
}

TEST(KeyboardStateTest, HashInto) {
    KeyboardState kb1;
    KeyboardState kb2;

    kb1.scanset = 1;
    kb1.num_lock = true;
    kb1.buffer_size = 5;

    kb2.scanset = 1;
    kb2.num_lock = true;
    kb2.buffer_size = 5;

    // Same state should produce same hash
    HashBuilder builder1;
    kb1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    kb2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);

    // Different state should produce different hash
    kb2.scanset = 3;

    HashBuilder builder3;
    kb2.hash_into(builder3);
    auto hash3 = builder3.finalize();

    EXPECT_NE(hash1, hash3);
}

TEST(KeyboardStateTest, HashIncludesAllFields) {
    KeyboardState base;

    HashBuilder base_builder;
    base.hash_into(base_builder);
    auto base_hash = base_builder.finalize();

    auto test_field_affects_hash = [&base, &base_hash](auto modifier) {
        KeyboardState modified = base;
        modifier(modified);

        HashBuilder builder;
        modified.hash_into(builder);
        auto hash = builder.finalize();

        EXPECT_NE(base_hash, hash);
    };

    // Test all fields
    test_field_affects_hash([](KeyboardState& k) { k.scanset = 1; });
    test_field_affects_hash([](KeyboardState& k) { k.enabled = !k.enabled; });
    test_field_affects_hash([](KeyboardState& k) { k.active = !k.active; });
    test_field_affects_hash([](KeyboardState& k) { k.buffer_size++; });
    test_field_affects_hash([](KeyboardState& k) { k.buffer_pos++; });
    test_field_affects_hash([](KeyboardState& k) { k.num_lock = !k.num_lock; });
    test_field_affects_hash([](KeyboardState& k) { k.caps_lock = !k.caps_lock; });
    test_field_affects_hash([](KeyboardState& k) { k.scroll_lock = !k.scroll_lock; });
    test_field_affects_hash([](KeyboardState& k) { k.command++; });
    test_field_affects_hash([](KeyboardState& k) { k.expecting_data = !k.expecting_data; });
    test_field_affects_hash([](KeyboardState& k) { k.ps2_mouse_enabled = !k.ps2_mouse_enabled; });
    test_field_affects_hash([](KeyboardState& k) { k.a20_gate = !k.a20_gate; });
}

// ═══════════════════════════════════════════════════════════════════════════════
// InputCaptureState Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(InputCaptureStateTest, DefaultValues) {
    InputCaptureState input;

    EXPECT_FALSE(input.captured_num_lock);
    EXPECT_FALSE(input.captured_caps_lock);
    EXPECT_FALSE(input.input_captured);
}

TEST(InputCaptureStateTest, Reset) {
    InputCaptureState input;

    // Set non-default values
    input.captured_num_lock = true;
    input.captured_caps_lock = true;
    input.input_captured = true;

    // Reset
    input.reset();

    // Verify all fields reset to defaults
    EXPECT_FALSE(input.captured_num_lock);
    EXPECT_FALSE(input.captured_caps_lock);
    EXPECT_FALSE(input.input_captured);
}

TEST(InputCaptureStateTest, HashInto) {
    InputCaptureState input1;
    InputCaptureState input2;

    input1.input_captured = true;
    input1.captured_num_lock = true;

    input2.input_captured = true;
    input2.captured_num_lock = true;

    // Same state should produce same hash
    HashBuilder builder1;
    input1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    input2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);

    // Different state should produce different hash
    input2.captured_caps_lock = true;

    HashBuilder builder3;
    input2.hash_into(builder3);
    auto hash3 = builder3.finalize();

    EXPECT_NE(hash1, hash3);
}

TEST(InputCaptureStateTest, HashIncludesAllFields) {
    InputCaptureState base;

    HashBuilder base_builder;
    base.hash_into(base_builder);
    auto base_hash = base_builder.finalize();

    auto test_field_affects_hash = [&base, &base_hash](auto modifier) {
        InputCaptureState modified = base;
        modifier(modified);

        HashBuilder builder;
        modified.hash_into(builder);
        auto hash = builder.finalize();

        EXPECT_NE(base_hash, hash);
    };

    // Test all fields
    test_field_affects_hash([](InputCaptureState& i) { i.captured_num_lock = !i.captured_num_lock; });
    test_field_affects_hash([](InputCaptureState& i) { i.captured_caps_lock = !i.captured_caps_lock; });
    test_field_affects_hash([](InputCaptureState& i) { i.input_captured = !i.input_captured; });
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash with New Subsystems Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(PR14HashTest, PicStateAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    // Get initial hash
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify PIC state
    ctx.pic.ticks = 10000;
    ctx.pic.irq_check = 0x01;
    ctx.pic.master_imr = 0xFE;

    // Get new hash
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    // Hashes should be different
    EXPECT_NE(hash1, hash2);
}

TEST(PR14HashTest, KeyboardStateAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify keyboard state
    ctx.keyboard.scanset = 1;
    ctx.keyboard.num_lock = true;
    ctx.keyboard.buffer_size = 10;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

TEST(PR14HashTest, InputStateAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify input state
    ctx.input.input_captured = true;
    ctx.input.captured_num_lock = true;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

TEST(PR14HashTest, SameStateProducesSameHash) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;

    ctx1.initialize();
    ctx2.initialize();

    // Set same state in all new subsystems
    ctx1.pic.ticks = 5000;
    ctx1.pic.irq_check = 0x02;
    ctx1.keyboard.scanset = 1;
    ctx1.keyboard.num_lock = true;
    ctx1.input.input_captured = true;

    ctx2.pic.ticks = 5000;
    ctx2.pic.irq_check = 0x02;
    ctx2.keyboard.scanset = 1;
    ctx2.keyboard.num_lock = true;
    ctx2.input.input_captured = true;

    // Get hash with ctx1
    set_current_context(&ctx1);
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());

    // Get hash with ctx2
    set_current_context(&ctx2);
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());

    // Should be same
    EXPECT_EQ(result1.value(), result2.value());

    // Clean up
    set_current_context(nullptr);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextPR14Test, ResetClearsAllNewSubsystems) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Modify all new subsystem states
    ctx.pic.ticks = 100000;
    ctx.pic.irq_check = 0xFF;
    ctx.pic.master_imr = 0x00;

    ctx.keyboard.scanset = 1;
    ctx.keyboard.num_lock = true;
    ctx.keyboard.caps_lock = true;
    ctx.keyboard.buffer_size = 16;

    ctx.input.input_captured = true;
    ctx.input.captured_num_lock = true;
    ctx.input.captured_caps_lock = true;

    // Reset
    ctx.reset();

    // PIC state should be reset
    EXPECT_EQ(ctx.pic.ticks, 0u);
    EXPECT_EQ(ctx.pic.irq_check, 0u);
    EXPECT_EQ(ctx.pic.master_imr, 0xFF);

    // Keyboard state should be reset
    EXPECT_EQ(ctx.keyboard.scanset, 2);
    EXPECT_FALSE(ctx.keyboard.num_lock);
    EXPECT_FALSE(ctx.keyboard.caps_lock);
    EXPECT_EQ(ctx.keyboard.buffer_size, 0);

    // Input state should be reset
    EXPECT_FALSE(ctx.input.input_captured);
    EXPECT_FALSE(ctx.input.captured_num_lock);
    EXPECT_FALSE(ctx.input.captured_caps_lock);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Combined All Seven Subsystems Hash Test
// ═══════════════════════════════════════════════════════════════════════════════

TEST(CombinedHashTest, AllSevenSubsystemsAffectHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Test each subsystem independently

    // 1. Timing
    ctx.timing.total_cycles += 1000;
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    EXPECT_NE(hash1, result2.value());
    ctx.timing.total_cycles -= 1000;

    // 2. CPU
    ctx.cpu_state.cycles += 1000;
    auto result3 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result3.has_value());
    EXPECT_NE(hash1, result3.value());
    ctx.cpu_state.cycles -= 1000;

    // 3. Mixer
    ctx.mixer.sample_counter += 1000;
    auto result4 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result4.has_value());
    EXPECT_NE(hash1, result4.value());
    ctx.mixer.sample_counter -= 1000;

    // 4. VGA
    ctx.vga.frame_counter += 100;
    auto result5 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result5.has_value());
    EXPECT_NE(hash1, result5.value());
    ctx.vga.frame_counter -= 100;

    // 5. PIC
    ctx.pic.ticks += 1000;
    auto result6 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result6.has_value());
    EXPECT_NE(hash1, result6.value());
    ctx.pic.ticks -= 1000;

    // 6. Keyboard
    ctx.keyboard.num_lock = !ctx.keyboard.num_lock;
    auto result7 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result7.has_value());
    EXPECT_NE(hash1, result7.value());
    ctx.keyboard.num_lock = !ctx.keyboard.num_lock;

    // 7. Input
    ctx.input.input_captured = !ctx.input.input_captured;
    auto result8 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result8.has_value());
    EXPECT_NE(hash1, result8.value());
}

TEST(CombinedHashTest, DeterministicWithAllSevenSubsystems) {
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
    ctx1.pic.ticks = 8000;
    ctx1.keyboard.num_lock = true;
    ctx1.input.input_captured = true;

    ctx2.timing.total_cycles = 10000;
    ctx2.cpu_state.cycles = 5000;
    ctx2.mixer.sample_counter = 2000;
    ctx2.vga.frame_counter = 100;
    ctx2.pic.ticks = 8000;
    ctx2.keyboard.num_lock = true;
    ctx2.input.input_captured = true;

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
