/**
 * @file test_dosbox_mixer.cpp
 * @brief Unit tests for DOSBox mixer state migration (PR #12).
 *
 * Tests:
 * - MixerState struct fields
 * - MixedFraction helper struct
 * - Mixer state reset
 * - State hash includes mixer state
 * - Thread safety documentation verification
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// MixedFraction Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(MixedFractionTest, DefaultValues) {
    MixedFraction frac;

    EXPECT_EQ(frac.whole, 0u);
    EXPECT_EQ(frac.numerator, 0u);
    EXPECT_EQ(frac.denominator, 1u);  // Never 0
}

TEST(MixedFractionTest, Reset) {
    MixedFraction frac;

    frac.whole = 100;
    frac.numerator = 5;
    frac.denominator = 10;

    frac.reset();

    EXPECT_EQ(frac.whole, 0u);
    EXPECT_EQ(frac.numerator, 0u);
    EXPECT_EQ(frac.denominator, 1u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// MixerState Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(MixerStateTest, DefaultValues) {
    MixerState mixer;

    // Core configuration
    EXPECT_EQ(mixer.freq, 44100u);
    EXPECT_EQ(mixer.blocksize, 1024u);

    // Volumes
    EXPECT_FLOAT_EQ(mixer.mastervol[0], 1.0f);
    EXPECT_FLOAT_EQ(mixer.mastervol[1], 1.0f);
    EXPECT_FLOAT_EQ(mixer.recordvol[0], 1.0f);
    EXPECT_FLOAT_EQ(mixer.recordvol[1], 1.0f);

    // Ring buffer state
    EXPECT_EQ(mixer.work_in, 0u);
    EXPECT_EQ(mixer.work_out, 0u);
    EXPECT_EQ(mixer.work_wrap, 0u);
    EXPECT_EQ(mixer.pos, 0u);
    EXPECT_EQ(mixer.done, 0u);

    // Fractional sample tracking
    EXPECT_EQ(mixer.samples_per_ms.whole, 0u);
    EXPECT_EQ(mixer.samples_this_ms.whole, 0u);
    EXPECT_EQ(mixer.samples_rendered.whole, 0u);

    // Flags
    EXPECT_FALSE(mixer.enabled);
    EXPECT_FALSE(mixer.nosound);
    EXPECT_FALSE(mixer.swapstereo);
    EXPECT_FALSE(mixer.sampleaccurate);
    EXPECT_FALSE(mixer.prebuffer_wait);
    EXPECT_FALSE(mixer.mute);

    // Prebuffer
    EXPECT_EQ(mixer.prebuffer_samples, 0u);

    // Statistics
    EXPECT_EQ(mixer.sample_counter, 0u);
    EXPECT_DOUBLE_EQ(mixer.start_pic_time, 0.0);
}

TEST(MixerStateTest, Reset) {
    MixerState mixer;

    // Set non-default values
    mixer.freq = 48000;
    mixer.blocksize = 2048;
    mixer.mastervol[0] = 0.5f;
    mixer.mastervol[1] = 0.8f;
    mixer.recordvol[0] = 0.3f;
    mixer.recordvol[1] = 0.7f;
    mixer.work_in = 1000;
    mixer.work_out = 500;
    mixer.work_wrap = 4096;
    mixer.pos = 200;
    mixer.done = 100;
    mixer.samples_per_ms.whole = 44;
    mixer.samples_per_ms.numerator = 1;
    mixer.samples_per_ms.denominator = 10;
    mixer.samples_this_ms.whole = 22;
    mixer.samples_rendered.whole = 10000;
    mixer.enabled = true;
    mixer.nosound = true;
    mixer.swapstereo = true;
    mixer.sampleaccurate = true;
    mixer.prebuffer_wait = true;
    mixer.mute = true;
    mixer.prebuffer_samples = 512;
    mixer.sample_counter = 1000000;
    mixer.start_pic_time = 123.456;

    // Reset
    mixer.reset();

    // Verify all fields reset
    EXPECT_EQ(mixer.freq, 44100u);
    EXPECT_EQ(mixer.blocksize, 1024u);
    EXPECT_FLOAT_EQ(mixer.mastervol[0], 1.0f);
    EXPECT_FLOAT_EQ(mixer.mastervol[1], 1.0f);
    EXPECT_FLOAT_EQ(mixer.recordvol[0], 1.0f);
    EXPECT_FLOAT_EQ(mixer.recordvol[1], 1.0f);
    EXPECT_EQ(mixer.work_in, 0u);
    EXPECT_EQ(mixer.work_out, 0u);
    EXPECT_EQ(mixer.work_wrap, 0u);
    EXPECT_EQ(mixer.pos, 0u);
    EXPECT_EQ(mixer.done, 0u);
    EXPECT_EQ(mixer.samples_per_ms.whole, 0u);
    EXPECT_EQ(mixer.samples_this_ms.whole, 0u);
    EXPECT_EQ(mixer.samples_rendered.whole, 0u);
    EXPECT_FALSE(mixer.enabled);
    EXPECT_FALSE(mixer.nosound);
    EXPECT_FALSE(mixer.swapstereo);
    EXPECT_FALSE(mixer.sampleaccurate);
    EXPECT_FALSE(mixer.prebuffer_wait);
    EXPECT_FALSE(mixer.mute);
    EXPECT_EQ(mixer.prebuffer_samples, 0u);
    EXPECT_EQ(mixer.sample_counter, 0u);
    EXPECT_DOUBLE_EQ(mixer.start_pic_time, 0.0);
}

TEST(MixerStateTest, HashInto) {
    MixerState mixer1;
    MixerState mixer2;

    mixer1.freq = 44100;
    mixer1.sample_counter = 1000;
    mixer1.enabled = true;

    mixer2.freq = 44100;
    mixer2.sample_counter = 1000;
    mixer2.enabled = true;

    // Same state should produce same hash
    HashBuilder builder1;
    mixer1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    mixer2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);

    // Different state should produce different hash
    mixer2.sample_counter = 2000;

    HashBuilder builder3;
    mixer2.hash_into(builder3);
    auto hash3 = builder3.finalize();

    EXPECT_NE(hash1, hash3);
}

TEST(MixerStateTest, HashExcludesStartPicTime) {
    MixerState mixer1;
    MixerState mixer2;

    // Same determinism-relevant state
    mixer1.freq = 44100;
    mixer1.sample_counter = 1000;
    mixer1.enabled = true;

    mixer2.freq = 44100;
    mixer2.sample_counter = 1000;
    mixer2.enabled = true;

    // Different wall-clock state (should NOT affect hash)
    mixer1.start_pic_time = 123.456;
    mixer2.start_pic_time = 789.012;

    // Hashes should be the same (start_pic_time excluded)
    HashBuilder builder1;
    mixer1.hash_into(builder1);
    auto hash1 = builder1.finalize();

    HashBuilder builder2;
    mixer2.hash_into(builder2);
    auto hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);
}

TEST(MixerStateTest, HashIncludesAllDeterminismFields) {
    MixerState base;
    base.freq = 44100;
    base.enabled = true;

    HashBuilder base_builder;
    base.hash_into(base_builder);
    auto base_hash = base_builder.finalize();

    auto test_field_affects_hash = [&base, &base_hash](auto modifier) {
        MixerState modified = base;
        modifier(modified);

        HashBuilder builder;
        modified.hash_into(builder);
        auto hash = builder.finalize();

        EXPECT_NE(base_hash, hash);
    };

    // Test core configuration
    test_field_affects_hash([](MixerState& m) { m.freq++; });
    test_field_affects_hash([](MixerState& m) { m.blocksize++; });

    // Test volumes
    test_field_affects_hash([](MixerState& m) { m.mastervol[0] += 0.1f; });
    test_field_affects_hash([](MixerState& m) { m.mastervol[1] += 0.1f; });
    test_field_affects_hash([](MixerState& m) { m.recordvol[0] += 0.1f; });
    test_field_affects_hash([](MixerState& m) { m.recordvol[1] += 0.1f; });

    // Test ring buffer state
    test_field_affects_hash([](MixerState& m) { m.work_in++; });
    test_field_affects_hash([](MixerState& m) { m.work_out++; });
    test_field_affects_hash([](MixerState& m) { m.work_wrap++; });
    test_field_affects_hash([](MixerState& m) { m.pos++; });
    test_field_affects_hash([](MixerState& m) { m.done++; });

    // Test fractional sample tracking
    test_field_affects_hash([](MixerState& m) { m.samples_per_ms.whole++; });
    test_field_affects_hash([](MixerState& m) { m.samples_this_ms.whole++; });
    test_field_affects_hash([](MixerState& m) { m.samples_rendered.whole++; });

    // Test flags
    test_field_affects_hash([](MixerState& m) { m.enabled = !m.enabled; });
    test_field_affects_hash([](MixerState& m) { m.nosound = !m.nosound; });
    test_field_affects_hash([](MixerState& m) { m.swapstereo = !m.swapstereo; });
    test_field_affects_hash([](MixerState& m) { m.sampleaccurate = !m.sampleaccurate; });
    test_field_affects_hash([](MixerState& m) { m.prebuffer_wait = !m.prebuffer_wait; });
    test_field_affects_hash([](MixerState& m) { m.mute = !m.mute; });

    // Test prebuffer
    test_field_affects_hash([](MixerState& m) { m.prebuffer_samples++; });

    // Test sample counter (determinism-relevant)
    test_field_affects_hash([](MixerState& m) { m.sample_counter++; });
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash with Mixer Context Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(MixerHashTest, HashChangesWithMixerState) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    // Get initial hash
    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Modify mixer state
    ctx.mixer.sample_counter += 1000;
    ctx.mixer.enabled = true;

    // Get new hash
    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    // Hashes should be different
    EXPECT_NE(hash1, hash2);
}

TEST(MixerHashTest, SameMixerStateProducesSameHash) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;

    ctx1.initialize();
    ctx2.initialize();

    // Set same mixer values
    ctx1.mixer.freq = 48000;
    ctx1.mixer.sample_counter = 5000;
    ctx1.mixer.enabled = true;

    ctx2.mixer.freq = 48000;
    ctx2.mixer.sample_counter = 5000;
    ctx2.mixer.enabled = true;

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

TEST(MixerHashTest, RingBufferStateAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Change ring buffer state
    ctx.mixer.work_in = 1000;
    ctx.mixer.work_out = 500;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

TEST(MixerHashTest, VolumeChangeAffectsHash) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    auto result1 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result1.has_value());
    auto hash1 = result1.value();

    // Change volume
    ctx.mixer.mastervol[0] = 0.5f;

    auto result2 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result2.has_value());
    auto hash2 = result2.value();

    EXPECT_NE(hash1, hash2);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context Mixer Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextMixerTest, ConfigAppliesSoundEnabled) {
    ContextConfig config;
    config.sound_enabled = true;

    DOSBoxContext ctx(config);
    ctx.initialize();

    // Config should apply enabled state
    EXPECT_TRUE(ctx.mixer.enabled);
}

TEST(ContextMixerTest, ConfigDisablesSound) {
    ContextConfig config;
    config.sound_enabled = false;

    DOSBoxContext ctx(config);
    ctx.initialize();

    // Config should disable mixer
    EXPECT_FALSE(ctx.mixer.enabled);
}

TEST(ContextMixerTest, ResetClearsMixerState) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Modify mixer state
    ctx.mixer.sample_counter = 100000;
    ctx.mixer.work_in = 500;
    ctx.mixer.mute = true;

    // Reset
    ctx.reset();

    // Mixer state should be reset
    EXPECT_EQ(ctx.mixer.sample_counter, 0u);
    EXPECT_EQ(ctx.mixer.work_in, 0u);
    EXPECT_FALSE(ctx.mixer.mute);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Combined Timing + CPU + Mixer Hash Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(CombinedHashTest, AllSubsystemsAffectHash) {
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
    EXPECT_NE(hash2, hash3);

    // Reset CPU, modify only mixer
    ctx.cpu_state.cycles -= 1000;
    ctx.mixer.sample_counter += 1000;
    auto result4 = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result4.has_value());
    auto hash4 = result4.value();
    EXPECT_NE(hash1, hash4);
    EXPECT_NE(hash2, hash4);
    EXPECT_NE(hash3, hash4);
}

TEST(CombinedHashTest, DeterministicWithAllSubsystems) {
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

    ctx2.timing.total_cycles = 10000;
    ctx2.cpu_state.cycles = 5000;
    ctx2.mixer.sample_counter = 2000;

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
