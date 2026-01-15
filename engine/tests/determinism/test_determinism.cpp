/**
 * @file test_determinism.cpp
 * @brief Determinism verification tests (PR #23)
 *
 * Tests to ensure DOSBox-X execution is deterministic:
 * - Same inputs produce same state hashes
 * - Save/load preserves execution trajectory
 * - Golden traces for regression testing
 *
 * @copyright GPL-2.0-or-later
 */

#include <gtest/gtest.h>
#include "determinism_harness.h"
#include "dosbox/dosbox_library.h"

using namespace aibox::determinism;

// ═══════════════════════════════════════════════════════════════════════════════
// Test Fixture
// ═══════════════════════════════════════════════════════════════════════════════

class DeterminismTest : public ::testing::Test {
protected:
    void SetUp() override {
        config_ = DOSBOX_LIB_CONFIG_INIT;
        config_.deterministic = 1;  // Ensure deterministic mode
    }

    void TearDown() override {
        if (handle_) {
            dosbox_lib_destroy(handle_);
            handle_ = nullptr;
        }
    }

    bool create_and_init() {
        if (dosbox_lib_create(&config_, &handle_) != DOSBOX_LIB_OK) {
            return false;
        }
        return dosbox_lib_init(handle_) == DOSBOX_LIB_OK;
    }

    dosbox_lib_config_t config_{};
    dosbox_lib_handle_t handle_ = nullptr;
};

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DeterminismTest, InitialStateHashIsConsistent) {
    // Create two instances and verify they have the same initial hash
    ASSERT_TRUE(create_and_init());
    StateHash hash1 = get_state_hash(handle_);
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    ASSERT_TRUE(create_and_init());
    StateHash hash2 = get_state_hash(handle_);

    EXPECT_EQ(hash1, hash2)
        << "Initial state hashes differ:\n"
        << "  hash1: " << hash1.to_hex() << "\n"
        << "  hash2: " << hash2.to_hex();
}

TEST_F(DeterminismTest, StateHashChangesAfterStep) {
    ASSERT_TRUE(create_and_init());

    StateHash hash_before = get_state_hash(handle_);
    dosbox_lib_step_ms(handle_, 10, nullptr);
    StateHash hash_after = get_state_hash(handle_);

    EXPECT_NE(hash_before, hash_after)
        << "State hash unchanged after stepping";
}

TEST_F(DeterminismTest, SameStepsProduceSameHash) {
    // Run 1
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_ms(handle_, 100, nullptr);
    StateHash hash1 = get_state_hash(handle_);
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    // Run 2
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_ms(handle_, 100, nullptr);
    StateHash hash2 = get_state_hash(handle_);

    EXPECT_EQ(hash1, hash2)
        << "State hashes differ after same steps:\n"
        << "  hash1: " << hash1.to_hex() << "\n"
        << "  hash2: " << hash2.to_hex();
}

TEST_F(DeterminismTest, DifferentStepsProduceDifferentHash) {
    // Run 1: 50ms
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_ms(handle_, 50, nullptr);
    StateHash hash1 = get_state_hash(handle_);
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    // Run 2: 100ms
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_ms(handle_, 100, nullptr);
    StateHash hash2 = get_state_hash(handle_);

    EXPECT_NE(hash1, hash2)
        << "State hashes should differ after different steps";
}

// ═══════════════════════════════════════════════════════════════════════════════
// Replay Determinism Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DeterminismTest, ReplayProducesSameTrace) {
    auto result = DeterminismVerifier::verify_replay(
        &config_,
        100,   // total_ms
        10     // checkpoint_interval_ms
    );

    EXPECT_TRUE(result.passed) << result.message;
}

TEST_F(DeterminismTest, LongerReplayProducesSameTrace) {
    auto result = DeterminismVerifier::verify_replay(
        &config_,
        500,   // total_ms
        50     // checkpoint_interval_ms
    );

    EXPECT_TRUE(result.passed) << result.message;
}

TEST_F(DeterminismTest, FineGrainedReplayProducesSameTrace) {
    auto result = DeterminismVerifier::verify_replay(
        &config_,
        50,    // total_ms
        1      // checkpoint_interval_ms (very fine-grained)
    );

    EXPECT_TRUE(result.passed) << result.message;
}

// ═══════════════════════════════════════════════════════════════════════════════
// Save/Load Round-Trip Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DeterminismTest, SaveLoadRoundTripPreservesDeterminism) {
    auto result = DeterminismVerifier::verify_save_load(
        &config_,
        50,    // ms_before_save
        50     // ms_after_save
    );

    EXPECT_TRUE(result.passed) << result.message;
}

TEST_F(DeterminismTest, SaveLoadWithLongerExecution) {
    auto result = DeterminismVerifier::verify_save_load(
        &config_,
        100,   // ms_before_save
        200    // ms_after_save
    );

    EXPECT_TRUE(result.passed) << result.message;
}

TEST_F(DeterminismTest, SaveLoadAtStartPreservesDeterminism) {
    auto result = DeterminismVerifier::verify_save_load(
        &config_,
        0,     // ms_before_save (immediate save)
        100    // ms_after_save
    );

    EXPECT_TRUE(result.passed) << result.message;
}

TEST_F(DeterminismTest, MultipleSaveLoadCycles) {
    ASSERT_TRUE(create_and_init());

    // Save initial state
    size_t state_size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &state_size);
    std::vector<uint8_t> saved_state(state_size);
    dosbox_lib_save_state(handle_, saved_state.data(), state_size, &state_size);

    // Step and record hashes
    std::vector<StateHash> hashes_run1;
    for (int i = 0; i < 5; ++i) {
        dosbox_lib_step_ms(handle_, 20, nullptr);
        hashes_run1.push_back(get_state_hash(handle_));
    }

    // Restore and replay
    dosbox_lib_load_state(handle_, saved_state.data(), state_size);

    std::vector<StateHash> hashes_run2;
    for (int i = 0; i < 5; ++i) {
        dosbox_lib_step_ms(handle_, 20, nullptr);
        hashes_run2.push_back(get_state_hash(handle_));
    }

    // Verify all hashes match
    ASSERT_EQ(hashes_run1.size(), hashes_run2.size());
    for (size_t i = 0; i < hashes_run1.size(); ++i) {
        EXPECT_EQ(hashes_run1[i], hashes_run2[i])
            << "Hash mismatch at step " << i;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Trace Recording Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DeterminismTest, TraceRecordingCaptures) {
    ASSERT_TRUE(create_and_init());

    TraceRecording trace;
    trace.capture(handle_, "start");
    dosbox_lib_step_ms(handle_, 50, nullptr);
    trace.capture(handle_, "middle");
    dosbox_lib_step_ms(handle_, 50, nullptr);
    trace.capture(handle_, "end");

    EXPECT_EQ(trace.size(), 3u);
    EXPECT_EQ(trace.points()[0].label, "start");
    EXPECT_EQ(trace.points()[1].label, "middle");
    EXPECT_EQ(trace.points()[2].label, "end");

    // Verify cycles are increasing
    EXPECT_LT(trace.points()[0].cycles, trace.points()[1].cycles);
    EXPECT_LT(trace.points()[1].cycles, trace.points()[2].cycles);
}

TEST_F(DeterminismTest, TracePointSerialization) {
    TracePoint point;
    point.cycles = 12345;
    point.emu_time_us = 67890;
    point.hash = *StateHash::from_hex(
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    );
    point.label = "test_point";

    std::string jsonl = point.to_jsonl();
    EXPECT_FALSE(jsonl.empty());

    auto parsed = TracePoint::from_jsonl(jsonl);
    ASSERT_TRUE(parsed.has_value());
    EXPECT_EQ(parsed->cycles, point.cycles);
    EXPECT_EQ(parsed->emu_time_us, point.emu_time_us);
    EXPECT_EQ(parsed->hash, point.hash);
    EXPECT_EQ(parsed->label, point.label);
}

TEST_F(DeterminismTest, TraceRecordingsMatch) {
    // Create two trace recordings with same execution
    auto run_trace = [this]() -> TraceRecording {
        create_and_init();
        TraceRecording trace;
        trace.capture(handle_, "start");
        for (int i = 0; i < 5; ++i) {
            dosbox_lib_step_ms(handle_, 20, nullptr);
            trace.capture(handle_, "step_" + std::to_string(i));
        }
        dosbox_lib_destroy(handle_);
        handle_ = nullptr;
        return trace;
    };

    TraceRecording trace1 = run_trace();
    TraceRecording trace2 = run_trace();

    EXPECT_TRUE(trace1.matches(trace2));
    EXPECT_FALSE(trace1.find_divergence(trace2).has_value());
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash Utility Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(StateHashTest, HexConversionRoundTrip) {
    StateHash original;
    for (size_t i = 0; i < 32; ++i) {
        original.bytes[i] = static_cast<uint8_t>(i * 8);
    }

    std::string hex = original.to_hex();
    EXPECT_EQ(hex.length(), 64u);

    auto parsed = StateHash::from_hex(hex);
    ASSERT_TRUE(parsed.has_value());
    EXPECT_EQ(*parsed, original);
}

TEST(StateHashTest, InvalidHexReturnsNullopt) {
    // Too short
    EXPECT_FALSE(StateHash::from_hex("0123").has_value());

    // Too long
    EXPECT_FALSE(StateHash::from_hex(
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef00"
    ).has_value());

    // Invalid characters
    EXPECT_FALSE(StateHash::from_hex(
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdeg"
    ).has_value());
}

TEST(StateHashTest, EqualityOperators) {
    StateHash hash1, hash2;
    hash1.bytes.fill(0x42);
    hash2.bytes.fill(0x42);

    EXPECT_EQ(hash1, hash2);
    EXPECT_FALSE(hash1 != hash2);

    hash2.bytes[0] = 0x00;
    EXPECT_NE(hash1, hash2);
    EXPECT_FALSE(hash1 == hash2);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Cycle-Based Stepping Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DeterminismTest, CycleSteppingIsDeterministic) {
    // Run 1
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_cycles(handle_, 10000, nullptr);
    StateHash hash1 = get_state_hash(handle_);
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    // Run 2
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_cycles(handle_, 10000, nullptr);
    StateHash hash2 = get_state_hash(handle_);

    EXPECT_EQ(hash1, hash2)
        << "Cycle-based stepping produced different hashes";
}

TEST_F(DeterminismTest, SmallStepsEqualLargeStep) {
    // Run 1: One large step
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_cycles(handle_, 10000, nullptr);
    StateHash hash1 = get_state_hash(handle_);
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    // Run 2: Many small steps
    ASSERT_TRUE(create_and_init());
    for (int i = 0; i < 100; ++i) {
        dosbox_lib_step_cycles(handle_, 100, nullptr);
    }
    StateHash hash2 = get_state_hash(handle_);

    EXPECT_EQ(hash1, hash2)
        << "Small steps should produce same result as one large step";
}

// ═══════════════════════════════════════════════════════════════════════════════
// Reset Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DeterminismTest, ResetRestoresInitialState) {
    ASSERT_TRUE(create_and_init());

    StateHash initial_hash = get_state_hash(handle_);

    // Step to change state
    dosbox_lib_step_ms(handle_, 100, nullptr);
    StateHash stepped_hash = get_state_hash(handle_);
    EXPECT_NE(initial_hash, stepped_hash);

    // Reset
    dosbox_lib_reset(handle_);
    StateHash reset_hash = get_state_hash(handle_);

    EXPECT_EQ(initial_hash, reset_hash)
        << "Reset should restore initial state";
}

TEST_F(DeterminismTest, ResetProducesSameHashAsNewInstance) {
    // Run 1: New instance
    ASSERT_TRUE(create_and_init());
    StateHash hash_new = get_state_hash(handle_);
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    // Run 2: Reset existing instance
    ASSERT_TRUE(create_and_init());
    dosbox_lib_step_ms(handle_, 100, nullptr);  // Modify state
    dosbox_lib_reset(handle_);
    StateHash hash_reset = get_state_hash(handle_);

    EXPECT_EQ(hash_new, hash_reset)
        << "Reset should produce same state as new instance";
}

// ═══════════════════════════════════════════════════════════════════════════════
// Stress Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DeterminismTest, ManyStepsRemainDeterministic) {
    // Run 1
    ASSERT_TRUE(create_and_init());
    for (int i = 0; i < 100; ++i) {
        dosbox_lib_step_ms(handle_, 10, nullptr);
    }
    StateHash hash1 = get_state_hash(handle_);
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    // Run 2
    ASSERT_TRUE(create_and_init());
    for (int i = 0; i < 100; ++i) {
        dosbox_lib_step_ms(handle_, 10, nullptr);
    }
    StateHash hash2 = get_state_hash(handle_);

    EXPECT_EQ(hash1, hash2)
        << "Many small steps should remain deterministic";
}

TEST_F(DeterminismTest, LongExecutionRemainsDeterministic) {
    auto result = DeterminismVerifier::verify_replay(
        &config_,
        1000,   // total_ms (1 second of emulated time)
        100     // checkpoint every 100ms
    );

    EXPECT_TRUE(result.passed) << result.message;
}
