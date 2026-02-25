/**
 * @file test_determinism_at_scale.cpp
 * @brief Determinism proofs: two-instance hash identity, save/load midpoint,
 *        and input replay determinism.
 *
 * These tests verify the core determinism invariant:
 *   Obs(Deserialize(Serialize(S))) = Obs(S)
 * and that independent runs produce identical state hashes.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <vector>
#include <cstring>

// ─────────────────────────────────────────────────────────────────────────────
// Test fixture with headless instance management
// ─────────────────────────────────────────────────────────────────────────────

class DeterminismAtScaleTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();
    }

    void TearDown() override {
        pal::Platform::shutdown();
    }

    legends_handle create_instance() {
        legends_handle h = nullptr;
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        auto err = legends_create(&cfg, &h);
        EXPECT_EQ(err, LEGENDS_OK);
        return h;
    }

    std::vector<uint8_t> get_hash(legends_handle h) {
        std::vector<uint8_t> hash(32, 0);
        auto err = legends_get_state_hash(h, hash.data());
        EXPECT_EQ(err, LEGENDS_OK);
        return hash;
    }

    std::vector<uint8_t> save_state(legends_handle h) {
        size_t sz = 0;
        legends_save_state(h, nullptr, 0, &sz);
        std::vector<uint8_t> buf(sz);
        legends_save_state(h, buf.data(), sz, &sz);
        return buf;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// E.2: Cycle correctness
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DeterminismAtScaleTest, CycleCountCorrect) {
    auto h = create_instance();
    legends_step_result_t result{};
    legends_step_cycles(h, 5000, &result);
    EXPECT_EQ(result.cycles_executed, 5000u);

    uint64_t total = 0;
    legends_get_total_cycles(h, &total);
    EXPECT_EQ(total, 5000u);

    legends_destroy(h);
}

// ─────────────────────────────────────────────────────────────────────────────
// E.3: Two runs produce identical state hash
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DeterminismAtScaleTest, TwoRunsProduceSameHash) {
    // Run 1
    auto h1 = create_instance();
    legends_step_cycles(h1, 100000, nullptr);
    auto hash1 = get_hash(h1);
    legends_destroy(h1);

    // Must re-init platform between instances (single-instance V1)
    pal::Platform::shutdown();
    pal::Platform::initialize(pal::Backend::Headless);
    legends_force_destroy();

    // Run 2 (identical)
    auto h2 = create_instance();
    legends_step_cycles(h2, 100000, nullptr);
    auto hash2 = get_hash(h2);
    legends_destroy(h2);

    EXPECT_EQ(hash1, hash2)
        << "Two identical runs must produce the same state hash";
}

// ─────────────────────────────────────────────────────────────────────────────
// E.4: Save/load midpoint matches straight run
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DeterminismAtScaleTest, MidpointSaveLoadMatchesStraightRun) {
    // Straight run: 100K cycles
    auto h1 = create_instance();
    legends_step_cycles(h1, 100000, nullptr);
    auto hash_straight = get_hash(h1);
    legends_destroy(h1);

    // Split run: 50K, save, load, 50K more
    pal::Platform::shutdown();
    pal::Platform::initialize(pal::Backend::Headless);
    legends_force_destroy();

    auto h2 = create_instance();
    legends_step_cycles(h2, 50000, nullptr);
    auto state = save_state(h2);

    // Load and continue
    legends_load_state(h2, state.data(), state.size());
    legends_step_cycles(h2, 50000, nullptr);
    auto hash_split = get_hash(h2);
    legends_destroy(h2);

    EXPECT_EQ(hash_straight, hash_split)
        << "Straight run hash must equal save/load midpoint hash";
}

// ─────────────────────────────────────────────────────────────────────────────
// E.4b: Save/load round-trip preserves hash
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DeterminismAtScaleTest, SaveLoadRoundTripPreservesHash) {
    auto h = create_instance();
    legends_step_cycles(h, 10000, nullptr);

    auto hash_before = get_hash(h);
    auto state = save_state(h);

    legends_load_state(h, state.data(), state.size());
    auto hash_after = get_hash(h);

    EXPECT_EQ(hash_before, hash_after)
        << "Hash must be identical after save/load round-trip";

    legends_destroy(h);
}

// ─────────────────────────────────────────────────────────────────────────────
// E.5: Built-in determinism verification API
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DeterminismAtScaleTest, VerifyDeterminismAPI) {
    auto h = create_instance();
    int is_deterministic = 0;
    auto err = legends_verify_determinism(h, 10000, &is_deterministic);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(is_deterministic, 1) << "Built-in determinism check must pass";
    legends_destroy(h);
}

// ─────────────────────────────────────────────────────────────────────────────
// E.6: Input replay determinism
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DeterminismAtScaleTest, InputReplayIsDeterministic) {
    auto run_with_input = [this]() -> std::vector<uint8_t> {
        auto h = create_instance();
        legends_step_cycles(h, 10000, nullptr);
        legends_key_event(h, 0x1E, 1);  // 'A' press
        legends_key_event(h, 0x1E, 0);  // 'A' release
        legends_step_cycles(h, 10000, nullptr);
        legends_mouse_event(h, 10, -5, 1);  // mouse move + left click
        legends_step_cycles(h, 10000, nullptr);
        auto hash = get_hash(h);
        legends_destroy(h);
        return hash;
    };

    auto hash1 = run_with_input();

    // Re-init for second run
    pal::Platform::shutdown();
    pal::Platform::initialize(pal::Backend::Headless);
    legends_force_destroy();

    auto hash2 = run_with_input();

    EXPECT_EQ(hash1, hash2)
        << "Input replay must produce identical state hashes";
}

// ─────────────────────────────────────────────────────────────────────────────
// E.6b: Different inputs produce different hashes
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DeterminismAtScaleTest, DifferentInputsProduceDifferentHashes) {
    // Run with key 'A'
    auto h1 = create_instance();
    legends_step_cycles(h1, 1000, nullptr);
    legends_key_event(h1, 0x1E, 1);  // 'A'
    legends_step_cycles(h1, 1000, nullptr);
    auto hash_a = get_hash(h1);
    legends_destroy(h1);

    pal::Platform::shutdown();
    pal::Platform::initialize(pal::Backend::Headless);
    legends_force_destroy();

    // Run with key 'B'
    auto h2 = create_instance();
    legends_step_cycles(h2, 1000, nullptr);
    legends_key_event(h2, 0x30, 1);  // 'B'
    legends_step_cycles(h2, 1000, nullptr);
    auto hash_b = get_hash(h2);
    legends_destroy(h2);

    EXPECT_NE(hash_a, hash_b)
        << "Different inputs should produce different hashes";
}
