/**
 * @file test_legends_embed_savestate.cpp
 * @brief Save/load state and determinism tests for legends_embed API.
 *
 * Split from test_legends_embed.cpp for faster incremental builds.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include "internal/legends_instance.h"
#include <cstring>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// Phase 5: Save-State Determinism Tests
// Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxSaveStateTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        legends_force_destroy();

        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

// Save State Tests

TEST_F(DosboxxSaveStateTest, SaveStateQuerySize) {
    size_t size;
    auto err = legends_save_state(handle_, nullptr, 0, &size);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_GT(size, 0u);  // Should return non-zero size
}

TEST_F(DosboxxSaveStateTest, SaveStateFillsBuffer) {
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size);
    auto err = legends_save_state(handle_, buffer.data(), buffer.size(), &size);
    EXPECT_EQ(err, LEGENDS_OK);

    // Check magic number (DBXS = 0x53584244 little-endian)
    uint32_t magic;
    std::memcpy(&magic, buffer.data(), sizeof(magic));
    EXPECT_EQ(magic, 0x53584244u);
}

TEST_F(DosboxxSaveStateTest, SaveStateBufferTooSmall) {
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size / 2);  // Too small
    size_t out_size;
    auto err = legends_save_state(handle_, buffer.data(), buffer.size(), &out_size);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DosboxxSaveStateTest, SaveStateRejectsNullSizeOut) {
    auto err = legends_save_state(handle_, nullptr, 0, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

// Load State Tests

TEST_F(DosboxxSaveStateTest, LoadStateRestoresState) {
    // Step some cycles
    legends_step_cycles(handle_, 10000, nullptr);

    // Save state
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Get current time
    uint64_t time_before;
    legends_get_emu_time(handle_, &time_before);

    // Step more
    legends_step_cycles(handle_, 5000, nullptr);

    // Load state
    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_OK);

    // Time should be restored
    uint64_t time_after;
    legends_get_emu_time(handle_, &time_after);
    EXPECT_EQ(time_after, time_before);
}

TEST_F(DosboxxSaveStateTest, LoadStateRejectsInvalidMagic) {
    std::vector<uint8_t> buffer(256, 0);  // All zeros = invalid magic
    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);
}

TEST_F(DosboxxSaveStateTest, LoadStateRejectsVersionMismatch) {
    // Save valid state
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Corrupt version field (offset 4)
    buffer[4] = 99;  // Invalid version

    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_ERR_VERSION_MISMATCH);
}

TEST_F(DosboxxSaveStateTest, LoadStateRejectsCorruptedChecksum) {
    // Save valid state
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Corrupt data (checksum will fail)
    if (size > 100) {
        buffer[100] ^= 0xFF;
    }

    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);
}

// State Hash Tests

TEST_F(DosboxxSaveStateTest, GetStateHashWorks) {
    uint8_t hash[32];
    auto err = legends_get_state_hash(handle_, hash);
    EXPECT_EQ(err, LEGENDS_OK);

    // Hash should not be all zeros
    bool all_zeros = true;
    for (int i = 0; i < 32; ++i) {
        if (hash[i] != 0) all_zeros = false;
    }
    EXPECT_FALSE(all_zeros);
}

TEST_F(DosboxxSaveStateTest, StateHashIsConsistent) {
    uint8_t hash1[32], hash2[32];

    legends_get_state_hash(handle_, hash1);
    legends_get_state_hash(handle_, hash2);

    // Same state should produce same hash
    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0);
}

TEST_F(DosboxxSaveStateTest, StateHashChangesAfterStep) {
    uint8_t hash1[32], hash2[32];

    legends_get_state_hash(handle_, hash1);

    // Step some cycles
    legends_step_cycles(handle_, 10000, nullptr);

    legends_get_state_hash(handle_, hash2);

    // Hash should change after stepping
    EXPECT_NE(std::memcmp(hash1, hash2, 32), 0);
}

TEST_F(DosboxxSaveStateTest, StateHashMatchesAfterLoadState) {
    // Save initial state and hash
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), buffer.size(), &size);

    uint8_t hash1[32];
    legends_get_state_hash(handle_, hash1);

    // Step and change state
    legends_step_cycles(handle_, 10000, nullptr);

    // Load original state
    legends_load_state(handle_, buffer.data(), buffer.size());

    // Hash should match original
    uint8_t hash2[32];
    legends_get_state_hash(handle_, hash2);
    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0);
}

// Determinism Verification Tests

TEST_F(DosboxxSaveStateTest, VerifyDeterminismWorks) {
    int is_deterministic;
    auto err = legends_verify_determinism(handle_, 10000, &is_deterministic);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(is_deterministic, 1);  // Should be deterministic
}

TEST_F(DosboxxSaveStateTest, VerifyDeterminismAfterInput) {
    // Queue some input
    legends_key_event(handle_, 0x1E, 1);
    legends_key_event(handle_, 0x1E, 0);

    int is_deterministic;
    auto err = legends_verify_determinism(handle_, 5000, &is_deterministic);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(is_deterministic, 1);  // Should still be deterministic
}

TEST_F(DosboxxSaveStateTest, VerifyDeterminismWithMultipleSteps) {
    // Do some initial work
    legends_step_ms(handle_, 50, nullptr);

    int is_deterministic;
    auto err = legends_verify_determinism(handle_, 20000, &is_deterministic);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(is_deterministic, 1);
}

// Round-Trip Invariant Test (per TLA+ specification)

TEST_F(DosboxxSaveStateTest, RoundTripPreservesObservation) {
    // Step to create some state
    legends_step_cycles(handle_, 50000, nullptr);

    // Get initial hash
    uint8_t hash_before[32];
    legends_get_state_hash(handle_, hash_before);

    // Save state
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Load state
    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_OK);

    // Get hash after round-trip
    uint8_t hash_after[32];
    legends_get_state_hash(handle_, hash_after);

    // Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
    EXPECT_EQ(std::memcmp(hash_before, hash_after, 32), 0)
        << "Round-trip must preserve observable state (TLA+ invariant)";
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 5.5: Engine State Integration Tests (Phase 2 of save/load)
// Tests that legends layer properly includes engine state in save/load
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DosboxxSaveStateTest, SaveStateIncludesEngineState) {
    // Step to create some state
    legends_step_cycles(handle_, 10000, nullptr);

    // Get size - should be larger than before engine state integration
    size_t size = 0;
    auto err = legends_save_state(handle_, nullptr, 0, &size);
    EXPECT_EQ(err, LEGENDS_OK);

    // Size should include engine state (ENGINE_STATE_SIZE = 120 bytes)
    // Minimum: legends header + sections + engine state (120 bytes)
    EXPECT_GT(size, 120u) << "Save state should include engine state";
}

TEST_F(DosboxxSaveStateTest, SaveLoadEngineStateSyncsTime) {
    // Step to create known timing state
    legends_step_cycles(handle_, 25000, nullptr);

    uint64_t total_cycles_before = 0;
    uint64_t emu_time_before = 0;
    legends_get_total_cycles(handle_, &total_cycles_before);
    legends_get_emu_time(handle_, &emu_time_before);

    // Save state
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), size, &size);

    // Step more to diverge state
    legends_step_cycles(handle_, 50000, nullptr);

    // Verify state diverged
    uint64_t total_cycles_diverged = 0;
    legends_get_total_cycles(handle_, &total_cycles_diverged);
    EXPECT_GT(total_cycles_diverged, total_cycles_before);

    // Load saved state
    auto err = legends_load_state(handle_, buffer.data(), size);
    EXPECT_EQ(err, LEGENDS_OK);

    // Verify timing restored
    uint64_t total_cycles_after = 0;
    uint64_t emu_time_after = 0;
    legends_get_total_cycles(handle_, &total_cycles_after);
    legends_get_emu_time(handle_, &emu_time_after);

    EXPECT_EQ(total_cycles_before, total_cycles_after);
    EXPECT_EQ(emu_time_before, emu_time_after);
}

TEST_F(DosboxxSaveStateTest, SaveLoadEngineStateRoundTripDeterminism) {
    // Step to initial state
    legends_step_cycles(handle_, 5000, nullptr);

    // Save state
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> saved_state(size);
    legends_save_state(handle_, saved_state.data(), size, &size);

    // Step more and record result
    legends_step_result_t result1{};
    legends_step_cycles(handle_, 15000, &result1);
    uint8_t hash1[32] = {0};
    legends_get_state_hash(handle_, hash1);

    // Restore state
    legends_load_state(handle_, saved_state.data(), size);

    // Step same amount
    legends_step_result_t result2{};
    legends_step_cycles(handle_, 15000, &result2);
    uint8_t hash2[32] = {0};
    legends_get_state_hash(handle_, hash2);

    // Should be deterministic
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0)
        << "Replay from saved state should be deterministic";
}

TEST_F(DosboxxSaveStateTest, SaveStateVersionIs3) {
    // Version 3 adds unified input queue and portable serialization
    legends_step_cycles(handle_, 1000, nullptr);

    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), size, &size);

    // Check version in header
    uint32_t version = 0;
    std::memcpy(&version, buffer.data() + 4, sizeof(version));  // version is at offset 4
    EXPECT_EQ(version, 3u) << "Save state version should be 3 (unified input queue, portable serialization)";
}

TEST_F(DosboxxSaveStateTest, MultipleEngineStateRoundTrips) {
    // Multiple save/load cycles should preserve complete state
    legends_step_cycles(handle_, 3000, nullptr);

    uint8_t original_hash[32] = {0};
    legends_get_state_hash(handle_, original_hash);

    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);

    for (int i = 0; i < 3; ++i) {
        // Save
        legends_save_state(handle_, buffer.data(), size, &size);

        // Step to diverge
        legends_step_cycles(handle_, 2000, nullptr);

        // Load (restore)
        legends_load_state(handle_, buffer.data(), size);

        // Verify state matches original
        uint8_t current_hash[32] = {0};
        legends_get_state_hash(handle_, current_hash);
        EXPECT_EQ(std::memcmp(original_hash, current_hash, 32), 0)
            << "Round trip " << i << " failed to preserve state";
    }
}

TEST_F(DosboxxSaveStateTest, EngineStatePreservesAllSubsystems) {
    // Step to create diverse state across subsystems
    legends_step_cycles(handle_, 10000, nullptr);

    // Inject input to affect keyboard state
    legends_key_event(handle_, 0x1C, 1);  // Enter key down
    legends_key_event(handle_, 0x1C, 0);  // Enter key up

    // Get comprehensive state hash before save
    uint8_t hash_before[32] = {0};
    legends_get_state_hash(handle_, hash_before);

    // Save complete state
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), size, &size);

    // Significantly diverge state
    legends_step_cycles(handle_, 50000, nullptr);
    for (int i = 0; i < 10; ++i) {
        legends_key_event(handle_, static_cast<uint8_t>(0x30 + i), 1);  // Various keys
        legends_key_event(handle_, static_cast<uint8_t>(0x30 + i), 0);
    }

    // Load saved state
    auto err = legends_load_state(handle_, buffer.data(), size);
    EXPECT_EQ(err, LEGENDS_OK);

    // Verify complete state restored
    uint8_t hash_after[32] = {0};
    legends_get_state_hash(handle_, hash_after);
    EXPECT_EQ(std::memcmp(hash_before, hash_after, 32), 0)
        << "All subsystem state should be restored";
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 8: Round-Trip Determinism Integration Tests
// Verifies that save/load/step produces identical results (TLA+ compliance)
// ─────────────────────────────────────────────────────────────────────────────

class DeterminismIntegrationTest : public ::testing::Test {
protected:
    void SetUp() override {
        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
    }

    void TearDown() override {
        if (handle_) {
            legends_destroy(handle_);
            handle_ = nullptr;
        }
    }

    legends_handle handle_ = nullptr;
};

TEST_F(DeterminismIntegrationTest, SaveStepLoadStepProducesSameHash) {
    // TLA+ test: save state, step N, hash1; load, step N, hash2; hash1 == hash2

    // Step to non-trivial state
    legends_step_cycles(handle_, 5000, nullptr);

    // Save state at this point
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> checkpoint(size);
    legends_save_state(handle_, checkpoint.data(), size, &size);

    // Step more and capture final hash
    legends_step_result_t result1{};
    legends_step_cycles(handle_, 20000, &result1);
    uint8_t hash1[32] = {0};
    legends_get_state_hash(handle_, hash1);

    // Restore to checkpoint
    legends_load_state(handle_, checkpoint.data(), size);

    // Step same amount
    legends_step_result_t result2{};
    legends_step_cycles(handle_, 20000, &result2);
    uint8_t hash2[32] = {0};
    legends_get_state_hash(handle_, hash2);

    // Results must match
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0)
        << "Determinism violated: hash differs after replay";
}

TEST_F(DeterminismIntegrationTest, MultipleBranchingDeterminism) {
    // Save at checkpoint, branch execution, verify both branches replay identically

    legends_step_cycles(handle_, 3000, nullptr);

    // Save checkpoint
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> checkpoint(size);
    legends_save_state(handle_, checkpoint.data(), size, &size);

    // Branch A: step 10000
    legends_step_cycles(handle_, 10000, nullptr);
    uint8_t hash_a[32] = {0};
    legends_get_state_hash(handle_, hash_a);

    // Restore and branch B: step 5000 + 5000
    legends_load_state(handle_, checkpoint.data(), size);
    legends_step_cycles(handle_, 5000, nullptr);
    legends_step_cycles(handle_, 5000, nullptr);
    uint8_t hash_b[32] = {0};
    legends_get_state_hash(handle_, hash_b);

    // Both branches should produce same result (10000 cycles total from checkpoint)
    EXPECT_EQ(std::memcmp(hash_a, hash_b, 32), 0)
        << "Determinism violated: different step sizes produce different results";
}

TEST_F(DeterminismIntegrationTest, LongRunningDeterminism) {
    // Extended determinism test with many iterations

    legends_step_cycles(handle_, 1000, nullptr);

    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> initial_state(size);
    legends_save_state(handle_, initial_state.data(), size, &size);

    // Run 1: multiple steps
    std::vector<uint8_t> hashes1;
    for (int i = 0; i < 10; ++i) {
        legends_step_cycles(handle_, 2000, nullptr);
        uint8_t hash[32];
        legends_get_state_hash(handle_, hash);
        hashes1.insert(hashes1.end(), hash, hash + 32);
    }

    // Restore and run 2: same steps
    legends_load_state(handle_, initial_state.data(), size);
    std::vector<uint8_t> hashes2;
    for (int i = 0; i < 10; ++i) {
        legends_step_cycles(handle_, 2000, nullptr);
        uint8_t hash[32];
        legends_get_state_hash(handle_, hash);
        hashes2.insert(hashes2.end(), hash, hash + 32);
    }

    // All intermediate hashes should match
    ASSERT_EQ(hashes1.size(), hashes2.size());
    for (size_t i = 0; i < hashes1.size(); ++i) {
        EXPECT_EQ(hashes1[i], hashes2[i]) << "Hash differs at position " << i;
    }
}

TEST_F(DeterminismIntegrationTest, DeterminismWithInputInjection) {
    // Verify determinism holds when input is injected at specific times

    legends_step_cycles(handle_, 2000, nullptr);

    // Save checkpoint
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> checkpoint(size);
    legends_save_state(handle_, checkpoint.data(), size, &size);

    // Run 1: inject key, step
    legends_key_event(handle_, 0x1C, 1);  // Enter down
    legends_step_cycles(handle_, 5000, nullptr);
    legends_key_event(handle_, 0x1C, 0);  // Enter up
    legends_step_cycles(handle_, 5000, nullptr);
    uint8_t hash1[32] = {0};
    legends_get_state_hash(handle_, hash1);

    // Restore and run 2: same sequence
    legends_load_state(handle_, checkpoint.data(), size);
    legends_key_event(handle_, 0x1C, 1);
    legends_step_cycles(handle_, 5000, nullptr);
    legends_key_event(handle_, 0x1C, 0);
    legends_step_cycles(handle_, 5000, nullptr);
    uint8_t hash2[32] = {0};
    legends_get_state_hash(handle_, hash2);

    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0)
        << "Determinism violated: input injection produces different results";
}

TEST_F(DeterminismIntegrationTest, ResetAndReplayDeterminism) {
    // Reset should produce deterministic initial state

    // Get initial state hash
    uint8_t hash_init1[32] = {0};
    legends_get_state_hash(handle_, hash_init1);

    // Step, then reset
    legends_step_cycles(handle_, 10000, nullptr);
    legends_reset(handle_);

    // Get hash after reset
    uint8_t hash_init2[32] = {0};
    legends_get_state_hash(handle_, hash_init2);

    // Reset should restore to same initial state
    EXPECT_EQ(std::memcmp(hash_init1, hash_init2, 32), 0)
        << "Reset does not restore deterministic initial state";
}

TEST_F(DeterminismIntegrationTest, NestedSaveLoadDeterminism) {
    // Nested checkpoints should all be restorable

    legends_step_cycles(handle_, 1000, nullptr);

    // Checkpoint 1
    size_t size1 = 0;
    legends_save_state(handle_, nullptr, 0, &size1);
    std::vector<uint8_t> cp1(size1);
    legends_save_state(handle_, cp1.data(), size1, &size1);
    uint8_t hash_cp1[32];
    legends_get_state_hash(handle_, hash_cp1);

    // Step more and checkpoint 2
    legends_step_cycles(handle_, 2000, nullptr);
    size_t size2 = 0;
    legends_save_state(handle_, nullptr, 0, &size2);
    std::vector<uint8_t> cp2(size2);
    legends_save_state(handle_, cp2.data(), size2, &size2);
    uint8_t hash_cp2[32];
    legends_get_state_hash(handle_, hash_cp2);

    // Step more and checkpoint 3
    legends_step_cycles(handle_, 3000, nullptr);
    size_t size3 = 0;
    legends_save_state(handle_, nullptr, 0, &size3);
    std::vector<uint8_t> cp3(size3);
    legends_save_state(handle_, cp3.data(), size3, &size3);
    uint8_t hash_cp3[32];
    legends_get_state_hash(handle_, hash_cp3);

    // Restore in reverse order and verify
    legends_load_state(handle_, cp1.data(), size1);
    uint8_t hash_restored1[32];
    legends_get_state_hash(handle_, hash_restored1);
    EXPECT_EQ(std::memcmp(hash_cp1, hash_restored1, 32), 0) << "Checkpoint 1 restore failed";

    legends_load_state(handle_, cp3.data(), size3);
    uint8_t hash_restored3[32];
    legends_get_state_hash(handle_, hash_restored3);
    EXPECT_EQ(std::memcmp(hash_cp3, hash_restored3, 32), 0) << "Checkpoint 3 restore failed";

    legends_load_state(handle_, cp2.data(), size2);
    uint8_t hash_restored2[32];
    legends_get_state_hash(handle_, hash_restored2);
    EXPECT_EQ(std::memcmp(hash_cp2, hash_restored2, 32), 0) << "Checkpoint 2 restore failed";
}

TEST_F(DeterminismIntegrationTest, TLAPlusObservationInvariant) {
    // TLA+ specification: Obs(Deserialize(Serialize(S))) = Obs(S)
    // This is the core invariant that must hold for deterministic replay

    // Create diverse state
    legends_step_cycles(handle_, 5000, nullptr);
    legends_key_event(handle_, 0x2A, 1);  // Left Shift
    legends_step_cycles(handle_, 1000, nullptr);

    // Capture observation before
    uint8_t obs_before[32];
    legends_get_state_hash(handle_, obs_before);

    // Serialize
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> serialized(size);
    auto err = legends_save_state(handle_, serialized.data(), size, &size);
    ASSERT_EQ(err, LEGENDS_OK);

    // Mutate state (simulate time passing or other changes)
    legends_step_cycles(handle_, 10000, nullptr);
    legends_key_event(handle_, 0x2A, 0);

    // Deserialize
    err = legends_load_state(handle_, serialized.data(), size);
    ASSERT_EQ(err, LEGENDS_OK);

    // Capture observation after
    uint8_t obs_after[32];
    legends_get_state_hash(handle_, obs_after);

    // TLA+ invariant: observations must match
    EXPECT_EQ(std::memcmp(obs_before, obs_after, 32), 0)
        << "TLA+ invariant violated: Obs(Deserialize(Serialize(S))) != Obs(S)";
}

// ─────────────────────────────────────────────────────────────────────────────
// Test Hardening: Determinism Tests
// ─────────────────────────────────────────────────────────────────────────────

class DeterminismHardeningTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        legends_force_destroy();
        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

// Test: Split-step determinism (step N vs step N/2 + N/2)
TEST_F(DeterminismHardeningTest, SplitStepDeterminism) {
    // Run 1: step 10000 cycles at once
    legends_reset(handle_);
    legends_step_cycles(handle_, 10000, nullptr);
    uint8_t hash1[32];
    legends_get_state_hash(handle_, hash1);

    // Run 2: step 5000 + 5000 cycles
    legends_reset(handle_);
    legends_step_cycles(handle_, 5000, nullptr);
    legends_step_cycles(handle_, 5000, nullptr);
    uint8_t hash2[32];
    legends_get_state_hash(handle_, hash2);

    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0)
        << "Split-step should produce identical state: step(N) == step(N/2) + step(N/2)";
}

// Test: Various split patterns
TEST_F(DeterminismHardeningTest, VariousSplitPatterns) {
    const uint64_t total = 12000;

    // Reference: single step
    legends_reset(handle_);
    legends_step_cycles(handle_, total, nullptr);
    uint8_t ref_hash[32];
    legends_get_state_hash(handle_, ref_hash);

    // Pattern 1: 3 equal parts
    legends_reset(handle_);
    legends_step_cycles(handle_, 4000, nullptr);
    legends_step_cycles(handle_, 4000, nullptr);
    legends_step_cycles(handle_, 4000, nullptr);
    uint8_t hash1[32];
    legends_get_state_hash(handle_, hash1);
    EXPECT_EQ(std::memcmp(ref_hash, hash1, 32), 0) << "3-way split failed";

    // Pattern 2: 12 small steps
    legends_reset(handle_);
    for (int i = 0; i < 12; ++i) {
        legends_step_cycles(handle_, 1000, nullptr);
    }
    uint8_t hash2[32];
    legends_get_state_hash(handle_, hash2);
    EXPECT_EQ(std::memcmp(ref_hash, hash2, 32), 0) << "12-way split failed";

    // Pattern 3: uneven split
    legends_reset(handle_);
    legends_step_cycles(handle_, 1, nullptr);
    legends_step_cycles(handle_, 11999, nullptr);
    uint8_t hash3[32];
    legends_get_state_hash(handle_, hash3);
    EXPECT_EQ(std::memcmp(ref_hash, hash3, 32), 0) << "Uneven split failed";
}

// Test: Round-trip determinism with continued execution
TEST_F(DeterminismHardeningTest, RoundTripWithContinuedExecution) {
    // Setup: step to create state
    legends_step_cycles(handle_, 5000, nullptr);

    // Save checkpoint
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> checkpoint(size);
    legends_save_state(handle_, checkpoint.data(), size, &size);

    // Run 1: continue from checkpoint
    legends_step_cycles(handle_, 10000, nullptr);
    uint8_t hash1[32];
    legends_get_state_hash(handle_, hash1);

    // Restore and Run 2: same continuation
    legends_load_state(handle_, checkpoint.data(), size);
    legends_step_cycles(handle_, 10000, nullptr);
    uint8_t hash2[32];
    legends_get_state_hash(handle_, hash2);

    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0)
        << "Round-trip with continued execution should be deterministic";
}

// Test: Input injection at deterministic times
TEST_F(DeterminismHardeningTest, InputInjectionDeterminism) {
    legends_step_cycles(handle_, 1000, nullptr);

    // Save checkpoint
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> checkpoint(size);
    legends_save_state(handle_, checkpoint.data(), size, &size);

    // Run 1: inject input sequence
    legends_key_event(handle_, 0x1E, 1);  // 'A' down
    legends_step_cycles(handle_, 500, nullptr);
    legends_key_event(handle_, 0x1E, 0);  // 'A' up
    legends_step_cycles(handle_, 500, nullptr);
    legends_key_event(handle_, 0x30, 1);  // 'B' down
    legends_step_cycles(handle_, 500, nullptr);
    legends_key_event(handle_, 0x30, 0);  // 'B' up
    legends_step_cycles(handle_, 500, nullptr);
    uint8_t hash1[32];
    legends_get_state_hash(handle_, hash1);

    // Restore and Run 2: identical sequence
    legends_load_state(handle_, checkpoint.data(), size);
    legends_key_event(handle_, 0x1E, 1);
    legends_step_cycles(handle_, 500, nullptr);
    legends_key_event(handle_, 0x1E, 0);
    legends_step_cycles(handle_, 500, nullptr);
    legends_key_event(handle_, 0x30, 1);
    legends_step_cycles(handle_, 500, nullptr);
    legends_key_event(handle_, 0x30, 0);
    legends_step_cycles(handle_, 500, nullptr);
    uint8_t hash2[32];
    legends_get_state_hash(handle_, hash2);

    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0)
        << "Input injection replay should be deterministic";
}

// Test: Multi-checkpoint restore in mixed order
TEST_F(DeterminismHardeningTest, MultiCheckpointMixedOrderRestore) {
    // Create checkpoint A at t=1000
    legends_step_cycles(handle_, 1000, nullptr);
    size_t sizeA = 0;
    legends_save_state(handle_, nullptr, 0, &sizeA);
    std::vector<uint8_t> checkpointA(sizeA);
    legends_save_state(handle_, checkpointA.data(), sizeA, &sizeA);
    uint8_t hashA[32];
    legends_get_state_hash(handle_, hashA);

    // Create checkpoint B at t=3000
    legends_step_cycles(handle_, 2000, nullptr);
    size_t sizeB = 0;
    legends_save_state(handle_, nullptr, 0, &sizeB);
    std::vector<uint8_t> checkpointB(sizeB);
    legends_save_state(handle_, checkpointB.data(), sizeB, &sizeB);
    uint8_t hashB[32];
    legends_get_state_hash(handle_, hashB);

    // Create checkpoint C at t=6000
    legends_step_cycles(handle_, 3000, nullptr);
    size_t sizeC = 0;
    legends_save_state(handle_, nullptr, 0, &sizeC);
    std::vector<uint8_t> checkpointC(sizeC);
    legends_save_state(handle_, checkpointC.data(), sizeC, &sizeC);
    uint8_t hashC[32];
    legends_get_state_hash(handle_, hashC);

    // Restore in mixed order: C, A, B, A, C
    legends_load_state(handle_, checkpointC.data(), sizeC);
    uint8_t verifyC[32];
    legends_get_state_hash(handle_, verifyC);
    EXPECT_EQ(std::memcmp(hashC, verifyC, 32), 0) << "Restore C failed";

    legends_load_state(handle_, checkpointA.data(), sizeA);
    uint8_t verifyA1[32];
    legends_get_state_hash(handle_, verifyA1);
    EXPECT_EQ(std::memcmp(hashA, verifyA1, 32), 0) << "Restore A (first) failed";

    legends_load_state(handle_, checkpointB.data(), sizeB);
    uint8_t verifyB[32];
    legends_get_state_hash(handle_, verifyB);
    EXPECT_EQ(std::memcmp(hashB, verifyB, 32), 0) << "Restore B failed";

    legends_load_state(handle_, checkpointA.data(), sizeA);
    uint8_t verifyA2[32];
    legends_get_state_hash(handle_, verifyA2);
    EXPECT_EQ(std::memcmp(hashA, verifyA2, 32), 0) << "Restore A (second) failed";

    legends_load_state(handle_, checkpointC.data(), sizeC);
    uint8_t verifyC2[32];
    legends_get_state_hash(handle_, verifyC2);
    EXPECT_EQ(std::memcmp(hashC, verifyC2, 32), 0) << "Restore C (second) failed";
}
