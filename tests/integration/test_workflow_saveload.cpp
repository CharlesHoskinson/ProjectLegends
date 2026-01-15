/**
 * @file test_workflow_saveload.cpp
 * @brief Integration tests for save/load state workflows.
 *
 * Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <vector>

class SaveLoadWorkflowTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));

        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        legends_create(&config, &handle_);
    }

    void TearDown() override {
        if (handle_) legends_destroy(handle_);
        pal::Platform::shutdown();
    }

    std::vector<uint8_t> save_state() {
        size_t size;
        legends_save_state(handle_, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle_, buffer.data(), size, &size);
        return buffer;
    }

    std::vector<uint8_t> get_hash() {
        std::vector<uint8_t> hash(32);
        legends_get_state_hash(handle_, hash.data());
        return hash;
    }
};

// Basic round-trip: save -> load -> verify hash
TEST_F(SaveLoadWorkflowTest, BasicRoundTrip) {
    legends_step_cycles(handle_, 50000, nullptr);

    auto hash_before = get_hash();
    auto state = save_state();

    // Mutate state
    legends_step_cycles(handle_, 50000, nullptr);
    auto hash_mutated = get_hash();
    EXPECT_NE(hash_before, hash_mutated);

    // Load and verify
    legends_load_state(handle_, state.data(), state.size());
    auto hash_after = get_hash();

    EXPECT_EQ(hash_before, hash_after)
        << "TLA+ invariant: Obs(Deserialize(Serialize(S))) = Obs(S)";
}

// Round-trip with pending input
TEST_F(SaveLoadWorkflowTest, RoundTripWithPendingInput) {
    legends_step_cycles(handle_, 10000, nullptr);

    // Queue input (but don't process yet)
    legends_key_event(handle_, 0x1E, 1);  // A press

    auto hash_before = get_hash();
    auto state = save_state();

    // Step (processes input), then load
    legends_step_cycles(handle_, 50000, nullptr);
    legends_load_state(handle_, state.data(), state.size());

    auto hash_after = get_hash();
    EXPECT_EQ(hash_before, hash_after);
}

// Round-trip preserves emulated time
TEST_F(SaveLoadWorkflowTest, RoundTripPreservesTime) {
    legends_step_ms(handle_, 200, nullptr);

    uint64_t time_before;
    legends_get_emu_time(handle_, &time_before);
    EXPECT_GT(time_before, 0u);

    auto state = save_state();

    legends_step_ms(handle_, 100, nullptr);
    legends_load_state(handle_, state.data(), state.size());

    uint64_t time_after;
    legends_get_emu_time(handle_, &time_after);
    EXPECT_EQ(time_before, time_after);
}

// Round-trip preserves cycle count
TEST_F(SaveLoadWorkflowTest, RoundTripPreservesCycles) {
    legends_step_cycles(handle_, 123456, nullptr);

    uint64_t cycles_before;
    legends_get_total_cycles(handle_, &cycles_before);
    EXPECT_EQ(cycles_before, 123456u);

    auto state = save_state();

    legends_step_cycles(handle_, 50000, nullptr);
    legends_load_state(handle_, state.data(), state.size());

    uint64_t cycles_after;
    legends_get_total_cycles(handle_, &cycles_after);
    EXPECT_EQ(cycles_before, cycles_after);
}

// Multiple save points
TEST_F(SaveLoadWorkflowTest, MultipleSavePoints) {
    // Save point 1
    legends_step_cycles(handle_, 10000, nullptr);
    auto state1 = save_state();
    auto hash1 = get_hash();

    // Save point 2
    legends_step_cycles(handle_, 20000, nullptr);
    auto state2 = save_state();
    auto hash2 = get_hash();

    EXPECT_NE(hash1, hash2);

    // Load point 1
    legends_load_state(handle_, state1.data(), state1.size());
    EXPECT_EQ(get_hash(), hash1);

    // Load point 2
    legends_load_state(handle_, state2.data(), state2.size());
    EXPECT_EQ(get_hash(), hash2);
}

// Deterministic replay after load
TEST_F(SaveLoadWorkflowTest, DeterministicReplayAfterLoad) {
    legends_step_cycles(handle_, 50000, nullptr);
    auto state = save_state();

    // Replay 1: load and step
    legends_load_state(handle_, state.data(), state.size());
    legends_step_cycles(handle_, 25000, nullptr);
    auto hash_replay1 = get_hash();

    // Replay 2: load and step (same)
    legends_load_state(handle_, state.data(), state.size());
    legends_step_cycles(handle_, 25000, nullptr);
    auto hash_replay2 = get_hash();

    EXPECT_EQ(hash_replay1, hash_replay2)
        << "Same state + same steps = same result";
}
