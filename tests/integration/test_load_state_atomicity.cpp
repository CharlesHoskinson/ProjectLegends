/**
 * @file test_load_state_atomicity.cpp
 * @brief Integration tests for load state atomicity (finding F2).
 *
 * Verifies that a failed legends_load_state call does not corrupt
 * the legends-layer state. After a failed load, the state hash must
 * remain identical to its value before the call.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <vector>

class LoadAtomicityTest : public ::testing::Test {
protected:
    legends_handle h_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();
        legends_create(nullptr, &h_);
        legends_step_ms(h_, 50, nullptr);
    }

    void TearDown() override {
        if (h_) legends_destroy(h_);
        pal::Platform::shutdown();
    }

    std::vector<uint8_t> save_state() {
        size_t size;
        legends_save_state(h_, nullptr, 0, &size);
        std::vector<uint8_t> state(size);
        legends_save_state(h_, state.data(), size, &size);
        return state;
    }
};

// A failed load (V3 path) must not mutate legends-layer state.
TEST_F(LoadAtomicityTest, FailedLoadDoesNotMutateLegendsState) {
    // Save a good state from the initial position.
    auto good_state = save_state();

    // Advance the emulator so current state differs from the saved one.
    legends_step_ms(h_, 200, nullptr);

    // Capture hash of the current (post-advance) state.
    uint8_t hash_before[32];
    legends_get_state_hash(h_, hash_before);

    // Build a corrupt state: flip bytes in the data section (after the
    // 64-byte header) so legend/engine deserialization will reject it.
    auto bad_state = good_state;
    for (size_t i = 64; i < std::min(bad_state.size(), size_t(128)); ++i) {
        bad_state[i] ^= 0xFF;
    }

    // Attempt to load the corrupt state -- should fail.
    auto err = legends_load_state(h_, bad_state.data(), bad_state.size());
    EXPECT_NE(err, LEGENDS_OK);

    // The current state must be completely unchanged.
    uint8_t hash_after[32];
    legends_get_state_hash(h_, hash_after);

    EXPECT_EQ(memcmp(hash_before, hash_after, 32), 0)
        << "State was mutated by a failed load - not atomic!";
}

// Same atomicity guarantee when the load triggers the V2 code path.
TEST_F(LoadAtomicityTest, V2FailedLoadPreservesState) {
    auto good_state = save_state();

    // Advance so current state differs from saved state.
    legends_step_ms(h_, 200, nullptr);

    uint8_t hash_before[32];
    legends_get_state_hash(h_, hash_before);

    // Rewrite the version field to 2 (offset 4) to force the V2 path,
    // then corrupt the data section.
    auto bad_state = good_state;
    uint32_t v2 = 2;
    std::memcpy(bad_state.data() + 4, &v2, 4);
    for (size_t i = 64; i < std::min(bad_state.size(), size_t(128)); ++i) {
        bad_state[i] ^= 0xFF;
    }

    auto err = legends_load_state(h_, bad_state.data(), bad_state.size());
    EXPECT_NE(err, LEGENDS_OK);

    uint8_t hash_after[32];
    legends_get_state_hash(h_, hash_after);

    EXPECT_EQ(memcmp(hash_before, hash_after, 32), 0)
        << "V2 state was mutated by a failed load - not atomic!";
}
