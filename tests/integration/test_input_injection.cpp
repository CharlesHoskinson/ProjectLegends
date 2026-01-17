/**
 * @file test_input_injection.cpp
 * @brief Integration tests for input injection.
 *
 * Tests that:
 * - Input events are forwarded to the engine
 * - Device interleaving order is preserved
 * - Deterministic replay works with input
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <vector>

class InputInjectionTest : public ::testing::Test {
protected:
    legends_handle h_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
        legends_create(nullptr, &h_);
        // Step to initialize
        legends_step_ms(h_, 50, nullptr);
    }

    void TearDown() override {
        if (h_) legends_destroy(h_);
        pal::Platform::shutdown();
    }

    void get_hash(uint8_t hash[32]) {
        legends_get_state_hash(h_, hash);
    }

    std::vector<uint8_t> save_state() {
        size_t size;
        legends_save_state(h_, nullptr, 0, &size);
        std::vector<uint8_t> state(size);
        legends_save_state(h_, state.data(), size, &size);
        return state;
    }

    void load_state(const std::vector<uint8_t>& state) {
        legends_load_state(h_, state.data(), state.size());
    }
};

// Verify key events affect engine state (not just time)
TEST_F(InputInjectionTest, KeyEventForwardedToEngine) {
    // Baseline: step with no input
    auto state0 = save_state();
    legends_step_cycles(h_, 1000, nullptr);
    uint8_t hash_no_input[32];
    get_hash(hash_no_input);

    // Restore and step with input using same cycles
    load_state(state0);
    legends_key_event(h_, 0x1E, 1);    // Press
    legends_key_event(h_, 0x1E, 0);    // Release
    legends_step_cycles(h_, 1000, nullptr);
    uint8_t hash_with_input[32];
    get_hash(hash_with_input);

    // If input is forwarded to engine, hashes should differ
    EXPECT_NE(memcmp(hash_no_input, hash_with_input, 32), 0);
}

// Verify state hash accounts for pending input contents
TEST_F(InputInjectionTest, PendingInputAffectsStateHash) {
    auto state0 = save_state();

    // Queue scancode A
    legends_key_event(h_, 0x1E, 1);
    uint8_t hash_a[32];
    get_hash(hash_a);

    // Restore and queue scancode B
    load_state(state0);
    legends_key_event(h_, 0x30, 1);
    uint8_t hash_b[32];
    get_hash(hash_b);

    // Hash should differ because pending input differs
    EXPECT_NE(std::memcmp(hash_a, hash_b, 32), 0);
}

// Verify input order is preserved across device types
TEST_F(InputInjectionTest, InputOrderPreserved) {
    // Save initial state
    auto state0 = save_state();

    // Interleave keyboard and mouse events
    legends_key_event(h_, 0x1E, 1);      // Key A down
    legends_mouse_event(h_, 10, 0, 0);   // Mouse move
    legends_key_event(h_, 0x1E, 0);      // Key A up
    legends_mouse_event(h_, -10, 0, 0);  // Mouse move back

    // Step to process input
    legends_step_ms(h_, 100, nullptr);

    uint8_t hash1[32];
    get_hash(hash1);

    // Restore and replay same sequence
    load_state(state0);
    legends_key_event(h_, 0x1E, 1);
    legends_mouse_event(h_, 10, 0, 0);
    legends_key_event(h_, 0x1E, 0);
    legends_mouse_event(h_, -10, 0, 0);
    legends_step_ms(h_, 100, nullptr);

    uint8_t hash2[32];
    get_hash(hash2);

    // Must be deterministic - same input sequence = same result
    EXPECT_EQ(memcmp(hash1, hash2, 32), 0);
}

// Verify input queue is drained on step
TEST_F(InputInjectionTest, InputQueueDrainedOnStep) {
    // Queue a key event without stepping
    legends_key_event(h_, 0x1E, 1);

    // Save state and read input event count
    auto state_before = save_state();
    struct SaveStateHeader {
        uint32_t magic;
        uint32_t version;
        uint32_t total_size;
        uint32_t checksum;
        uint32_t time_offset;
        uint32_t cpu_offset;
        uint32_t pic_offset;
        uint32_t dma_offset;
        uint32_t event_queue_offset;
        uint32_t input_offset;
        uint32_t frame_offset;
        uint32_t engine_offset;
        uint32_t engine_size;
        uint32_t _reserved[3];
    };
    struct SaveStateInputHeader {
        uint32_t event_count;
        uint32_t next_sequence_lo;
        uint32_t next_sequence_hi;
        uint32_t _reserved;
    };
    static_assert(sizeof(SaveStateHeader) == 64, "SaveStateHeader size must be 64");
    const auto* header_before = reinterpret_cast<const SaveStateHeader*>(state_before.data());
    const auto* input_before = reinterpret_cast<const SaveStateInputHeader*>(
        state_before.data() + header_before->input_offset);
    EXPECT_GT(input_before->event_count, 0u);

    // Step to drain queue
    legends_step_cycles(h_, 1000, nullptr);

    auto state_after = save_state();
    const auto* header_after = reinterpret_cast<const SaveStateHeader*>(state_after.data());
    const auto* input_after = reinterpret_cast<const SaveStateInputHeader*>(
        state_after.data() + header_after->input_offset);
    EXPECT_EQ(input_after->event_count, 0u);
}

// Verify extended keys work (E0-prefixed)
TEST_F(InputInjectionTest, ExtendedKeyE0Prefix) {
    uint8_t hash_before[32];
    get_hash(hash_before);

    // Arrow keys (E0-prefixed)
    legends_key_event_ext(h_, 0x4D, 1);  // Right arrow down
    legends_step_cycles(h_, 10000, nullptr);
    legends_key_event_ext(h_, 0x4D, 0);  // Right arrow up
    legends_step_cycles(h_, 10000, nullptr);

    // Verify no crash and state changed (timing at least)
    uint8_t hash_after[32];
    get_hash(hash_after);
    EXPECT_NE(memcmp(hash_before, hash_after, 32), 0);
}

// Verify text input works
TEST_F(InputInjectionTest, TextInputTypesString) {
    uint8_t hash_before[32];
    get_hash(hash_before);

    legends_text_input(h_, "HELLO");
    legends_step_ms(h_, 100, nullptr);

    uint8_t hash_after[32];
    get_hash(hash_after);

    // State should change from input
    EXPECT_NE(memcmp(hash_before, hash_after, 32), 0);
}

// Verify mouse events work
TEST_F(InputInjectionTest, MouseMovement) {
    uint8_t hash_before[32];
    get_hash(hash_before);

    legends_mouse_event(h_, 10, -5, 0x01);  // Move + left button
    legends_step_cycles(h_, 10000, nullptr);
    legends_mouse_event(h_, 0, 0, 0);       // Release
    legends_step_cycles(h_, 10000, nullptr);

    uint8_t hash_after[32];
    get_hash(hash_after);

    // State should change
    EXPECT_NE(memcmp(hash_before, hash_after, 32), 0);
}

// Deterministic replay after load
TEST_F(InputInjectionTest, DeterministicReplayAfterLoad) {
    // Save initial state S0
    auto state0 = save_state();

    // Inject input sequence and step
    legends_key_event(h_, 0x1E, 1);
    legends_key_event(h_, 0x1E, 0);
    legends_step_ms(h_, 100, nullptr);

    uint8_t hash1[32];
    get_hash(hash1);

    // Restore S0 and replay
    load_state(state0);
    legends_key_event(h_, 0x1E, 1);
    legends_key_event(h_, 0x1E, 0);
    legends_step_ms(h_, 100, nullptr);

    uint8_t hash2[32];
    get_hash(hash2);

    EXPECT_EQ(memcmp(hash1, hash2, 32), 0);
}

// Prove input affects state beyond just time passing
// This is the critical test - it proves input actually reaches the engine
TEST_F(InputInjectionTest, InputAffectsStateBeyondTime) {
    // Save initial state S0
    auto state0 = save_state();

    // Path A: Step WITH input
    legends_key_event(h_, 0x1E, 1);  // Press 'A'
    legends_key_event(h_, 0x1E, 0);  // Release 'A'
    legends_step_ms(h_, 100, nullptr);  // Process input

    uint8_t hash_with_input[32];
    get_hash(hash_with_input);

    // Restore to S0
    load_state(state0);

    // Path B: Step WITHOUT input, same duration
    legends_step_ms(h_, 100, nullptr);  // Same time, no input

    uint8_t hash_without_input[32];
    get_hash(hash_without_input);

    // These hashes must differ if input actually affects state
    // If equal, input isn't reaching the engine - only time changed
    EXPECT_NE(memcmp(hash_with_input, hash_without_input, 32), 0)
        << "Input should affect state beyond just time passing. "
        << "If hashes are equal, input may not be reaching the engine.";
}

// Queue capacity enforcement
TEST_F(InputInjectionTest, QueueCapacityEnforced) {
    // Fill queue to capacity (320 - 1 = 319 events)
    for (int i = 0; i < 319; ++i) {
        legends_error_t err = legends_key_event(h_, static_cast<uint8_t>(0x1E), i % 2);
        EXPECT_EQ(err, LEGENDS_OK) << "Failed at event " << i;
    }

    // 320th should fail (queue full)
    legends_error_t err = legends_key_event(h_, 0x1E, 1);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
}
