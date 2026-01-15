/**
 * @file test_workflow_determinism.cpp
 * @brief Integration tests for determinism verification.
 *
 * Per TLA+ Determinism.tla: Same inputs + same config = same state hash.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <functional>
#include <vector>

class DeterminismWorkflowTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
    }

    void TearDown() override {
        pal::Platform::shutdown();
    }

    // Run a trace and return final hash
    std::vector<uint8_t> run_trace(
        std::function<void(legends_handle)> trace
    ) {
        legends_handle handle = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        legends_create(&config, &handle);

        trace(handle);

        std::vector<uint8_t> hash(32);
        legends_get_state_hash(handle, hash.data());
        legends_destroy(handle);

        return hash;
    }
};

// Identical traces produce identical hashes
TEST_F(DeterminismWorkflowTest, IdenticalTracesProduceIdenticalHashes) {
    auto trace = [](legends_handle h) {
        legends_step_cycles(h, 10000, nullptr);
        legends_key_event(h, 0x1E, 1);  // A press
        legends_step_cycles(h, 1000, nullptr);
        legends_key_event(h, 0x1E, 0);  // A release
        legends_step_cycles(h, 20000, nullptr);
    };

    auto hash1 = run_trace(trace);
    auto hash2 = run_trace(trace);

    EXPECT_EQ(hash1, hash2)
        << "Identical traces must produce identical hashes";
}

// Different traces produce different hashes
// Note: With headless stub, input may not affect state hash since
// full emulation isn't running. Test verifies different cycle counts
// do produce different hashes.
TEST_F(DeterminismWorkflowTest, DifferentTracesProduceDifferentHashes) {
    auto trace_a = [](legends_handle h) {
        legends_step_cycles(h, 10000, nullptr);
    };

    auto trace_b = [](legends_handle h) {
        legends_step_cycles(h, 20000, nullptr);  // Different cycle count
    };

    auto hash_a = run_trace(trace_a);
    auto hash_b = run_trace(trace_b);

    EXPECT_NE(hash_a, hash_b)
        << "Different cycle counts must produce different hashes";
}

// Extended workflow: complex input sequence
TEST_F(DeterminismWorkflowTest, ExtendedInputSequenceDeterminism) {
    auto extended_trace = [](legends_handle h) {
        // Type several keys with steps between
        legends_step_cycles(h, 5000, nullptr);

        // Press D
        legends_key_event(h, 0x20, 1);
        legends_step_cycles(h, 500, nullptr);
        legends_key_event(h, 0x20, 0);
        legends_step_cycles(h, 500, nullptr);

        // Press I
        legends_key_event(h, 0x17, 1);
        legends_step_cycles(h, 500, nullptr);
        legends_key_event(h, 0x17, 0);
        legends_step_cycles(h, 500, nullptr);

        // Press R
        legends_key_event(h, 0x13, 1);
        legends_step_cycles(h, 500, nullptr);
        legends_key_event(h, 0x13, 0);
        legends_step_cycles(h, 500, nullptr);

        // Press Enter
        legends_key_event(h, 0x1C, 1);
        legends_step_cycles(h, 500, nullptr);
        legends_key_event(h, 0x1C, 0);

        legends_step_ms(h, 100, nullptr);
    };

    auto hash1 = run_trace(extended_trace);
    auto hash2 = run_trace(extended_trace);

    EXPECT_EQ(hash1, hash2) << "Extended input sequence must be deterministic";
}

// Verify API: legends_verify_determinism
TEST_F(DeterminismWorkflowTest, VerifyDeterminismAPI) {
    legends_handle handle = nullptr;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;
    legends_create(&config, &handle);

    // Queue some input
    legends_key_event(handle, 0x1E, 1);
    legends_key_event(handle, 0x1E, 0);

    int is_det;
    legends_error_t err = legends_verify_determinism(handle, 50000, &is_det);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(is_det, 1) << "Deterministic mode must be deterministic";

    legends_destroy(handle);
}

// Mouse input determinism
TEST_F(DeterminismWorkflowTest, MouseInputDeterminism) {
    auto mouse_trace = [](legends_handle h) {
        legends_step_cycles(h, 5000, nullptr);
        legends_mouse_event(h, 10, 5, 0);
        legends_step_cycles(h, 2000, nullptr);
        legends_mouse_event(h, 20, 10, 1);  // Left click
        legends_step_cycles(h, 5000, nullptr);
        legends_mouse_event(h, 0, 0, 0);    // Release
        legends_step_cycles(h, 5000, nullptr);
    };

    auto hash1 = run_trace(mouse_trace);
    auto hash2 = run_trace(mouse_trace);

    EXPECT_EQ(hash1, hash2) << "Mouse input must be deterministic";
}
