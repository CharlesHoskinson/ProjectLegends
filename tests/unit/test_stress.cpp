/**
 * @file test_stress.cpp
 * @brief Stress and performance tests.
 *
 * Tests:
 * - Rapid create/destroy cycles
 * - Long-running step sequences
 * - High-frequency input injection
 * - Memory stability under load
 * - Save/load under stress
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <vector>
#include <chrono>
#include <cstring>

class StressTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
    }

    void TearDown() override {
        pal::Platform::shutdown();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Create/Destroy Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, RapidCreateDestroy100x) {
    for (int i = 0; i < 100; ++i) {
        legends_handle handle = nullptr;
        legends_error_t err = legends_create(nullptr, &handle);
        ASSERT_EQ(err, LEGENDS_OK) << "Create failed on iteration " << i;
        ASSERT_NE(handle, nullptr);

        err = legends_destroy(handle);
        ASSERT_EQ(err, LEGENDS_OK) << "Destroy failed on iteration " << i;
    }
}

TEST_F(StressTest, RapidCreateStepDestroy50x) {
    for (int i = 0; i < 50; ++i) {
        legends_handle handle = nullptr;
        legends_create(nullptr, &handle);

        legends_step_result_t result;
        legends_step_ms(handle, 100, &result);
        EXPECT_GT(result.cycles_executed, 0u);

        legends_destroy(handle);
    }
}

TEST_F(StressTest, CreateWithDifferentConfigs) {
    for (int i = 0; i < 20; ++i) {
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = (i % 2);
        config.memory_kb = 640;

        legends_handle handle = nullptr;
        legends_error_t err = legends_create(&config, &handle);
        ASSERT_EQ(err, LEGENDS_OK) << "Create failed with config variant " << i;

        legends_destroy(handle);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Long-Running Step Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, ManySmallSteps) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Execute many small steps
    for (int i = 0; i < 1000; ++i) {
        legends_step_result_t result;
        legends_error_t err = legends_step_cycles(handle, 1000, &result);
        ASSERT_EQ(err, LEGENDS_OK) << "Step failed on iteration " << i;
    }

    uint64_t total_cycles;
    legends_get_total_cycles(handle, &total_cycles);
    EXPECT_EQ(total_cycles, 1000000u);

    legends_destroy(handle);
}

TEST_F(StressTest, MixedStepSizes) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    uint64_t expected_cycles = 0;
    for (int i = 0; i < 100; ++i) {
        uint64_t cycles = (i + 1) * 100;
        legends_step_result_t result;
        legends_step_cycles(handle, cycles, &result);
        expected_cycles += cycles;
    }

    uint64_t actual_cycles;
    legends_get_total_cycles(handle, &actual_cycles);
    EXPECT_EQ(actual_cycles, expected_cycles);

    legends_destroy(handle);
}

TEST_F(StressTest, ContinuousSteppingOneSecond) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    auto start = std::chrono::steady_clock::now();
    int iterations = 0;

    // Step for about 1 second of wall-clock time
    while (std::chrono::steady_clock::now() - start < std::chrono::seconds(1)) {
        legends_step_cycles(handle, 10000, nullptr);
        iterations++;
    }

    // Should have executed many iterations in 1 second
    EXPECT_GT(iterations, 100) << "Should complete many step iterations in 1 second";

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Input Injection Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, RapidKeyEvents) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Inject many key events rapidly
    for (int i = 0; i < 1000; ++i) {
        uint8_t scancode = static_cast<uint8_t>((i % 50) + 0x10);  // Various keys
        legends_key_event(handle, scancode, 1);  // Press
        legends_key_event(handle, scancode, 0);  // Release
    }

    // Step to process input
    legends_step_cycles(handle, 50000, nullptr);

    legends_destroy(handle);
}

TEST_F(StressTest, RapidMouseEvents) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Inject many mouse events
    for (int i = 0; i < 1000; ++i) {
        int16_t dx = static_cast<int16_t>(i % 10 - 5);
        int16_t dy = static_cast<int16_t>(i % 10 - 5);
        uint8_t buttons = static_cast<uint8_t>(i % 8);
        legends_mouse_event(handle, dx, dy, buttons);
    }

    // Step to process input
    legends_step_cycles(handle, 50000, nullptr);

    legends_destroy(handle);
}

TEST_F(StressTest, MixedInputTypes) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Interleave different input types
    for (int i = 0; i < 500; ++i) {
        legends_key_event(handle, 0x1E, 1);      // A press
        legends_mouse_event(handle, 1, 1, 0);    // Mouse move
        legends_key_event(handle, 0x1E, 0);      // A release
        legends_text_input(handle, "B");         // Text input
        legends_step_cycles(handle, 100, nullptr);
    }

    legends_destroy(handle);
}

TEST_F(StressTest, TextInputLongStrings) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Input progressively longer strings
    for (int len = 1; len <= 100; ++len) {
        std::string text(len, 'A');
        legends_text_input(handle, text.c_str());
        legends_step_cycles(handle, 1000, nullptr);
    }

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Capture Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, RepeatedTextCapture) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Capture text many times
    for (int i = 0; i < 100; ++i) {
        size_t count;
        legends_capture_text(handle, nullptr, 0, &count, nullptr);

        std::vector<legends_text_cell_t> cells(count);
        legends_error_t err = legends_capture_text(handle, cells.data(), count, &count, nullptr);
        ASSERT_EQ(err, LEGENDS_OK) << "Capture failed on iteration " << i;

        legends_step_cycles(handle, 1000, nullptr);
    }

    legends_destroy(handle);
}

TEST_F(StressTest, RepeatedRgbCapture) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Capture RGB many times
    for (int i = 0; i < 50; ++i) {
        size_t size;
        uint16_t width, height;
        legends_capture_rgb(handle, nullptr, 0, &size, &width, &height);

        std::vector<uint8_t> buffer(size);
        legends_error_t err = legends_capture_rgb(handle, buffer.data(), size, &size, &width, &height);
        ASSERT_EQ(err, LEGENDS_OK) << "RGB capture failed on iteration " << i;

        legends_step_cycles(handle, 1000, nullptr);
    }

    legends_destroy(handle);
}

TEST_F(StressTest, AlternatingCaptures) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    for (int i = 0; i < 100; ++i) {
        if (i % 2 == 0) {
            // Text capture
            size_t count;
            legends_capture_text(handle, nullptr, 0, &count, nullptr);
            std::vector<legends_text_cell_t> cells(count);
            legends_capture_text(handle, cells.data(), count, &count, nullptr);
        } else {
            // RGB capture
            size_t size;
            uint16_t width, height;
            legends_capture_rgb(handle, nullptr, 0, &size, &width, &height);
            std::vector<uint8_t> buffer(size);
            legends_capture_rgb(handle, buffer.data(), size, &size, &width, &height);
        }

        legends_step_cycles(handle, 500, nullptr);
    }

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Save/Load Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, RepeatedSaveLoad) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    for (int i = 0; i < 20; ++i) {
        // Step some
        legends_step_cycles(handle, 10000, nullptr);

        // Save
        size_t size;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> state(size);
        legends_save_state(handle, state.data(), size, &size);

        // Step more
        legends_step_cycles(handle, 10000, nullptr);

        // Load
        legends_error_t err = legends_load_state(handle, state.data(), size);
        ASSERT_EQ(err, LEGENDS_OK) << "Load failed on iteration " << i;
    }

    legends_destroy(handle);
}

TEST_F(StressTest, MultipleSavePoints) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::vector<std::vector<uint8_t>> save_points;

    // Create multiple save points
    for (int i = 0; i < 10; ++i) {
        legends_step_cycles(handle, 10000, nullptr);

        size_t size;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> state(size);
        legends_save_state(handle, state.data(), size, &size);
        save_points.push_back(std::move(state));
    }

    // Jump between save points
    for (int i = 0; i < 20; ++i) {
        int idx = i % save_points.size();
        legends_error_t err = legends_load_state(handle, save_points[idx].data(), save_points[idx].size());
        ASSERT_EQ(err, LEGENDS_OK) << "Load from save point " << idx << " failed";

        // Do some stepping
        legends_step_cycles(handle, 1000, nullptr);
    }

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Reset Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, RepeatedReset) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    for (int i = 0; i < 50; ++i) {
        // Step
        legends_step_cycles(handle, 50000, nullptr);

        // Verify time accumulated
        uint64_t time;
        legends_get_emu_time(handle, &time);
        EXPECT_GT(time, 0u);

        // Reset
        legends_error_t err = legends_reset(handle);
        ASSERT_EQ(err, LEGENDS_OK) << "Reset failed on iteration " << i;

        // Verify time reset
        legends_get_emu_time(handle, &time);
        EXPECT_EQ(time, 0u);
    }

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Hash Stability Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, HashStabilityUnderLoad) {
    legends_handle handle = nullptr;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;
    legends_create(&config, &handle);

    // Run deterministic trace
    legends_step_cycles(handle, 100000, nullptr);
    legends_key_event(handle, 0x1E, 1);
    legends_key_event(handle, 0x1E, 0);
    legends_step_cycles(handle, 100000, nullptr);

    // Capture hash multiple times - should be identical each time
    uint8_t hashes[10][32];
    for (int i = 0; i < 10; ++i) {
        legends_get_state_hash(handle, hashes[i]);
    }

    // All hashes should be identical
    for (int i = 1; i < 10; ++i) {
        EXPECT_EQ(std::memcmp(hashes[0], hashes[i], 32), 0)
            << "Hash at iteration " << i << " differs from initial";
    }

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Mixed Operations Stress
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(StressTest, MixedOperationsWorkflow) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    for (int i = 0; i < 50; ++i) {
        // Step
        legends_step_cycles(handle, 5000, nullptr);

        // Input
        legends_key_event(handle, 0x1E + (i % 10), 1);
        legends_key_event(handle, 0x1E + (i % 10), 0);

        // Step
        legends_step_cycles(handle, 5000, nullptr);

        // Capture
        size_t count;
        legends_capture_text(handle, nullptr, 0, &count, nullptr);

        // Check dirty
        int dirty;
        legends_is_frame_dirty(handle, &dirty);

        // Get cursor
        uint8_t x, y;
        int visible;
        legends_get_cursor(handle, &x, &y, &visible);

        // Get timing
        uint64_t time, cycles;
        legends_get_emu_time(handle, &time);
        legends_get_total_cycles(handle, &cycles);
    }

    legends_destroy(handle);
}

TEST_F(StressTest, FullWorkflowSimulation) {
    // Simulate a realistic AI agent workflow
    legends_handle handle = nullptr;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;
    legends_create(&config, &handle);

    for (int frame = 0; frame < 30; ++frame) {
        // Step 100ms
        legends_step_ms(handle, 100, nullptr);

        // Capture screen
        size_t count;
        legends_capture_text(handle, nullptr, 0, &count, nullptr);
        std::vector<legends_text_cell_t> cells(count);
        legends_capture_text(handle, cells.data(), count, &count, nullptr);

        // Check if frame is dirty
        int dirty;
        legends_is_frame_dirty(handle, &dirty);

        // Simulate AI deciding to type something
        if (frame % 5 == 0) {
            legends_text_input(handle, "DIR\n");
        }

        // Occasionally save state
        if (frame % 10 == 0) {
            size_t size;
            legends_save_state(handle, nullptr, 0, &size);
            std::vector<uint8_t> state(size);
            legends_save_state(handle, state.data(), size, &size);
        }
    }

    legends_destroy(handle);
}

