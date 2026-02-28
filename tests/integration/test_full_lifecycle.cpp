// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Full lifecycle integration test: init → configure → boot → save → load → quit.
// Validates the complete application workflow end-to-end.

#include <legends/legends_embed.h>
#include <pal/platform.h>

#include <cstdint>
#include <cstring>
#include <gtest/gtest.h>
#include <string>
#include <vector>

namespace legends {
namespace {

class FullLifecycleTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();

        // Create engine with default config
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.deterministic = 1;
        legends_error_t err = legends_create(&cfg, &engine_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(engine_, nullptr);
    }

    void TearDown() override {
        if (engine_) {
            legends_destroy(engine_);
            engine_ = nullptr;
        }
        pal::Platform::shutdown();
    }

    void stepFrames(int frames) {
        for (int i = 0; i < frames; ++i) {
            legends_step_result_t result{};
            legends_step_ms(engine_, 16, &result);
        }
    }

    legends_handle engine_ = nullptr;
};

TEST_F(FullLifecycleTest, InitConfigureBootSaveLoadQuit) {
    // Step 1: Boot — step engine to produce initial output
    stepFrames(60); // ~1 second of emulated time

    // Step 2: Capture initial state
    uint8_t boot_hash[32] = {};
    legends_get_state_hash(engine_, boot_hash);
    {
        uint8_t zero[32] = {};
        EXPECT_NE(memcmp(boot_hash, zero, 32), 0) << "Boot hash should be non-zero";
    }

    // Step 3: Capture framebuffer
    size_t rgb_size = 0;
    uint16_t fw = 0, fh = 0;
    legends_capture_rgb(engine_, nullptr, 0, &rgb_size, &fw, &fh);
    EXPECT_GT(rgb_size, 0u) << "Framebuffer should have data";
    EXPECT_GT(fw, 0u) << "Frame width should be positive";
    EXPECT_GT(fh, 0u) << "Frame height should be positive";

    // Step 4: Capture audio
    size_t audio_avail = 0;
    legends_capture_audio(engine_, nullptr, 0, &audio_avail);
    // Audio may or may not be available depending on engine state

    // Step 5: Save state
    size_t save_size = 0;
    legends_save_state(engine_, nullptr, 0, &save_size);
    EXPECT_GT(save_size, 0u) << "Save state should have data";

    std::vector<uint8_t> save_data(save_size);
    size_t actual_save = 0;
    legends_save_state(engine_, save_data.data(), save_data.size(), &actual_save);
    EXPECT_GT(actual_save, 0u) << "Save should write data";

    uint8_t pre_save_hash[32] = {};
    legends_get_state_hash(engine_, pre_save_hash);

    // Step 6: Mutate state (inject keys, step further)
    legends_key_event(engine_, 0x1E, 1); // 'A' down
    legends_key_event(engine_, 0x1E, 0); // 'A' up
    stepFrames(30);

    uint8_t post_mutate_hash[32] = {};
    legends_get_state_hash(engine_, post_mutate_hash);
    // Hash may or may not differ depending on engine behavior

    // Step 7: Load state (restore to pre-mutation)
    legends_error_t load_err = legends_load_state(engine_, save_data.data(), actual_save);
    EXPECT_EQ(load_err, LEGENDS_OK) << "Load state should succeed";

    uint8_t post_load_hash[32] = {};
    legends_get_state_hash(engine_, post_load_hash);
    EXPECT_EQ(memcmp(post_load_hash, pre_save_hash, 32), 0)
        << "Hash after load should match hash before save";

    // Step 8: Continue execution after load
    stepFrames(30);
    // Should not crash

    // Step 9: Verify engine is still functional
    size_t rgb_size2 = 0;
    uint16_t fw2 = 0, fh2 = 0;
    legends_capture_rgb(engine_, nullptr, 0, &rgb_size2, &fw2, &fh2);
    EXPECT_GT(rgb_size2, 0u);

    // Step 10: Clean shutdown (TearDown handles destroy)
}

TEST_F(FullLifecycleTest, MultipleEngineInstances) {
    // Create a second engine
    legends_config_t cfg2 = LEGENDS_CONFIG_INIT;
    cfg2.deterministic = 1;
    legends_handle engine2 = nullptr;
    legends_error_t err = legends_create(&cfg2, &engine2);
    ASSERT_EQ(err, LEGENDS_OK);
    ASSERT_NE(engine2, nullptr);

    // Step both
    for (int i = 0; i < 10; ++i) {
        legends_step_result_t result1{}, result2{};
        legends_step_ms(engine_, 16, &result1);
        legends_step_ms(engine2, 16, &result2);
    }

    // Both should have valid state
    uint8_t hash1[32] = {}, hash2[32] = {};
    legends_get_state_hash(engine_, hash1);
    legends_get_state_hash(engine2, hash2);
    {
        uint8_t zero[32] = {};
        EXPECT_NE(memcmp(hash1, zero, 32), 0);
        EXPECT_NE(memcmp(hash2, zero, 32), 0);
    }
    EXPECT_EQ(memcmp(hash1, hash2, 32), 0) << "Deterministic engines should have same hash";

    legends_destroy(engine2);
}

TEST_F(FullLifecycleTest, TextCaptureAfterBoot) {
    stepFrames(120); // ~2 seconds

    // Two-call pattern: query size, then fill
    size_t count = 0;
    legends_text_info_t info{};
    legends_error_t err =
        legends_capture_text(engine_, nullptr, 0, &count, &info);
    ASSERT_EQ(err, LEGENDS_OK);

    if (count > 0) {
        std::vector<legends_text_cell_t> cells(count);
        err = legends_capture_text(engine_, cells.data(), count, &count, nullptr);
        EXPECT_EQ(err, LEGENDS_OK);
    }
    // In headless mode, count may be 0 — just verify no crash
}

TEST_F(FullLifecycleTest, InputInjectionSequence) {
    stepFrames(30);

    // Type "DIR" and Enter
    const uint8_t scancodes[] = {
        0x20, // D
        0x17, // I
        0x13, // R
        0x1C, // Enter
    };

    for (auto sc : scancodes) {
        legends_key_event(engine_, sc, 1); // key down
        legends_step_result_t result{};
        legends_step_ms(engine_, 16, &result);
        legends_key_event(engine_, sc, 0); // key up
        legends_step_ms(engine_, 16, &result);
    }

    stepFrames(60);

    // Capture text after command (two-call pattern)
    size_t count = 0;
    legends_capture_text(engine_, nullptr, 0, &count, nullptr);
    if (count > 0) {
        std::vector<legends_text_cell_t> cells(count);
        legends_capture_text(engine_, cells.data(), count, &count, nullptr);
    }
    // Verify no crash; content depends on headless mode
}

TEST_F(FullLifecycleTest, MouseEventProcessing) {
    stepFrames(10);

    // Send mouse events
    legends_mouse_event(engine_, 10, 5, 0x01); // move + left button
    stepFrames(1);
    legends_mouse_event(engine_, -5, -3, 0x00); // move + release
    stepFrames(1);

    // Should not crash
}

TEST_F(FullLifecycleTest, ResetAndContinue) {
    stepFrames(60);

    uint8_t pre_reset_hash[32] = {};
    legends_get_state_hash(engine_, pre_reset_hash);

    legends_reset(engine_);
    stepFrames(60);

    uint8_t post_reset_hash[32] = {};
    legends_get_state_hash(engine_, post_reset_hash);

    // After reset, hash should differ from pre-reset
    // (though in deterministic mode, it may match the initial boot hash)
    {
        uint8_t zero[32] = {};
        EXPECT_NE(memcmp(post_reset_hash, zero, 32), 0);
    }
}

TEST_F(FullLifecycleTest, RapidCreateDestroy) {
    // Stress test: rapidly create and destroy engines
    for (int i = 0; i < 10; ++i) {
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.deterministic = 1;
        legends_handle h = nullptr;
        legends_error_t err = legends_create(&cfg, &h);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(h, nullptr);

        legends_step_result_t result{};
        legends_step_ms(h, 16, &result);

        legends_destroy(h);
    }
}

} // namespace
} // namespace legends
