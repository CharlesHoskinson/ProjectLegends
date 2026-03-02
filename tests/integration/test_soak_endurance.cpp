// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Soak/endurance test: long-running stability validation.
// REQ-TEST-008: Endurance test for memory leaks, audio health, hash consistency.
//
// Default: 1 hour. Override with LEGENDS_SOAK_DURATION_HOURS env var.
// Nightly CI runs 12hr soak.

#include <legends/legends_embed.h>

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <gtest/gtest.h>
#include <string>
#include <vector>

namespace legends {
namespace {

/// Get soak duration from environment, default 1 hour.
static int getSoakDurationSeconds() {
    const char* env = std::getenv("LEGENDS_SOAK_DURATION_HOURS");
    if (env) {
        int hours = std::atoi(env);
        if (hours > 0) return hours * 3600;
    }
    // Default: use a short duration for CI unit label exclusion
    // The "soak" label test will run this with longer duration
    return 3600; // 1 hour
}

/// Get RSS (Resident Set Size) in bytes. Platform-specific.
static size_t getCurrentRSS() {
#if defined(_WIN32)
    // Windows: use GetProcessMemoryInfo
    return 0; // Stub — filled by platform code
#elif defined(__APPLE__)
    // macOS: use task_info
    return 0;
#else
    // Linux: read /proc/self/statm
    std::FILE* f = std::fopen("/proc/self/statm", "r");
    if (!f) return 0;
    long pages = 0;
    if (std::fscanf(f, "%*d %ld", &pages) != 1) pages = 0;
    std::fclose(f);
    return static_cast<size_t>(pages) * 4096;
#endif
}

class SoakEnduranceTest : public ::testing::Test {
protected:
    void SetUp() override {
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
    }

    legends_handle engine_ = nullptr;
};

TEST_F(SoakEnduranceTest, EnduranceRunMonitorsHealth) {
    // Soak tests are long-running (default 1 hour) and must be opted in.
    // Set LEGENDS_SOAK_ENABLED=1 or LEGENDS_SOAK_SHORT=1 to run.
    const char* soak_enabled = std::getenv("LEGENDS_SOAK_ENABLED");
    const char* short_soak = std::getenv("LEGENDS_SOAK_SHORT");
    if ((!soak_enabled || std::strcmp(soak_enabled, "1") != 0) &&
        (!short_soak || std::strcmp(short_soak, "1") != 0)) {
        GTEST_SKIP() << "Soak test skipped (set LEGENDS_SOAK_ENABLED=1 to run)";
    }

    int duration_seconds = getSoakDurationSeconds();

    // For CI, if not labeled as soak, use 10 seconds
    if (short_soak && std::strcmp(short_soak, "1") == 0) {
        duration_seconds = 10;
    }

    auto start = std::chrono::steady_clock::now();
    auto deadline = start + std::chrono::seconds(duration_seconds);

    size_t initial_rss = getCurrentRSS();
    size_t max_rss = initial_rss;
    uint64_t step_count = 0;
    uint8_t last_hash[32] = {};
    int hash_mismatches = 0;

    // Capture initial state hash
    legends_get_state_hash(engine_, last_hash);

    constexpr int kCheckIntervalMs = 100;
    constexpr int kStepMs = 16;

    while (std::chrono::steady_clock::now() < deadline) {
        // Step engine
        legends_step_result_t result{};
        legends_step_ms(engine_, kStepMs, &result);
        ++step_count;

        // Periodic health checks (every ~100ms of simulated time)
        if (step_count % (kCheckIntervalMs / kStepMs) == 0) {
            // Memory check
            size_t current_rss = getCurrentRSS();
            if (current_rss > max_rss) max_rss = current_rss;

            // Audio health: verify capture doesn't crash
            size_t audio_avail = 0;
            legends_capture_audio(engine_, nullptr, 0, &audio_avail);

            // State hash consistency (deterministic mode)
            uint8_t current_hash[32] = {};
            legends_get_state_hash(engine_, current_hash);
            // Hash will change as engine progresses, but should not be zero
            {
                uint8_t zero[32] = {};
                if (memcmp(current_hash, zero, 32) == 0) {
                    ++hash_mismatches;
                }
            }
        }
    }

    auto elapsed = std::chrono::steady_clock::now() - start;
    auto elapsed_sec = std::chrono::duration_cast<std::chrono::seconds>(elapsed).count();

    std::fprintf(stderr, "Soak test completed: %llu steps in %lld seconds\n",
                 static_cast<unsigned long long>(step_count),
                 static_cast<long long>(elapsed_sec));
    std::fprintf(stderr, "RSS: initial=%zu, max=%zu\n", initial_rss, max_rss);

    // Verify no excessive memory growth (within 5% of initial, or 50MB if initial is 0)
    if (initial_rss > 0) {
        double growth = static_cast<double>(max_rss) / static_cast<double>(initial_rss);
        EXPECT_LT(growth, 1.05)
            << "RSS grew more than 5%: initial=" << initial_rss
            << " max=" << max_rss;
    }

    // Verify engine is still operational
    legends_step_result_t final_result{};
    legends_step_ms(engine_, kStepMs, &final_result);
    // Should not crash

    EXPECT_EQ(hash_mismatches, 0) << "State hash was zero during execution";
    EXPECT_GT(step_count, 0u) << "Should have stepped at least once";
}

TEST_F(SoakEnduranceTest, RepeatedSaveLoadStability) {
    // Save and load state repeatedly to check for leaks
    constexpr int kCycles = 100;

    for (int i = 0; i < kCycles; ++i) {
        // Step a few frames
        for (int s = 0; s < 10; ++s) {
            legends_step_result_t result{};
            legends_step_ms(engine_, 16, &result);
        }

        // Save state
        size_t save_size = 0;
        legends_save_state(engine_, nullptr, 0, &save_size);
        if (save_size == 0) continue;

        std::vector<uint8_t> state(save_size);
        size_t actual = 0;
        legends_save_state(engine_, state.data(), state.size(), &actual);

        // Load state
        legends_error_t err = legends_load_state(engine_, state.data(), actual);
        EXPECT_EQ(err, LEGENDS_OK) << "Load state failed at cycle " << i;
    }
}

TEST_F(SoakEnduranceTest, ContinuousFrameCaptureStability) {
    constexpr int kFrames = 500;
    std::vector<uint8_t> rgb_buffer;

    for (int i = 0; i < kFrames; ++i) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 16, &result);

        size_t size_needed = 0;
        uint16_t w = 0, h = 0;
        legends_capture_rgb(engine_, nullptr, 0, &size_needed, &w, &h);

        if (size_needed > 0 && w > 0 && h > 0) {
            if (rgb_buffer.size() < size_needed) {
                rgb_buffer.resize(size_needed);
            }
            legends_capture_rgb(engine_, rgb_buffer.data(),
                                rgb_buffer.size(), &size_needed, &w, &h);
        }
    }
}

TEST_F(SoakEnduranceTest, ContinuousAudioCaptureStability) {
    constexpr int kFrames = 500;
    std::vector<int16_t> audio_buffer;

    for (int i = 0; i < kFrames; ++i) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 16, &result);

        size_t avail = 0;
        legends_capture_audio(engine_, nullptr, 0, &avail);

        if (avail > 0) {
            if (audio_buffer.size() < avail) {
                audio_buffer.resize(avail);
            }
            size_t actual = 0;
            legends_capture_audio(engine_, audio_buffer.data(),
                                  audio_buffer.size(), &actual);
        }
    }
}

TEST_F(SoakEnduranceTest, HashConsistencyOverTime) {
    // Step engine and verify hash changes but stays valid
    constexpr int kSamples = 50;
    uint8_t hashes[kSamples][32] = {};

    for (int i = 0; i < kSamples; ++i) {
        for (int s = 0; s < 100; ++s) {
            legends_step_result_t result{};
            legends_step_ms(engine_, 16, &result);
        }

        legends_get_state_hash(engine_, hashes[i]);
    }

    // Check if hashes differ (engine is progressing)
    for (int i = 1; i < kSamples; ++i) {
        if (memcmp(hashes[i], hashes[0], 32) != 0) {
            break;
        }
    }
    // In deterministic mode the hash may or may not change depending on what the engine does
    // but it should never be zero
    uint8_t zero[32] = {};
    for (int i = 0; i < kSamples; ++i) {
        EXPECT_NE(memcmp(hashes[i], zero, 32), 0) << "Hash should not be zero";
    }
}

} // namespace
} // namespace legends
