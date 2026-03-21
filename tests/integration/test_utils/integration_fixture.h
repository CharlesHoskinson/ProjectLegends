// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Shared integration test fixtures for legends emulator tests.

#ifndef LEGENDS_TEST_UTILS_INTEGRATION_FIXTURE_H
#define LEGENDS_TEST_UTILS_INTEGRATION_FIXTURE_H

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>

#include <cstring>
#include <vector>

namespace legends {
namespace test_utils {

// ═══════════════════════════════════════════════════════════════════════════════
// LegendsIntegrationTest: Base fixture with Platform init + create/destroy.
// ═══════════════════════════════════════════════════════════════════════════════

class LegendsIntegrationTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();
    }

    void TearDown() override {
        if (handle_) {
            legends_destroy(handle_);
            handle_ = nullptr;
        }
        pal::Platform::shutdown();
    }

    // ── Shared helpers ──────────────────────────────────────────────────

    /// Save complete machine state to a byte vector.
    std::vector<uint8_t> save_state() {
        size_t size = 0;
        legends_error_t err = legends_save_state(handle_, nullptr, 0, &size);
        EXPECT_EQ(err, LEGENDS_OK);
        std::vector<uint8_t> buf(size);
        err = legends_save_state(handle_, buf.data(), buf.size(), &size);
        EXPECT_EQ(err, LEGENDS_OK);
        return buf;
    }

    /// Get 32-byte SHA-256 hash of current machine state.
    std::vector<uint8_t> get_hash() {
        std::vector<uint8_t> hash(32);
        legends_error_t err = legends_get_state_hash(handle_, hash.data());
        EXPECT_EQ(err, LEGENDS_OK);
        return hash;
    }

    /// Step the emulator forward by the given number of milliseconds.
    void stepFrames(uint32_t ms) {
        legends_step_ms(handle_, ms, nullptr);
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// LegendsConfiguredTest: Creates an instance with deterministic=1 by default.
// ═══════════════════════════════════════════════════════════════════════════════

class LegendsConfiguredTest : public LegendsIntegrationTest {
protected:
    void SetUp() override {
        LegendsIntegrationTest::SetUp();

        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        legends_error_t err = legends_create(&config, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }
};

} // namespace test_utils
} // namespace legends

#endif // LEGENDS_TEST_UTILS_INTEGRATION_FIXTURE_H
