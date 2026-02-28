// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Integration tests for event callback firing (REQ-API-006).

#include <legends/legends_embed.h>
#include <pal/platform.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <gtest/gtest.h>
#include <string>

namespace legends {
namespace {

struct CallbackRecord {
    std::atomic<int> call_count{0};
    int last_event_type{0};
};

static void test_callback(int event_type, const void* /*data*/,
                           size_t /*data_size*/, void* userdata) {
    auto* rec = static_cast<CallbackRecord*>(userdata);
    rec->last_event_type = event_type;
    rec->call_count.fetch_add(1);
}

class EventCallbackTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();

        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.deterministic = 1;
        legends_error_t err = legends_create(&cfg, &engine_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(engine_, nullptr);

        // Step a few frames to stabilize
        for (int i = 0; i < 10; ++i) {
            legends_step_result_t result{};
            legends_step_ms(engine_, 16, &result);
        }

        mount_dir_ = std::filesystem::temp_directory_path() / "legends_event_cb_test";
        std::filesystem::create_directories(mount_dir_);
    }

    void TearDown() override {
        if (engine_) {
            legends_destroy(engine_);
            engine_ = nullptr;
        }
        pal::Platform::shutdown();
        std::filesystem::remove_all(mount_dir_);
    }

    legends_handle engine_ = nullptr;
    std::filesystem::path mount_dir_;
};

TEST_F(EventCallbackTest, RegisterAndReceiveDriveEvent) {
    CallbackRecord rec;

    legends_error_t err = legends_register_event_callback(
        engine_, LEGENDS_EVENT_DRIVE_ACTIVITY, test_callback, &rec);
    ASSERT_EQ(err, LEGENDS_OK);

    err = legends_mount_drive(engine_, 'D', mount_dir_.string().c_str(), 0);
    ASSERT_EQ(err, LEGENDS_OK);

    EXPECT_GE(rec.call_count.load(), 1);
    EXPECT_EQ(rec.last_event_type, LEGENDS_EVENT_DRIVE_ACTIVITY);
}

TEST_F(EventCallbackTest, UnmountFiresDriveEvent) {
    // Mount first
    legends_error_t err = legends_mount_drive(
        engine_, 'E', mount_dir_.string().c_str(), 0);
    ASSERT_EQ(err, LEGENDS_OK);

    // Register callback and unmount
    CallbackRecord rec;
    err = legends_register_event_callback(
        engine_, LEGENDS_EVENT_DRIVE_ACTIVITY, test_callback, &rec);
    ASSERT_EQ(err, LEGENDS_OK);

    err = legends_unmount_drive(engine_, 'E');
    ASSERT_EQ(err, LEGENDS_OK);

    EXPECT_GE(rec.call_count.load(), 1);
    EXPECT_EQ(rec.last_event_type, LEGENDS_EVENT_DRIVE_ACTIVITY);
}

TEST_F(EventCallbackTest, NullCallbackUnregisters) {
    CallbackRecord rec;

    legends_error_t err = legends_register_event_callback(
        engine_, LEGENDS_EVENT_DRIVE_ACTIVITY, test_callback, &rec);
    ASSERT_EQ(err, LEGENDS_OK);

    // Unregister by passing NULL
    err = legends_register_event_callback(
        engine_, LEGENDS_EVENT_DRIVE_ACTIVITY, nullptr, nullptr);
    ASSERT_EQ(err, LEGENDS_OK);

    // Mount should not fire callback
    err = legends_mount_drive(engine_, 'F', mount_dir_.string().c_str(), 0);
    ASSERT_EQ(err, LEGENDS_OK);

    EXPECT_EQ(rec.call_count.load(), 0);
}

TEST_F(EventCallbackTest, InvalidEventTypeRejected) {
    legends_error_t err = legends_register_event_callback(
        engine_, 0, test_callback, nullptr);
    EXPECT_NE(err, LEGENDS_OK);

    err = legends_register_event_callback(
        engine_, 99, test_callback, nullptr);
    EXPECT_NE(err, LEGENDS_OK);
}

} // namespace
} // namespace legends
