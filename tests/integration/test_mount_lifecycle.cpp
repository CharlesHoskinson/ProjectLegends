// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Integration tests for mount/unmount lifecycle via the C API.
// REQ-MOUNT-001, REQ-MOUNT-002, REQ-API-004

#include <legends/legends_embed.h>
#include <pal/platform.h>

#include <cstdint>
#include <filesystem>
#include <gtest/gtest.h>
#include <string>

namespace legends {
namespace {

class MountLifecycleTest : public ::testing::Test {
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

        // Step a few frames so the engine is in a stable state
        for (int i = 0; i < 10; ++i) {
            legends_step_result_t result{};
            legends_step_ms(engine_, 16, &result);
        }

        // Create a temporary directory for mounting
        mount_dir_ = std::filesystem::temp_directory_path() / "legends_mount_integ";
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

TEST_F(MountLifecycleTest, MountHostDirectory_ViaAPI) {
    legends_error_t err = legends_mount_drive(
        engine_, 'D', mount_dir_.string().c_str(), 0);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(MountLifecycleTest, UnmountDrive_ViaAPI) {
    legends_error_t err = legends_mount_drive(
        engine_, 'E', mount_dir_.string().c_str(), 0);
    ASSERT_EQ(err, LEGENDS_OK);

    err = legends_unmount_drive(engine_, 'E');
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(MountLifecycleTest, MountInvalidPath_ReturnsError) {
    legends_error_t err = legends_mount_drive(
        engine_, 'D', "/nonexistent/path/12345", 0);
    EXPECT_EQ(err, LEGENDS_ERR_IO_FAILED);
}

TEST_F(MountLifecycleTest, MountInvalidLetter_ReturnsError) {
    legends_error_t err = legends_mount_drive(
        engine_, '1', mount_dir_.string().c_str(), 0);
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_CONFIG);
}

TEST_F(MountLifecycleTest, NullHandle_ReturnsError) {
    legends_error_t err = legends_mount_drive(
        nullptr, 'D', mount_dir_.string().c_str(), 0);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);

    err = legends_unmount_drive(nullptr, 'D');
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

} // namespace
} // namespace legends
