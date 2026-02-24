/**
 * @file test_memory_api.cpp
 * @brief Tests for memory read/write C API (Phase A).
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_library.h"
#include "dosbox/dosbox_context.h"

class MemoryAPITest : public ::testing::Test {
protected:
    dosbox_lib_handle_t handle_ = nullptr;

    void SetUp() override {
        dosbox_lib_config_t config = DOSBOX_LIB_CONFIG_INIT;
        config.memory_kb = 640;
        auto err = dosbox_lib_create(&config, &handle_);
        ASSERT_EQ(err, DOSBOX_LIB_OK) << "Failed to create instance";
        err = dosbox_lib_init(handle_);
        ASSERT_EQ(err, DOSBOX_LIB_OK) << "Failed to init instance";
    }

    void TearDown() override {
        if (handle_) {
            dosbox_lib_destroy(handle_);
            handle_ = nullptr;
        }
    }
};

TEST_F(MemoryAPITest, WriteReadRoundTrip) {
    uint8_t data[] = {0xDE, 0xAD, 0xBE, 0xEF};
    auto err = dosbox_lib_write_memory(handle_, data, 0x8000, 4);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    uint8_t readback[4] = {};
    err = dosbox_lib_read_memory(handle_, 0x8000, readback, 4);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    EXPECT_EQ(memcmp(data, readback, 4), 0);
}

TEST_F(MemoryAPITest, WriteSingleByte) {
    uint8_t val = 0x42;
    auto err = dosbox_lib_write_memory(handle_, &val, 0x100, 1);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    uint8_t readback = 0;
    err = dosbox_lib_read_memory(handle_, 0x100, &readback, 1);
    ASSERT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(readback, 0x42);
}

TEST_F(MemoryAPITest, NullBufferReturnsError) {
    auto err = dosbox_lib_read_memory(handle_, 0x100, nullptr, 4);
    EXPECT_EQ(err, DOSBOX_LIB_ERR_NULL_POINTER);

    err = dosbox_lib_write_memory(handle_, nullptr, 0x100, 4);
    EXPECT_EQ(err, DOSBOX_LIB_ERR_NULL_POINTER);
}

TEST_F(MemoryAPITest, NullHandleReturnsError) {
    uint8_t buf[4] = {};
    auto err = dosbox_lib_read_memory(nullptr, 0x100, buf, 4);
    EXPECT_EQ(err, DOSBOX_LIB_ERR_NULL_HANDLE);

    err = dosbox_lib_write_memory(nullptr, buf, 0x100, 4);
    EXPECT_EQ(err, DOSBOX_LIB_ERR_NULL_HANDLE);
}
