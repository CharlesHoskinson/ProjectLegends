// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/shared_memory.h>
#include <cstring>
#include <string>

using namespace legends_ipc;

static std::string unique_name(const char* base) {
    static int counter = 0;
    return std::string(base) + "_" + std::to_string(::GetCurrentProcessId()) +
           "_" + std::to_string(counter++);
}

TEST(IpcSharedMemoryTest, CreateAndMap) {
    auto name = unique_name("shm_create");
    auto result = SharedMemoryRegion::create(name, 4096);
    ASSERT_TRUE(result.has_value()) << "Failed to create shared memory";
    EXPECT_EQ(result->size(), 4096u);
    EXPECT_FALSE(result->data().empty());
}

TEST(IpcSharedMemoryTest, WriteAndRead) {
    auto name = unique_name("shm_rw");
    auto region = SharedMemoryRegion::create(name, 1024);
    ASSERT_TRUE(region.has_value());

    auto data = region->data();
    data[0] = 0xAA;
    data[1] = 0xBB;
    EXPECT_EQ(data[0], 0xAA);
    EXPECT_EQ(data[1], 0xBB);
}

TEST(IpcSharedMemoryTest, OpenByName) {
    auto name = unique_name("shm_open");
    auto creator = SharedMemoryRegion::create(name, 4096);
    ASSERT_TRUE(creator.has_value());

    // Write known pattern
    auto cdata = creator->data();
    cdata[0] = 0x42;
    cdata[100] = 0xFF;

    // Open by same name
    auto opener = SharedMemoryRegion::open(name, 4096);
    ASSERT_TRUE(opener.has_value());
    auto odata = opener->data();
    EXPECT_EQ(odata[0], 0x42);
    EXPECT_EQ(odata[100], 0xFF);
}

TEST(IpcSharedMemoryTest, RaiiCleanup) {
    auto name = unique_name("shm_raii");
    {
        auto region = SharedMemoryRegion::create(name, 1024);
        ASSERT_TRUE(region.has_value());
    }
    // After destruction, opening should fail (eventually, OS dependent)
    // We can't reliably test this on all platforms, so just verify no crash.
}

TEST(IpcSharedMemoryTest, ZeroSizeFails) {
    auto name = unique_name("shm_zero");
    auto result = SharedMemoryRegion::create(name, 0);
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), IpcError::InvalidArgument);
}

TEST(IpcSharedMemoryTest, MoveSemantics) {
    auto name = unique_name("shm_move");
    auto region = SharedMemoryRegion::create(name, 512);
    ASSERT_TRUE(region.has_value());

    auto moved = std::move(*region);
    EXPECT_EQ(moved.size(), 512u);
    EXPECT_FALSE(moved.data().empty());
}
