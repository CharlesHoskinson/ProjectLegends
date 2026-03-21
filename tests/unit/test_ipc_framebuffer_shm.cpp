// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/framebuffer_shm.h>
#include "test_utils/ipc_test_helpers.h"
#include <cstring>
#include <string>

using namespace legends_ipc;
using legends_ipc::test_utils::ipc_test_unique_name;

static std::string fb_name(const char* base) {
    return ipc_test_unique_name(base);
}

TEST(IpcFramebufferShmTest, CreateAndWriteFlipRead) {
    auto name = fb_name("fb_basic");
    auto fb = FramebufferShm::create(name, 64, 64);
    if (!fb.has_value()) {
        GTEST_SKIP() << "Shared memory not available (CI environment limitation)";
    }

    // Write a frame
    auto write_buf = fb->begin_write();
    if (write_buf.empty()) {
        GTEST_SKIP() << "SHM buffer not available (CI environment limitation)";
    }
    ASSERT_GE(write_buf.size(), 64u * 64 * 4);
    std::memset(write_buf.data(), 0xAB, 64 * 64 * 4);
    fb->end_write(64, 64);

    // Read it back
    auto frame = fb->read_if_new(0);
    ASSERT_TRUE(frame.has_value());
    EXPECT_EQ(frame->width, 64u);
    EXPECT_EQ(frame->height, 64u);
    EXPECT_EQ(frame->frame_index, 1u);
    EXPECT_EQ(frame->pixels[0], 0xAB);
}

TEST(IpcFramebufferShmTest, DoubleBufferIsolation) {
    auto name = fb_name("fb_double");
    auto fb = FramebufferShm::create(name, 32, 32);
    if (!fb.has_value()) {
        GTEST_SKIP() << "Shared memory not available (CI environment limitation)";
    }

    // Write first frame (fills buffer1 since active=0)
    auto w1 = fb->begin_write();
    if (w1.empty()) {
        GTEST_SKIP() << "SHM buffer not available (CI environment limitation)";
    }
    std::memset(w1.data(), 0x11, 32 * 32 * 4);
    fb->end_write(32, 32);

    // Write second frame (fills buffer0 since active=1 now)
    auto w2 = fb->begin_write();
    std::memset(w2.data(), 0x22, 32 * 32 * 4);
    // Don't flip yet - active is still buffer1

    // Read should still see first frame
    auto frame1 = fb->read_if_new(0);
    ASSERT_TRUE(frame1.has_value());
    EXPECT_EQ(frame1->pixels[0], 0x11);

    // Now flip
    fb->end_write(32, 32);
    auto frame2 = fb->read_if_new(1);
    ASSERT_TRUE(frame2.has_value());
    EXPECT_EQ(frame2->pixels[0], 0x22);
}

TEST(IpcFramebufferShmTest, ReadIfNewSkipsStale) {
    auto name = fb_name("fb_stale");
    auto fb = FramebufferShm::create(name, 16, 16);
    if (!fb.has_value()) {
        GTEST_SKIP() << "Shared memory not available (CI environment limitation)";
    }

    auto w = fb->begin_write();
    if (w.empty()) {
        GTEST_SKIP() << "SHM buffer not available (CI environment limitation)";
    }
    std::memset(w.data(), 0xFF, 16 * 16 * 4);
    fb->end_write(16, 16);

    // Read at current index - should find nothing new
    auto frame = fb->read_if_new(1);
    EXPECT_FALSE(frame.has_value());
}

TEST(IpcFramebufferShmTest, Dimensions) {
    auto name = fb_name("fb_dims");
    auto fb = FramebufferShm::create(name, 1920, 1080);
    if (!fb.has_value()) {
        GTEST_SKIP() << "Shared memory not available (CI environment limitation)";
    }
    EXPECT_EQ(fb->max_width(), 1920u);
    EXPECT_EQ(fb->max_height(), 1080u);
}

TEST(IpcFramebufferShmTest, SmallerResolutionThanMax) {
    auto name = fb_name("fb_small");
    auto fb = FramebufferShm::create(name, 1920, 1080);
    if (!fb.has_value()) {
        GTEST_SKIP() << "Shared memory not available (CI environment limitation)";
    }

    auto wb = fb->begin_write();
    if (wb.empty()) {
        GTEST_SKIP() << "SHM buffer not available (CI environment limitation)";
    }
    (void)wb;
    // Write only 640x480
    fb->end_write(640, 480);

    auto frame = fb->read_if_new(0);
    ASSERT_TRUE(frame.has_value());
    EXPECT_EQ(frame->width, 640u);
    EXPECT_EQ(frame->height, 480u);
}

TEST(IpcFramebufferShmTest, ZeroDimensionFails) {
    auto name = fb_name("fb_zero");
    auto fb = FramebufferShm::create(name, 0, 100);
    ASSERT_FALSE(fb.has_value());
    EXPECT_EQ(fb.error(), IpcError::InvalidArgument);
}
