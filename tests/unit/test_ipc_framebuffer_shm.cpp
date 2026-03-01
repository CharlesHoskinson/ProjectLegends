// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/framebuffer_shm.h>
#include <cstring>
#include <string>

#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif

using namespace legends_ipc;

static uint32_t current_pid() {
#ifdef _WIN32
    return static_cast<uint32_t>(::GetCurrentProcessId());
#else
    return static_cast<uint32_t>(::getpid());
#endif
}

static std::string fb_name(const char* base) {
    static int counter = 0;
    return std::string(base) + "_" + std::to_string(current_pid()) +
           "_" + std::to_string(counter++);
}

TEST(IpcFramebufferShmTest, CreateAndWriteFlipRead) {
    auto name = fb_name("fb_basic");
    auto fb = FramebufferShm::create(name, 64, 64);
    ASSERT_TRUE(fb.has_value());

    // Write a frame
    auto write_buf = fb->begin_write();
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
    ASSERT_TRUE(fb.has_value());

    // Write first frame (fills buffer1 since active=0)
    auto w1 = fb->begin_write();
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
    ASSERT_TRUE(fb.has_value());

    auto w = fb->begin_write();
    std::memset(w.data(), 0xFF, 16 * 16 * 4);
    fb->end_write(16, 16);

    // Read at current index - should find nothing new
    auto frame = fb->read_if_new(1);
    EXPECT_FALSE(frame.has_value());
}

TEST(IpcFramebufferShmTest, Dimensions) {
    auto name = fb_name("fb_dims");
    auto fb = FramebufferShm::create(name, 1920, 1080);
    ASSERT_TRUE(fb.has_value());
    EXPECT_EQ(fb->max_width(), 1920u);
    EXPECT_EQ(fb->max_height(), 1080u);
}

TEST(IpcFramebufferShmTest, SmallerResolutionThanMax) {
    auto name = fb_name("fb_small");
    auto fb = FramebufferShm::create(name, 1920, 1080);
    ASSERT_TRUE(fb.has_value());

    (void)fb->begin_write();
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
