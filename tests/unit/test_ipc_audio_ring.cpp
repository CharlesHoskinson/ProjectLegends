// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/audio_ring.h>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif

using namespace legends_ipc;

static constexpr int kTotalFrames = 100000;

static std::string ring_name(const char* base) {
    static int counter = 0;
#ifdef _WIN32
    auto pid = static_cast<unsigned long>(GetCurrentProcessId());
#else
    auto pid = static_cast<unsigned long>(getpid());
#endif
    return std::string(base) + "_" + std::to_string(pid) +
           "_" + std::to_string(counter++);
}

TEST(IpcAudioRingTest, PushPopRoundTrip) {
    auto name = ring_name("ar_basic");
    auto ring = AudioRingBuffer::create(name, 256, 2, 44100);
    ASSERT_TRUE(ring.has_value());

    // Push 10 stereo frames (20 samples)
    std::vector<int16_t> input(20);
    for (int i = 0; i < 20; ++i) input[i] = static_cast<int16_t>(i * 100);

    uint32_t written = ring->push(input);
    EXPECT_EQ(written, 10u);

    // Pop them back
    std::vector<int16_t> output(20, 0);
    uint32_t read = ring->pop(output);
    EXPECT_EQ(read, 10u);
    for (int i = 0; i < 20; ++i)
        EXPECT_EQ(output[i], static_cast<int16_t>(i * 100));
}

TEST(IpcAudioRingTest, EmptyReturnsZero) {
    auto name = ring_name("ar_empty");
    auto ring = AudioRingBuffer::create(name, 128, 2, 44100);
    ASSERT_TRUE(ring.has_value());

    std::vector<int16_t> output(64, 0);
    uint32_t read = ring->pop(output);
    EXPECT_EQ(read, 0u);
}

TEST(IpcAudioRingTest, OverflowDropsOldest) {
    auto name = ring_name("ar_overflow");
    auto ring = AudioRingBuffer::create(name, 4, 2, 44100); // 4-frame capacity
    ASSERT_TRUE(ring.has_value());

    // Push 6 frames (overflows by 2)
    std::vector<int16_t> input(12);
    for (int i = 0; i < 12; ++i) input[i] = static_cast<int16_t>(i);
    ring->push(input);

    // Pop should get at most 4 frames (the latest 4)
    std::vector<int16_t> output(12, -1);
    uint32_t read = ring->pop(output);
    EXPECT_LE(read, 4u);
}

TEST(IpcAudioRingTest, StereoOrdering) {
    auto name = ring_name("ar_stereo");
    auto ring = AudioRingBuffer::create(name, 64, 2, 44100);
    ASSERT_TRUE(ring.has_value());

    // L=1000, R=2000 for one frame
    std::vector<int16_t> input = {1000, 2000};
    ring->push(input);

    std::vector<int16_t> output(2, 0);
    uint32_t read = ring->pop(output);
    EXPECT_EQ(read, 1u);
    EXPECT_EQ(output[0], 1000); // Left
    EXPECT_EQ(output[1], 2000); // Right
}

TEST(IpcAudioRingTest, WrapAround) {
    auto name = ring_name("ar_wrap");
    auto ring = AudioRingBuffer::create(name, 8, 2, 44100);
    ASSERT_TRUE(ring.has_value());

    // Push and pop multiple times to trigger wrap-around
    for (int iteration = 0; iteration < 5; ++iteration) {
        std::vector<int16_t> input(16); // 8 frames
        for (int i = 0; i < 16; ++i)
            input[i] = static_cast<int16_t>(iteration * 1000 + i);
        ring->push(input);

        std::vector<int16_t> output(16, 0);
        uint32_t read = ring->pop(output);
        EXPECT_EQ(read, 8u);
        for (int i = 0; i < 16; ++i)
            EXPECT_EQ(output[i], static_cast<int16_t>(iteration * 1000 + i));
    }
}

TEST(IpcAudioRingTest, Available) {
    auto name = ring_name("ar_avail");
    auto ring = AudioRingBuffer::create(name, 64, 2, 44100);
    ASSERT_TRUE(ring.has_value());
    EXPECT_EQ(ring->available(), 0u);

    std::vector<int16_t> input(20); // 10 frames
    ring->push(input);
    EXPECT_EQ(ring->available(), 10u);

    std::vector<int16_t> output(10); // pop 5 frames
    ring->pop(output);
    EXPECT_EQ(ring->available(), 5u);
}

TEST(IpcAudioRingTest, ConcurrentSPSCStress) {
    auto name = ring_name("ar_spsc");
    auto ring = AudioRingBuffer::create(name, 256, 2, 44100);
    ASSERT_TRUE(ring.has_value());

    std::atomic<int> total_popped{0};

    // Producer thread
    std::thread producer([&ring]() {
        std::vector<int16_t> chunk(64); // 32 frames at a time
        int frames_pushed = 0;
        while (frames_pushed < kTotalFrames) {
            int to_push = std::min(32, kTotalFrames - frames_pushed);
            for (int i = 0; i < to_push * 2; ++i)
                chunk[i] = static_cast<int16_t>((frames_pushed + i / 2) & 0x7FFF);
            ring->push(std::span<const int16_t>(chunk.data(), to_push * 2));
            frames_pushed += to_push;
        }
    });

    // Consumer thread
    std::thread consumer([&ring, &total_popped]() {
        std::vector<int16_t> buf(64);
        int popped = 0;
        while (popped < kTotalFrames) {
            uint32_t n = ring->pop(buf);
            popped += n;
            if (n == 0) std::this_thread::yield();
        }
        total_popped.store(popped);
    });

    producer.join();
    consumer.join();

    EXPECT_GE(total_popped.load(), kTotalFrames);
}

TEST(IpcAudioRingTest, ZeroCapacityFails) {
    auto name = ring_name("ar_zero");
    auto ring = AudioRingBuffer::create(name, 0, 2, 44100);
    ASSERT_FALSE(ring.has_value());
    EXPECT_EQ(ring.error(), IpcError::InvalidArgument);
}

TEST(IpcAudioRingTest, Properties) {
    auto name = ring_name("ar_props");
    auto ring = AudioRingBuffer::create(name, 2048, 2, 44100);
    ASSERT_TRUE(ring.has_value());
    EXPECT_EQ(ring->capacity_frames(), 2048u);
    EXPECT_EQ(ring->channels(), 2u);
    EXPECT_EQ(ring->sample_rate(), 44100u);
}
