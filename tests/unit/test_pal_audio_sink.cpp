// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors

#include <gtest/gtest.h>
#include "pal/platform.h"
#include "pal/audio_sink.h"
#include <vector>
#include <cmath>

namespace pal {
namespace {

class PalAudioSinkTest : public ::testing::Test {
protected:
    void SetUp() override {
        Platform::shutdown();
        ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
        sink_ = Platform::createAudioSink();
        ASSERT_NE(sink_, nullptr);
    }

    void TearDown() override {
        sink_.reset();
        Platform::shutdown();
    }

    std::unique_ptr<IAudioSink> sink_;

    // Generate a sine wave for testing
    std::vector<int16_t> generateSineWave(uint32_t frames, uint16_t channels = 2) {
        std::vector<int16_t> samples(frames * channels);
        for (uint32_t i = 0; i < frames; ++i) {
            int16_t sample = static_cast<int16_t>(std::sin(i * 0.1) * 16000);
            for (uint16_t c = 0; c < channels; ++c) {
                samples[i * channels + c] = sample;
            }
        }
        return samples;
    }
};

// ═══════════════════════════════════════════════════════════════════════════
// Lifecycle Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalAudioSinkTest, OpenWithDefaultConfig) {
    AudioConfig config;
    Result result = sink_->open(config);
    EXPECT_EQ(result, Result::Success);
    EXPECT_TRUE(sink_->isOpen());
}

TEST_F(PalAudioSinkTest, OpenWith48000Hz) {
    AudioConfig config;
    config.sample_rate = 48000;
    Result result = sink_->open(config);
    EXPECT_EQ(result, Result::Success);

    AudioConfig actual = sink_->getConfig();
    EXPECT_EQ(actual.sample_rate, 48000u);
}

TEST_F(PalAudioSinkTest, OpenWithMono) {
    AudioConfig config;
    config.channels = 1;
    Result result = sink_->open(config);
    EXPECT_EQ(result, Result::Success);

    AudioConfig actual = sink_->getConfig();
    EXPECT_EQ(actual.channels, 1u);
}

TEST_F(PalAudioSinkTest, OpenWithLowLatency) {
    AudioConfig config;
    config.buffer_ms = 20;
    Result result = sink_->open(config);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalAudioSinkTest, OpenWithHighLatency) {
    AudioConfig config;
    config.buffer_ms = 200;
    Result result = sink_->open(config);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalAudioSinkTest, OpenTwiceFails) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);
    EXPECT_EQ(sink_->open(config), Result::AlreadyOpen);
}

TEST_F(PalAudioSinkTest, CloseAfterOpen) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);
    sink_->close();
    EXPECT_FALSE(sink_->isOpen());
}

TEST_F(PalAudioSinkTest, CloseWithoutOpenIsSafe) {
    EXPECT_FALSE(sink_->isOpen());
    sink_->close();  // Should not crash
    EXPECT_FALSE(sink_->isOpen());
}

TEST_F(PalAudioSinkTest, ReopenAfterClose) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);
    sink_->close();
    EXPECT_EQ(sink_->open(config), Result::Success);
    EXPECT_TRUE(sink_->isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Push Model Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalAudioSinkTest, PushSamplesSucceeds) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    auto samples = generateSineWave(1024);
    Result result = sink_->pushSamples(samples.data(), 1024);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalAudioSinkTest, PushSamplesNullFails) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    Result result = sink_->pushSamples(nullptr, 1024);
    EXPECT_EQ(result, Result::InvalidParameter);
}

TEST_F(PalAudioSinkTest, PushSamplesZeroCountSucceeds) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    auto samples = generateSineWave(100);
    Result result = sink_->pushSamples(samples.data(), 0);
    EXPECT_EQ(result, Result::Success);
}

TEST_F(PalAudioSinkTest, PushSamplesUpdatesQueuedFrames) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    EXPECT_EQ(sink_->getQueuedFrames(), 0u);

    auto samples = generateSineWave(100);
    ASSERT_EQ(sink_->pushSamples(samples.data(), 100), Result::Success);
    EXPECT_EQ(sink_->getQueuedFrames(), 100u);
}

TEST_F(PalAudioSinkTest, PushSamplesBeforeOpenFails) {
    auto samples = generateSineWave(100);
    Result result = sink_->pushSamples(samples.data(), 100);
    EXPECT_EQ(result, Result::NotInitialized);
}

TEST_F(PalAudioSinkTest, PushSamplesOverflowDropsOldest) {
    AudioConfig config;
    config.buffer_ms = 10;  // Small buffer
    ASSERT_EQ(sink_->open(config), Result::Success);

    uint32_t capacity = sink_->getBufferCapacity();
    EXPECT_EQ(sink_->getDroppedFrames(), 0u);

    // Fill the buffer
    auto samples = generateSineWave(capacity);
    ASSERT_EQ(sink_->pushSamples(samples.data(), capacity), Result::Success);

    // Push more - should drop oldest, not return error
    auto more = generateSineWave(100);
    Result result = sink_->pushSamples(more.data(), 100);
    EXPECT_EQ(result, Result::Success);  // Backpressure policy: always succeeds
    EXPECT_GT(sink_->getDroppedFrames(), 0u);  // But tracks dropped frames
}

// ═══════════════════════════════════════════════════════════════════════════
// Buffer Query Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalAudioSinkTest, GetQueuedFramesInitiallyZero) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);
    EXPECT_EQ(sink_->getQueuedFrames(), 0u);
}

TEST_F(PalAudioSinkTest, GetBufferCapacityMatchesConfig) {
    AudioConfig config;
    config.sample_rate = 44100;
    config.buffer_ms = 50;
    ASSERT_EQ(sink_->open(config), Result::Success);

    uint32_t expected = (44100 * 50) / 1000;  // ~2205 frames
    uint32_t capacity = sink_->getBufferCapacity();
    EXPECT_EQ(capacity, expected);
}

TEST_F(PalAudioSinkTest, QueuedFramesNeverExceedsCapacity) {
    AudioConfig config;
    config.buffer_ms = 50;
    ASSERT_EQ(sink_->open(config), Result::Success);

    uint32_t capacity = sink_->getBufferCapacity();

    auto samples = generateSineWave(capacity + 100);
    sink_->pushSamples(samples.data(), capacity);
    EXPECT_LE(sink_->getQueuedFrames(), capacity);
}

TEST_F(PalAudioSinkTest, GetDroppedFramesInitiallyZero) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);
    EXPECT_EQ(sink_->getDroppedFrames(), 0u);
}

TEST_F(PalAudioSinkTest, DroppedFramesResetsOnClose) {
    AudioConfig config;
    config.buffer_ms = 10;  // Small buffer
    ASSERT_EQ(sink_->open(config), Result::Success);

    uint32_t capacity = sink_->getBufferCapacity();

    // Fill buffer and overflow to get drops
    auto samples = generateSineWave(capacity + 100);
    sink_->pushSamples(samples.data(), capacity + 100);
    EXPECT_GT(sink_->getDroppedFrames(), 0u);

    // Close and reopen
    sink_->close();
    ASSERT_EQ(sink_->open(config), Result::Success);
    EXPECT_EQ(sink_->getDroppedFrames(), 0u);  // Reset on close
}

// ═══════════════════════════════════════════════════════════════════════════
// Playback Control Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalAudioSinkTest, InitiallyNotPaused) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);
    EXPECT_FALSE(sink_->isPaused());
}

TEST_F(PalAudioSinkTest, PauseSetsState) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    EXPECT_EQ(sink_->pause(true), Result::Success);
    EXPECT_TRUE(sink_->isPaused());
}

TEST_F(PalAudioSinkTest, ResumeClearsState) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    sink_->pause(true);
    EXPECT_EQ(sink_->pause(false), Result::Success);
    EXPECT_FALSE(sink_->isPaused());
}

TEST_F(PalAudioSinkTest, PauseBeforeOpenFails) {
    EXPECT_EQ(sink_->pause(true), Result::NotInitialized);
}

TEST_F(PalAudioSinkTest, PushWhilePausedSucceeds) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    sink_->pause(true);
    auto samples = generateSineWave(100);
    EXPECT_EQ(sink_->pushSamples(samples.data(), 100), Result::Success);
}

// ═══════════════════════════════════════════════════════════════════════════
// Volume Control Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalAudioSinkTest, DefaultVolumeIsOne) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);
    EXPECT_FLOAT_EQ(sink_->getVolume(), 1.0f);
}

TEST_F(PalAudioSinkTest, SetVolumeInRange) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    EXPECT_EQ(sink_->setVolume(0.5f), Result::Success);
    EXPECT_FLOAT_EQ(sink_->getVolume(), 0.5f);
}

TEST_F(PalAudioSinkTest, SetVolumeZero) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    EXPECT_EQ(sink_->setVolume(0.0f), Result::Success);
    EXPECT_FLOAT_EQ(sink_->getVolume(), 0.0f);
}

TEST_F(PalAudioSinkTest, SetVolumeOne) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    sink_->setVolume(0.5f);
    EXPECT_EQ(sink_->setVolume(1.0f), Result::Success);
    EXPECT_FLOAT_EQ(sink_->getVolume(), 1.0f);
}

TEST_F(PalAudioSinkTest, SetVolumeClampsBelowZero) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    EXPECT_EQ(sink_->setVolume(-0.5f), Result::Success);
    EXPECT_FLOAT_EQ(sink_->getVolume(), 0.0f);
}

TEST_F(PalAudioSinkTest, SetVolumeClampsAboveOne) {
    AudioConfig config;
    ASSERT_EQ(sink_->open(config), Result::Success);

    EXPECT_EQ(sink_->setVolume(1.5f), Result::Success);
    EXPECT_FLOAT_EQ(sink_->getVolume(), 1.0f);
}

// ═══════════════════════════════════════════════════════════════════════════
// Configuration Query Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PalAudioSinkTest, GetConfigReturnsOpenedConfig) {
    AudioConfig config;
    config.sample_rate = 48000;
    config.channels = 1;
    config.buffer_ms = 100;
    ASSERT_EQ(sink_->open(config), Result::Success);

    AudioConfig actual = sink_->getConfig();
    EXPECT_EQ(actual.sample_rate, 48000u);
    EXPECT_EQ(actual.channels, 1u);
    EXPECT_EQ(actual.buffer_ms, 100u);
}

} // namespace
} // namespace pal
