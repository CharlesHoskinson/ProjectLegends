// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Integration tests for volume control logic using PAL Headless audio sink.

#include <gtest/gtest.h>
#include <pal/platform.h>
#include <pal/audio_sink.h>

#include <algorithm>
#include <cmath>
#include <memory>

namespace {

class VolumeControlTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        ASSERT_EQ(pal::Platform::initialize(pal::Backend::Headless), pal::Result::Success);
        sink_ = pal::Platform::createAudioSink();
        ASSERT_NE(sink_, nullptr);
        pal::AudioConfig cfg;
        cfg.sample_rate = 44100;
        cfg.channels    = 2;
        cfg.buffer_ms   = 50;
        ASSERT_EQ(sink_->open(cfg), pal::Result::Success);

        // Initialize state matching Application defaults
        volume_ = 1.0f;
        pre_mute_vol_ = 1.0f;
        muted_ = false;
    }

    void TearDown() override {
        sink_.reset();
        pal::Platform::shutdown();
    }

    // Replicates Application::processEvents volume logic
    void volumeUp() {
        volume_ = std::min(1.0f, volume_ + 0.1f);
        muted_ = false;
        sink_->setVolume(volume_);
    }

    void volumeDown() {
        volume_ = std::max(0.0f, volume_ - 0.1f);
        muted_ = false;
        sink_->setVolume(volume_);
    }

    void toggleMute() {
        if (muted_) {
            muted_ = false;
            volume_ = pre_mute_vol_;
        } else {
            muted_ = true;
            pre_mute_vol_ = volume_;
            volume_ = 0.0f;
        }
        sink_->setVolume(volume_);
    }

    std::unique_ptr<pal::IAudioSink> sink_;
    float volume_       = 1.0f;
    float pre_mute_vol_ = 1.0f;
    bool  muted_        = false;
};

// ═══════════════════════════════════════════════════════════════════════════
// Increment / Decrement
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(VolumeControlTest, VolumeUpClampsAtOne) {
    volume_ = 1.0f;
    volumeUp();
    EXPECT_FLOAT_EQ(volume_, 1.0f);
}

TEST_F(VolumeControlTest, VolumeDownClampsAtZero) {
    volume_ = 0.0f;
    volumeDown();
    EXPECT_FLOAT_EQ(volume_, 0.0f);
}

TEST_F(VolumeControlTest, VolumeUpFromZero) {
    volume_ = 0.0f;
    sink_->setVolume(0.0f);
    volumeUp();
    EXPECT_NEAR(volume_, 0.1f, 0.001f);
}

TEST_F(VolumeControlTest, VolumeDownFromOne) {
    volumeDown();
    EXPECT_NEAR(volume_, 0.9f, 0.001f);
}

TEST_F(VolumeControlTest, TenDownStepsReachZero) {
    for (int i = 0; i < 10; ++i) volumeDown();
    EXPECT_NEAR(volume_, 0.0f, 0.001f);
}

TEST_F(VolumeControlTest, TenUpStepsReachOne) {
    volume_ = 0.0f;
    sink_->setVolume(0.0f);
    for (int i = 0; i < 10; ++i) volumeUp();
    EXPECT_NEAR(volume_, 1.0f, 0.001f);
}

TEST_F(VolumeControlTest, SinkVolumeMatchesState) {
    volume_ = 0.5f;
    sink_->setVolume(volume_);
    volumeUp();
    EXPECT_NEAR(sink_->getVolume(), volume_, 0.001f);
}

// ═══════════════════════════════════════════════════════════════════════════
// Mute
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(VolumeControlTest, MuteSetsZero) {
    toggleMute();
    EXPECT_TRUE(muted_);
    EXPECT_FLOAT_EQ(volume_, 0.0f);
}

TEST_F(VolumeControlTest, UnmuteRestores) {
    volume_ = 0.7f;
    sink_->setVolume(volume_);
    toggleMute(); // mute
    EXPECT_FLOAT_EQ(volume_, 0.0f);
    toggleMute(); // unmute
    EXPECT_NEAR(volume_, 0.7f, 0.001f);
}

TEST_F(VolumeControlTest, MuteRoundtrip) {
    float original = volume_;
    toggleMute();
    toggleMute();
    EXPECT_NEAR(volume_, original, 0.001f);
    EXPECT_FALSE(muted_);
}

TEST_F(VolumeControlTest, VolumeUpCancelsMute) {
    toggleMute();
    EXPECT_TRUE(muted_);
    volumeUp();
    EXPECT_FALSE(muted_);
    EXPECT_GT(volume_, 0.0f);
}

TEST_F(VolumeControlTest, VolumeDownCancelsMute) {
    volume_ = 0.5f;
    sink_->setVolume(volume_);
    toggleMute();
    EXPECT_TRUE(muted_);
    volumeDown();
    EXPECT_FALSE(muted_);
    // After mute set volume to 0, then volumeDown clamps at 0
    EXPECT_FLOAT_EQ(volume_, 0.0f);
}

} // namespace
