// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for AudioMixer.

#include <gtest/gtest.h>
#include "app/audio_mixer.h"

#include <array>
#include <cstdint>
#include <cstring>
#include <vector>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// clampToInt16
// ═══════════════════════════════════════════════════════════════════════════

TEST(AudioMixerTest, ClampToInt16_Zero) {
    EXPECT_EQ(AudioMixer::clampToInt16(0), 0);
}

TEST(AudioMixerTest, ClampToInt16_InRange_Positive) {
    EXPECT_EQ(AudioMixer::clampToInt16(1000), 1000);
}

TEST(AudioMixerTest, ClampToInt16_InRange_Negative) {
    EXPECT_EQ(AudioMixer::clampToInt16(-1000), -1000);
}

TEST(AudioMixerTest, ClampToInt16_AtMax) {
    EXPECT_EQ(AudioMixer::clampToInt16(32767), 32767);
}

TEST(AudioMixerTest, ClampToInt16_AtMin) {
    EXPECT_EQ(AudioMixer::clampToInt16(-32768), -32768);
}

TEST(AudioMixerTest, ClampToInt16_AboveMax) {
    EXPECT_EQ(AudioMixer::clampToInt16(32768), 32767);
}

TEST(AudioMixerTest, ClampToInt16_BelowMin) {
    EXPECT_EQ(AudioMixer::clampToInt16(-32769), -32768);
}

TEST(AudioMixerTest, ClampToInt16_FarAboveMax) {
    EXPECT_EQ(AudioMixer::clampToInt16(100000), 32767);
}

TEST(AudioMixerTest, ClampToInt16_FarBelowMin) {
    EXPECT_EQ(AudioMixer::clampToInt16(-100000), -32768);
}

// ═══════════════════════════════════════════════════════════════════════════
// mix (two sources)
// ═══════════════════════════════════════════════════════════════════════════

TEST(AudioMixerTest, MixTwoSilenceBuffers) {
    std::array<int16_t, 8> a = {};
    std::array<int16_t, 8> b = {};
    std::array<int16_t, 8> out = {};

    AudioMixer::mix(out, a, b);

    for (auto sample : out) {
        EXPECT_EQ(sample, 0);
    }
}

TEST(AudioMixerTest, MixSilenceAndSignal) {
    std::array<int16_t, 4> silence = {0, 0, 0, 0};
    std::array<int16_t, 4> signal = {100, -200, 300, -400};
    std::array<int16_t, 4> out = {};

    AudioMixer::mix(out, silence, signal);

    for (size_t i = 0; i < 4; ++i) {
        EXPECT_EQ(out[i], signal[i]);
    }
}

TEST(AudioMixerTest, MixSignalPlusSignal) {
    std::array<int16_t, 4> a = {100, 200, 300, 400};
    std::array<int16_t, 4> b = {100, 200, 300, 400};
    std::array<int16_t, 4> out = {};

    AudioMixer::mix(out, a, b);

    EXPECT_EQ(out[0], 200);
    EXPECT_EQ(out[1], 400);
    EXPECT_EQ(out[2], 600);
    EXPECT_EQ(out[3], 800);
}

TEST(AudioMixerTest, MixPositiveOverflowClampsToMax) {
    std::array<int16_t, 1> a = {30000};
    std::array<int16_t, 1> b = {30000};
    std::array<int16_t, 1> out = {};

    AudioMixer::mix(out, a, b);

    EXPECT_EQ(out[0], INT16_MAX);
}

TEST(AudioMixerTest, MixNegativeOverflowClampsToMin) {
    std::array<int16_t, 1> a = {-30000};
    std::array<int16_t, 1> b = {-30000};
    std::array<int16_t, 1> out = {};

    AudioMixer::mix(out, a, b);

    EXPECT_EQ(out[0], INT16_MIN);
}

TEST(AudioMixerTest, MixSingleSample) {
    int16_t a = 500;
    int16_t b = 700;
    int16_t out = 0;

    AudioMixer::mix(std::span<int16_t>{&out, 1},
                    std::span<const int16_t>{&a, 1},
                    std::span<const int16_t>{&b, 1});

    EXPECT_EQ(out, 1200);
}

TEST(AudioMixerTest, MixZeroCount_NoOp) {
    int16_t a = 123;
    int16_t b = 456;
    int16_t out = 999;

    AudioMixer::mix(std::span<int16_t>{}, std::span<const int16_t>{},
                    std::span<const int16_t>{});

    // Output should remain unchanged.
    EXPECT_EQ(out, 999);
}

TEST(AudioMixerTest, MixLargeBuffer) {
    constexpr size_t kSize = 1024;
    std::vector<int16_t> a(kSize, 100);
    std::vector<int16_t> b(kSize, 200);
    std::vector<int16_t> out(kSize, 0);

    AudioMixer::mix(out, a, b);

    for (size_t i = 0; i < kSize; ++i) {
        EXPECT_EQ(out[i], 300);
    }
}

TEST(AudioMixerTest, MixAlternatingPositiveNegative) {
    std::array<int16_t, 4> a = {1000, -1000, 1000, -1000};
    std::array<int16_t, 4> b = {-1000, 1000, -1000, 1000};
    std::array<int16_t, 4> out = {};

    AudioMixer::mix(out, a, b);

    for (auto sample : out) {
        EXPECT_EQ(sample, 0);
    }
}

TEST(AudioMixerTest, MixStereoInterleavingPreserved) {
    // Stereo: L R L R
    std::array<int16_t, 4> a = {100, 200, 300, 400};  // L=100,300; R=200,400
    std::array<int16_t, 4> b = {10, 20, 30, 40};
    std::array<int16_t, 4> out = {};

    AudioMixer::mix(out, a, b);

    EXPECT_EQ(out[0], 110);  // L
    EXPECT_EQ(out[1], 220);  // R
    EXPECT_EQ(out[2], 330);  // L
    EXPECT_EQ(out[3], 440);  // R
}

// ═══════════════════════════════════════════════════════════════════════════
// mixAdditive
// ═══════════════════════════════════════════════════════════════════════════

TEST(AudioMixerTest, MixAdditiveAddsToExisting) {
    std::array<int16_t, 4> out = {100, 200, 300, 400};
    std::array<int16_t, 4> src = {10, 20, 30, 40};

    AudioMixer::mixAdditive(out, src);

    EXPECT_EQ(out[0], 110);
    EXPECT_EQ(out[1], 220);
    EXPECT_EQ(out[2], 330);
    EXPECT_EQ(out[3], 440);
}

TEST(AudioMixerTest, MixAdditiveClamps) {
    std::array<int16_t, 1> out = {30000};
    std::array<int16_t, 1> src = {30000};

    AudioMixer::mixAdditive(out, src);

    EXPECT_EQ(out[0], INT16_MAX);
}

// ═══════════════════════════════════════════════════════════════════════════
// applyVolume
// ═══════════════════════════════════════════════════════════════════════════

TEST(AudioMixerTest, ApplyVolume_Unity_NoChange) {
    std::array<int16_t, 4> buf = {100, -200, 300, -400};
    auto original = buf;

    AudioMixer::applyVolume(buf, 1.0f);

    for (size_t i = 0; i < 4; ++i) {
        EXPECT_EQ(buf[i], original[i]);
    }
}

TEST(AudioMixerTest, ApplyVolume_Zero_Silence) {
    std::array<int16_t, 4> buf = {100, -200, 300, -400};

    AudioMixer::applyVolume(buf, 0.0f);

    for (auto sample : buf) {
        EXPECT_EQ(sample, 0);
    }
}

TEST(AudioMixerTest, ApplyVolume_Half) {
    std::array<int16_t, 4> buf = {100, -200, 300, -400};

    AudioMixer::applyVolume(buf, 0.5f);

    EXPECT_EQ(buf[0], 50);
    EXPECT_EQ(buf[1], -100);
    EXPECT_EQ(buf[2], 150);
    EXPECT_EQ(buf[3], -200);
}

TEST(AudioMixerTest, ApplyVolume_Double_Clamps) {
    std::array<int16_t, 2> buf = {20000, -20000};

    AudioMixer::applyVolume(buf, 2.0f);

    EXPECT_EQ(buf[0], INT16_MAX);
    EXPECT_EQ(buf[1], INT16_MIN);
}

TEST(AudioMixerTest, ApplyVolume_Negative_Inverts) {
    std::array<int16_t, 2> buf = {100, -200};

    AudioMixer::applyVolume(buf, -1.0f);

    EXPECT_EQ(buf[0], -100);
    EXPECT_EQ(buf[1], 200);
}

TEST(AudioMixerTest, ApplyVolume_PreservesSign) {
    std::array<int16_t, 2> buf = {500, -500};

    AudioMixer::applyVolume(buf, 0.5f);

    EXPECT_GT(buf[0], 0);
    EXPECT_LT(buf[1], 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// mixN
// ═══════════════════════════════════════════════════════════════════════════

TEST(AudioMixerTest, MixN_ZeroSources_Silence) {
    std::array<int16_t, 4> out = {999, 999, 999, 999};

    AudioMixer::mixN(out, std::span<const std::span<const int16_t>>{});

    for (auto sample : out) {
        EXPECT_EQ(sample, 0);
    }
}

TEST(AudioMixerTest, MixN_OneSource_Copy) {
    std::array<int16_t, 4> src = {100, 200, 300, 400};
    std::span<const int16_t> sources[] = {src};
    std::array<int16_t, 4> out = {};

    AudioMixer::mixN(out, sources);

    for (size_t i = 0; i < 4; ++i) {
        EXPECT_EQ(out[i], src[i]);
    }
}

TEST(AudioMixerTest, MixN_ThreeSources) {
    std::array<int16_t, 4> a = {100, 100, 100, 100};
    std::array<int16_t, 4> b = {200, 200, 200, 200};
    std::array<int16_t, 4> c = {300, 300, 300, 300};
    std::span<const int16_t> sources[] = {
        std::span<const int16_t>{a},
        std::span<const int16_t>{b},
        std::span<const int16_t>{c}
    };
    std::array<int16_t, 4> out = {};

    AudioMixer::mixN(out, sources);

    for (auto sample : out) {
        EXPECT_EQ(sample, 600);
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Edge cases
// ═══════════════════════════════════════════════════════════════════════════

TEST(AudioMixerTest, MixWithZeroCount_NullPtrs) {
    // Should not crash when spans are empty.
    AudioMixer::mix(std::span<int16_t>{}, std::span<const int16_t>{},
                    std::span<const int16_t>{});
    AudioMixer::mixAdditive(std::span<int16_t>{}, std::span<const int16_t>{});
    AudioMixer::applyVolume(std::span<int16_t>{}, 1.0f);
    AudioMixer::mixN(std::span<int16_t>{}, std::span<const std::span<const int16_t>>{});
}

} // namespace
} // namespace legends
