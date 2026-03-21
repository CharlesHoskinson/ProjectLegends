// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AudioMixer implementation — int16_t stereo stream mixing with clamping.

#include "app/audio_mixer.h"

#include <algorithm>
#include <cmath>
#include <cstring>

namespace legends {

void AudioMixer::mix(std::span<int16_t> out, std::span<const int16_t> src_a,
                     std::span<const int16_t> src_b) {
    size_t count = out.size();
    if (count == 0) {
        return;
    }
    for (size_t i = 0; i < count; ++i) {
        int32_t sum = static_cast<int32_t>(src_a[i]) + static_cast<int32_t>(src_b[i]);
        out[i] = clampToInt16(sum);
    }
}

void AudioMixer::mixAdditive(std::span<int16_t> out, std::span<const int16_t> src) {
    size_t count = std::min(out.size(), src.size());
    if (count == 0) {
        return;
    }
    for (size_t i = 0; i < count; ++i) {
        int32_t sum = static_cast<int32_t>(out[i]) + static_cast<int32_t>(src[i]);
        out[i] = clampToInt16(sum);
    }
}

void AudioMixer::applyVolume(std::span<int16_t> buf, float volume) {
    if (buf.empty()) {
        return;
    }
    for (size_t i = 0; i < buf.size(); ++i) {
        int32_t scaled = static_cast<int32_t>(std::lroundf(
            static_cast<float>(buf[i]) * volume));
        buf[i] = clampToInt16(scaled);
    }
}

int16_t AudioMixer::clampToInt16(int32_t value) {
    if (value > INT16_MAX) {
        return INT16_MAX;
    }
    if (value < INT16_MIN) {
        return INT16_MIN;
    }
    return static_cast<int16_t>(value);
}

void AudioMixer::mixN(std::span<int16_t> out,
                       std::span<const std::span<const int16_t>> sources) {
    if (out.empty()) {
        return;
    }

    // Zero the output buffer first.
    std::memset(out.data(), 0, out.size() * sizeof(int16_t));

    // Additively mix each source.
    for (const auto& src : sources) {
        mixAdditive(out, src);
    }
}

} // namespace legends
