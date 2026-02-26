// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AudioMixer implementation — int16_t stereo stream mixing with clamping.

#include "app/audio_mixer.h"

#include <algorithm>
#include <cmath>
#include <cstring>

namespace legends {

void AudioMixer::mix(int16_t* out, const int16_t* src_a, const int16_t* src_b, size_t count) {
    if (count == 0) {
        return;
    }
    for (size_t i = 0; i < count; ++i) {
        int32_t sum = static_cast<int32_t>(src_a[i]) + static_cast<int32_t>(src_b[i]);
        out[i] = clampToInt16(sum);
    }
}

void AudioMixer::mixAdditive(int16_t* out, const int16_t* src, size_t count) {
    if (count == 0) {
        return;
    }
    for (size_t i = 0; i < count; ++i) {
        int32_t sum = static_cast<int32_t>(out[i]) + static_cast<int32_t>(src[i]);
        out[i] = clampToInt16(sum);
    }
}

void AudioMixer::applyVolume(int16_t* buf, size_t count, float volume) {
    if (count == 0) {
        return;
    }
    for (size_t i = 0; i < count; ++i) {
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

void AudioMixer::mixN(int16_t* out, const int16_t* const* sources, size_t n, size_t count) {
    if (count == 0) {
        return;
    }

    // Zero the output buffer first.
    std::memset(out, 0, count * sizeof(int16_t));

    // Additively mix each source.
    for (size_t s = 0; s < n; ++s) {
        mixAdditive(out, sources[s], count);
    }
}

} // namespace legends
