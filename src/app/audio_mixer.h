// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AudioMixer — mix N int16_t stereo streams into one output buffer.

#pragma once

#include <cstdint>
#include <cstddef>

namespace legends {

class AudioMixer {
public:
    /// Mix two stereo int16_t streams into output.
    /// Uses int32_t intermediates with clamping to prevent overflow.
    /// @param out    Output buffer (must have capacity >= count)
    /// @param src_a  First source stream
    /// @param src_b  Second source stream
    /// @param count  Number of int16_t samples (not frames)
    /// @pre out, src_a, and src_b must be non-null.
    static void mix(int16_t* out, const int16_t* src_a, const int16_t* src_b, size_t count);

    /// Mix source into existing output (additive).
    /// @param out    Output buffer (read + write)
    /// @param src    Source to add
    /// @param count  Number of int16_t samples
    /// @pre out and src must be non-null.
    static void mixAdditive(int16_t* out, const int16_t* src, size_t count);

    /// Apply volume scaling to a buffer in-place.
    /// @param buf    Buffer to scale
    /// @param count  Number of int16_t samples
    /// @param volume Volume multiplier (0.0 = silent, 1.0 = unity)
    /// @pre buf must be non-null.
    static void applyVolume(int16_t* buf, size_t count, float volume);

    /// Clamp an int32_t to int16_t range.
    static int16_t clampToInt16(int32_t value);

    /// Mix N sources into output.
    /// @param out     Output buffer
    /// @param sources Array of source buffer pointers
    /// @param n       Number of sources
    /// @param count   Number of int16_t samples per source
    static void mixN(int16_t* out, const int16_t* const* sources, size_t n, size_t count);
};

} // namespace legends
