// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// AudioMixer — mix N int16_t stereo streams into one output buffer.

#pragma once

#include <cstdint>
#include <cstddef>
#include <span>

namespace legends {

class AudioMixer {
public:
    /// Mix two stereo int16_t streams into output.
    /// Uses int32_t intermediates with clamping to prevent overflow.
    /// @param out    Output buffer
    /// @param src_a  First source stream
    /// @param src_b  Second source stream
    /// @pre All spans must have equal size.
    static void mix(std::span<int16_t> out, std::span<const int16_t> src_a,
                    std::span<const int16_t> src_b);

    /// Mix source into existing output (additive).
    /// @param out    Output buffer (read + write)
    /// @param src    Source to add
    /// @pre out.size() >= src.size().
    static void mixAdditive(std::span<int16_t> out, std::span<const int16_t> src);

    /// Apply volume scaling to a buffer in-place.
    /// @param buf    Buffer to scale
    /// @param volume Volume multiplier (0.0 = silent, 1.0 = unity)
    static void applyVolume(std::span<int16_t> buf, float volume);

    /// Clamp an int32_t to int16_t range.
    static int16_t clampToInt16(int32_t value);

    /// Mix N sources into output.
    /// @param out     Output buffer
    /// @param sources Array of source spans
    static void mixN(std::span<int16_t> out, std::span<const std::span<const int16_t>> sources);
};

} // namespace legends
