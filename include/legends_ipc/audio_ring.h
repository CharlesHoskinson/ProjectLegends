// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_AUDIO_RING_H
#define LEGENDS_IPC_AUDIO_RING_H

#include <atomic>
#include <cstdint>
#include <expected>
#include <span>
#include <string_view>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/shared_memory.h>

namespace legends_ipc {

// Shared memory layout for audio ring header (32 bytes).
struct AudioRingHeader {
    uint32_t capacity_frames;             // 0
    uint32_t channels;                    // 4
    uint32_t sample_rate;                 // 8
    uint32_t padding;                     // 12
    std::atomic<uint32_t> write_index;    // 16
    std::atomic<uint32_t> read_index;     // 20
    uint8_t  padding2[8];                 // 24
};                                        // 32 total

static_assert(sizeof(AudioRingHeader) == 32);
static_assert(std::atomic<uint32_t>::is_always_lock_free,
              "SHM requires lock-free uint32_t atomics for ring buffer indices");

// Lock-free SPSC ring buffer for audio over shared memory.
// Producer (engine): push(samples) -> frames written
// Consumer (proxy):  pop(buffer)   -> frames read
class AudioRingBuffer {
public:
    [[nodiscard]] static std::expected<AudioRingBuffer, IpcError>
    create(std::string_view name, uint32_t capacity_frames,
           uint32_t channels = 2, uint32_t sample_rate = 44100);

    [[nodiscard]] static std::expected<AudioRingBuffer, IpcError>
    open(std::string_view name, uint32_t capacity_frames,
         uint32_t channels = 2, uint32_t sample_rate = 44100);

    // Push samples (interleaved). Returns number of frames actually written.
    // Drops oldest if buffer is full (overwrites).
    [[nodiscard]] uint32_t push(std::span<const int16_t> samples);

    // Pop samples into buffer. Returns number of frames actually read.
    [[nodiscard]] uint32_t pop(std::span<int16_t> buffer);

    // How many frames are available to read.
    [[nodiscard]] uint32_t available() const;

    [[nodiscard]] uint32_t capacity_frames() const;
    [[nodiscard]] uint32_t channels() const;
    [[nodiscard]] uint32_t sample_rate() const;

    [[nodiscard]] static size_t required_size(uint32_t capacity_frames, uint32_t channels) {
        return sizeof(AudioRingHeader) +
               static_cast<size_t>(capacity_frames) * channels * sizeof(int16_t);
    }

private:
    AudioRingBuffer() = default;
    SharedMemoryRegion region_;
    AudioRingHeader* header_ = nullptr;
    int16_t* samples_        = nullptr;
    uint32_t capacity_       = 0;
    uint32_t channels_       = 0;

    void map_pointers();
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_AUDIO_RING_H
