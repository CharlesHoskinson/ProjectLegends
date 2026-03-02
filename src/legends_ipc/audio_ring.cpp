// SPDX-License-Identifier: MIT
#include <legends_ipc/audio_ring.h>
#include <algorithm>
#include <cstring>

namespace legends_ipc {

void AudioRingBuffer::map_pointers() {
    auto d = region_.data();
    header_   = reinterpret_cast<AudioRingHeader*>(d.data());
    samples_  = reinterpret_cast<int16_t*>(d.data() + sizeof(AudioRingHeader));
    capacity_ = header_->capacity_frames;
    channels_ = header_->channels;
}

std::expected<AudioRingBuffer, IpcError>
AudioRingBuffer::create(const std::string& name, uint32_t capacity_frames,
                         uint32_t channels, uint32_t sample_rate) {
    if (capacity_frames == 0 || channels == 0)
        return std::unexpected(IpcError::InvalidArgument);

    size_t total = required_size(capacity_frames, channels);
    auto region = SharedMemoryRegion::create(name + "_audio", total);
    if (!region.has_value())
        return std::unexpected(region.error());

    AudioRingBuffer ring;
    ring.region_ = std::move(*region);

    // Set header fields BEFORE map_pointers() so cached members get correct values
    auto d = ring.region_.data();
    auto* hdr = reinterpret_cast<AudioRingHeader*>(d.data());
    hdr->capacity_frames = capacity_frames;
    hdr->channels        = channels;
    hdr->sample_rate     = sample_rate;
    hdr->write_index.store(0, std::memory_order_relaxed);
    hdr->read_index.store(0, std::memory_order_relaxed);

    ring.map_pointers();

    return ring;
}

std::expected<AudioRingBuffer, IpcError>
AudioRingBuffer::open(const std::string& name, uint32_t capacity_frames,
                       uint32_t channels, uint32_t /*sample_rate*/) {
    if (capacity_frames == 0 || channels == 0)
        return std::unexpected(IpcError::InvalidArgument);

    size_t total = required_size(capacity_frames, channels);
    auto region = SharedMemoryRegion::open(name + "_audio", total);
    if (!region.has_value())
        return std::unexpected(region.error());

    AudioRingBuffer ring;
    ring.region_ = std::move(*region);
    ring.map_pointers();
    return ring;
}

uint32_t AudioRingBuffer::push(std::span<const int16_t> samples) {
    uint32_t frames_to_write = static_cast<uint32_t>(samples.size() / channels_);
    if (frames_to_write == 0) return 0;

    uint32_t wi = header_->write_index.load(std::memory_order_relaxed);
    uint32_t samples_per_frame = channels_;

    for (uint32_t f = 0; f < frames_to_write; ++f) {
        uint32_t pos = (wi % capacity_) * samples_per_frame;
        for (uint32_t c = 0; c < samples_per_frame; ++c)
            samples_[pos + c] = samples[f * samples_per_frame + c];
        ++wi;
    }

    header_->write_index.store(wi, std::memory_order_release);
    return frames_to_write;
}

uint32_t AudioRingBuffer::pop(std::span<int16_t> buffer) {
    uint32_t ri = header_->read_index.load(std::memory_order_relaxed);
    uint32_t wi = header_->write_index.load(std::memory_order_acquire);

    uint32_t avail = wi - ri;
    if (avail > capacity_) {
        // Writer has lapped reader; skip to latest data minus capacity
        ri = wi - capacity_;
        avail = capacity_;
    }

    uint32_t max_frames = static_cast<uint32_t>(buffer.size() / channels_);
    uint32_t to_read = std::min(avail, max_frames);
    uint32_t samples_per_frame = channels_;

    for (uint32_t f = 0; f < to_read; ++f) {
        uint32_t pos = (ri % capacity_) * samples_per_frame;
        for (uint32_t c = 0; c < samples_per_frame; ++c)
            buffer[f * samples_per_frame + c] = samples_[pos + c];
        ++ri;
    }

    header_->read_index.store(ri, std::memory_order_release);
    return to_read;
}

uint32_t AudioRingBuffer::available() const {
    uint32_t ri = header_->read_index.load(std::memory_order_relaxed);
    uint32_t wi = header_->write_index.load(std::memory_order_acquire);
    uint32_t avail = wi - ri;
    return std::min(avail, capacity_);
}

uint32_t AudioRingBuffer::capacity_frames() const { return capacity_; }
uint32_t AudioRingBuffer::channels() const { return channels_; }
uint32_t AudioRingBuffer::sample_rate() const { return header_->sample_rate; }

} // namespace legends_ipc
