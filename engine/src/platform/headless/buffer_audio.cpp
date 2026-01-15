/**
 * @file buffer_audio.cpp
 * @brief BufferAudio implementation for audio capture and analysis.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/platform/headless.h"
#include <algorithm>
#include <cmath>

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// BufferAudio Implementation
// ═══════════════════════════════════════════════════════════════════════════════

BufferAudio::BufferAudio(float buffer_seconds)
    : buffer_seconds_(buffer_seconds) {
}

bool BufferAudio::open(const AudioSpec& spec) {
    std::lock_guard<std::mutex> lock(mutex_);

    spec_ = spec;

    // Calculate buffer size: sample_rate * channels * buffer_seconds
    capacity_ = static_cast<size_t>(
        spec.sample_rate * spec.channels * buffer_seconds_);

    buffer_.resize(capacity_);
    write_pos_ = 0;
    read_pos_ = 0;
    queued_ = 0;
    is_open_ = true;
    paused_ = false;

    return true;
}

void BufferAudio::close() {
    std::lock_guard<std::mutex> lock(mutex_);

    is_open_ = false;
    buffer_.clear();
    capacity_ = 0;
    queued_ = 0;
}

bool BufferAudio::is_open() const {
    return is_open_;
}

AudioSpec BufferAudio::get_spec() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return spec_;
}

size_t BufferAudio::push_samples(std::span<const int16_t> samples) {
    if (!is_open_ || paused_) {
        return 0;
    }

    std::lock_guard<std::mutex> lock(mutex_);

    size_t to_push = samples.size();
    size_t available = capacity_ - queued_;

    // Limit to available space
    size_t actual = std::min(to_push, available);

    for (size_t i = 0; i < actual; ++i) {
        buffer_[write_pos_] = samples[i];
        write_pos_ = (write_pos_ + 1) % capacity_;
    }

    queued_ += actual;
    total_pushed_.fetch_add(actual, std::memory_order_relaxed);

    return actual;
}

size_t BufferAudio::push_samples_float(std::span<const float> samples) {
    if (!is_open_ || paused_) {
        return 0;
    }

    // Convert float to S16
    std::vector<int16_t> converted(samples.size());
    for (size_t i = 0; i < samples.size(); ++i) {
        float clamped = std::clamp(samples[i], -1.0f, 1.0f);
        converted[i] = static_cast<int16_t>(clamped * 32767.0f);
    }

    return push_samples(converted);
}

size_t BufferAudio::get_queued_samples() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return queued_;
}

size_t BufferAudio::get_buffer_capacity() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return capacity_;
}

void BufferAudio::pause(bool paused) {
    paused_ = paused;
}

bool BufferAudio::is_paused() const {
    return paused_;
}

void BufferAudio::clear() {
    std::lock_guard<std::mutex> lock(mutex_);

    write_pos_ = 0;
    read_pos_ = 0;
    queued_ = 0;
}

std::vector<int16_t> BufferAudio::pop_samples(size_t count) {
    std::lock_guard<std::mutex> lock(mutex_);

    size_t actual = std::min(count, queued_);
    std::vector<int16_t> result(actual);

    for (size_t i = 0; i < actual; ++i) {
        result[i] = buffer_[read_pos_];
        read_pos_ = (read_pos_ + 1) % capacity_;
    }

    queued_ -= actual;
    total_popped_.fetch_add(actual, std::memory_order_relaxed);

    return result;
}

std::vector<int16_t> BufferAudio::peek_samples(size_t count) const {
    std::lock_guard<std::mutex> lock(mutex_);

    size_t actual = std::min(count, queued_);
    std::vector<int16_t> result(actual);

    size_t pos = read_pos_;
    for (size_t i = 0; i < actual; ++i) {
        result[i] = buffer_[pos];
        pos = (pos + 1) % capacity_;
    }

    return result;
}

std::vector<int16_t> BufferAudio::get_all_samples() const {
    std::lock_guard<std::mutex> lock(mutex_);

    std::vector<int16_t> result(queued_);

    size_t pos = read_pos_;
    for (size_t i = 0; i < queued_; ++i) {
        result[i] = buffer_[pos];
        pos = (pos + 1) % capacity_;
    }

    return result;
}

float BufferAudio::calculate_rms() const {
    std::lock_guard<std::mutex> lock(mutex_);

    if (queued_ == 0) {
        return 0.0f;
    }

    double sum_squares = 0.0;
    size_t pos = read_pos_;

    for (size_t i = 0; i < queued_; ++i) {
        double sample = static_cast<double>(buffer_[pos]) / 32768.0;
        sum_squares += sample * sample;
        pos = (pos + 1) % capacity_;
    }

    return static_cast<float>(std::sqrt(sum_squares / queued_));
}

bool BufferAudio::is_silent(float threshold) const {
    return calculate_rms() < threshold;
}

} // namespace platform
} // namespace dosbox
