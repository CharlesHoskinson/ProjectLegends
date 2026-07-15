// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Mutex-serialized ring buffer. Establishes C++ happens-before for every
// field byte (audit F013: seqlock+memcpy is still a data race under TSan).

#include "app/crash_breadcrumb.h"

#include <algorithm>
#include <chrono>
#include <cstring>

#if defined(_WIN32)
#  ifndef WIN32_LEAN_AND_MEAN
#    define WIN32_LEAN_AND_MEAN
#  endif
#  ifndef NOMINMAX
#    define NOMINMAX
#  endif
#  include <windows.h>
#else
#  include <pthread.h>
#endif

namespace legends {

CrashBreadcrumb::CrashBreadcrumb() {
    clear();
}

CrashBreadcrumb::~CrashBreadcrumb() = default;

void CrashBreadcrumb::add(const char* message, BreadcrumbCategory category) {
    if (!message) return;

    std::lock_guard<std::mutex> lock(mu_);

    uint64_t idx = write_index_++;
    size_t slot = static_cast<size_t>(idx % kCapacity);

    auto& entry = entries_[slot];
    entry.timestamp_us = currentTimestampUs();
    entry.thread_id = currentThreadId();
    entry.category = static_cast<uint8_t>(category);

    size_t len = std::strlen(message);
    size_t copy_len = std::min(len, BreadcrumbEntry::kMaxMessageLen - 1);
    std::memcpy(entry.message, message, copy_len);
    entry.message[copy_len] = '\0';
}

std::vector<BreadcrumbEntry> CrashBreadcrumb::read() const {
    std::vector<BreadcrumbEntry> result;
    result.resize(kCapacity);
    size_t count = readInto(result.data(), kCapacity);
    result.resize(count);
    return result;
}

size_t CrashBreadcrumb::readInto(BreadcrumbEntry* out, size_t max_entries) const {
    if (!out || max_entries == 0) return 0;

    std::lock_guard<std::mutex> lock(mu_);

    if (write_index_ == 0) return 0;

    uint64_t total = write_index_;
    uint64_t count = std::min(total, static_cast<uint64_t>(kCapacity));
    uint64_t start = (total > kCapacity) ? (total - kCapacity) : 0;
    size_t out_count = static_cast<size_t>(std::min(count, static_cast<uint64_t>(max_entries)));

    for (size_t i = 0; i < out_count; ++i) {
        size_t slot = static_cast<size_t>((start + i) % kCapacity);
        out[i] = entries_[slot];
    }

    return out_count;
}

void CrashBreadcrumb::clear() {
    std::lock_guard<std::mutex> lock(mu_);
    write_index_ = 0;
    for (auto& entry : entries_) {
        entry.clear();
    }
}

uint64_t CrashBreadcrumb::totalCount() const {
    std::lock_guard<std::mutex> lock(mu_);
    return write_index_;
}

uint32_t CrashBreadcrumb::currentThreadId() {
#if defined(_WIN32)
    return static_cast<uint32_t>(GetCurrentThreadId());
#else
    return static_cast<uint32_t>(
        reinterpret_cast<uintptr_t>(reinterpret_cast<void*>(pthread_self())) & 0xFFFFFFFFu);
#endif
}

uint64_t CrashBreadcrumb::currentTimestampUs() {
    auto now = std::chrono::steady_clock::now();
    return static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::microseconds>(
            now.time_since_epoch()).count());
}

CrashBreadcrumb& globalBreadcrumb() {
    static CrashBreadcrumb instance;
    return instance;
}

} // namespace legends
