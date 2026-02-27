// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Lock-free crash breadcrumb ring buffer implementation.

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
#  include <unistd.h>
#endif

namespace legends {

CrashBreadcrumb::CrashBreadcrumb() {
    clear();
}

CrashBreadcrumb::~CrashBreadcrumb() = default;

void CrashBreadcrumb::add(const char* message, BreadcrumbCategory category) {
    if (!message) return;

    uint64_t idx = write_index_.fetch_add(1, std::memory_order_relaxed);
    size_t slot = static_cast<size_t>(idx % kCapacity);

    auto& entry = entries_[slot];
    entry.timestamp_us = currentTimestampUs();
    entry.thread_id = currentThreadId();
    entry.category = static_cast<uint8_t>(category);

    // Safe string copy
    size_t len = std::strlen(message);
    size_t copy_len = std::min(len, BreadcrumbEntry::kMaxMessageLen - 1);
    std::memcpy(entry.message, message, copy_len);
    entry.message[copy_len] = '\0';

    // Ensure all field writes are visible before a concurrent readInto()
    std::atomic_thread_fence(std::memory_order_release);
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

    uint64_t total = write_index_.load(std::memory_order_acquire);
    if (total == 0) return 0;

    // Determine how many valid entries exist
    uint64_t count = std::min(total, static_cast<uint64_t>(kCapacity));
    uint64_t start = (total > kCapacity) ? (total - kCapacity) : 0;

    size_t out_count = static_cast<size_t>(std::min(count, static_cast<uint64_t>(max_entries)));

    // Acquire fence pairs with the release fence in add() to ensure
    // we see fully-written entries (not partially-constructed ones).
    std::atomic_thread_fence(std::memory_order_acquire);

    // Copy in chronological order (oldest first)
    for (size_t i = 0; i < out_count; ++i) {
        size_t slot = static_cast<size_t>((start + i) % kCapacity);
        std::memcpy(&out[i], &entries_[slot], sizeof(BreadcrumbEntry));
    }

    return out_count;
}

void CrashBreadcrumb::clear() {
    write_index_.store(0, std::memory_order_release);
    for (auto& entry : entries_) {
        entry.clear();
    }
}

uint32_t CrashBreadcrumb::currentThreadId() {
#if defined(_WIN32)
    return static_cast<uint32_t>(GetCurrentThreadId());
#else
    // Use a hash of pthread_self for a compact ID
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
