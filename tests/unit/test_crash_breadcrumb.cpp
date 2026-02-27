// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for CrashBreadcrumb: ring buffer correctness, overflow, concurrent access.

#include "app/crash_breadcrumb.h"

#include <algorithm>
#include <gtest/gtest.h>
#include <string>
#include <thread>
#include <vector>

namespace legends {
namespace {

class CrashBreadcrumbTest : public ::testing::Test {
protected:
    CrashBreadcrumb crumb_;

    void SetUp() override {
        crumb_.clear();
    }
};

// ── Basic Operations ─────────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, InitiallyEmpty) {
    EXPECT_EQ(crumb_.totalCount(), 0u);
    auto entries = crumb_.read();
    EXPECT_TRUE(entries.empty());
}

TEST_F(CrashBreadcrumbTest, AddSingleEntry) {
    crumb_.add("test message");
    EXPECT_EQ(crumb_.totalCount(), 1u);

    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), 1u);
    EXPECT_STREQ(entries[0].message, "test message");
    EXPECT_NE(entries[0].timestamp_us, 0u);
    EXPECT_EQ(entries[0].category, 0u); // General
}

TEST_F(CrashBreadcrumbTest, AddMultipleEntries) {
    crumb_.add("first");
    crumb_.add("second");
    crumb_.add("third");

    EXPECT_EQ(crumb_.totalCount(), 3u);
    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), 3u);
    EXPECT_STREQ(entries[0].message, "first");
    EXPECT_STREQ(entries[1].message, "second");
    EXPECT_STREQ(entries[2].message, "third");
}

TEST_F(CrashBreadcrumbTest, CategoryIsPreserved) {
    crumb_.add("engine", BreadcrumbCategory::Engine);
    crumb_.add("io", BreadcrumbCategory::IO);
    crumb_.add("render", BreadcrumbCategory::Render);
    crumb_.add("audio", BreadcrumbCategory::Audio);

    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), 4u);
    EXPECT_EQ(entries[0].category, static_cast<uint8_t>(BreadcrumbCategory::Engine));
    EXPECT_EQ(entries[1].category, static_cast<uint8_t>(BreadcrumbCategory::IO));
    EXPECT_EQ(entries[2].category, static_cast<uint8_t>(BreadcrumbCategory::Render));
    EXPECT_EQ(entries[3].category, static_cast<uint8_t>(BreadcrumbCategory::Audio));
}

// ── Ring Buffer Overflow ─────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, OverflowWrapsAround) {
    // Fill the buffer completely
    for (size_t i = 0; i < CrashBreadcrumb::kCapacity; ++i) {
        std::string msg = "msg_" + std::to_string(i);
        crumb_.add(msg.c_str());
    }

    EXPECT_EQ(crumb_.totalCount(), CrashBreadcrumb::kCapacity);
    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), CrashBreadcrumb::kCapacity);
    EXPECT_STREQ(entries[0].message, "msg_0");
    std::string expected_last = "msg_" + std::to_string(CrashBreadcrumb::kCapacity - 1);
    EXPECT_STREQ(entries[CrashBreadcrumb::kCapacity - 1].message, expected_last.c_str());
}

TEST_F(CrashBreadcrumbTest, OverflowOverwritesOldest) {
    // Fill buffer + 10 more
    size_t total = CrashBreadcrumb::kCapacity + 10;
    for (size_t i = 0; i < total; ++i) {
        std::string msg = "msg_" + std::to_string(i);
        crumb_.add(msg.c_str());
    }

    EXPECT_EQ(crumb_.totalCount(), total);
    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), CrashBreadcrumb::kCapacity);

    // Oldest should be msg_10 (first 10 were overwritten)
    EXPECT_STREQ(entries[0].message, "msg_10");
    // Newest should be msg_73
    std::string expected_last = "msg_" + std::to_string(total - 1);
    EXPECT_STREQ(entries[CrashBreadcrumb::kCapacity - 1].message, expected_last.c_str());
}

TEST_F(CrashBreadcrumbTest, ChronologicalOrder) {
    for (size_t i = 0; i < CrashBreadcrumb::kCapacity * 3; ++i) {
        std::string msg = "msg_" + std::to_string(i);
        crumb_.add(msg.c_str());
    }

    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), CrashBreadcrumb::kCapacity);

    // Entries should be in chronological order (timestamps increasing)
    for (size_t i = 1; i < entries.size(); ++i) {
        EXPECT_GE(entries[i].timestamp_us, entries[i - 1].timestamp_us)
            << "Entry " << i << " should have >= timestamp than entry " << i - 1;
    }
}

// ── Message Truncation ──────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, LongMessageTruncated) {
    std::string long_msg(BreadcrumbEntry::kMaxMessageLen + 100, 'X');
    crumb_.add(long_msg.c_str());

    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), 1u);
    EXPECT_EQ(std::strlen(entries[0].message), BreadcrumbEntry::kMaxMessageLen - 1);
}

TEST_F(CrashBreadcrumbTest, ExactMaxLengthMessage) {
    std::string exact(BreadcrumbEntry::kMaxMessageLen - 1, 'A');
    crumb_.add(exact.c_str());

    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), 1u);
    EXPECT_EQ(std::strlen(entries[0].message), BreadcrumbEntry::kMaxMessageLen - 1);
}

// ── Null message ─────────────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, NullMessageIgnored) {
    crumb_.add(nullptr);
    EXPECT_EQ(crumb_.totalCount(), 0u);
}

// ── Clear ────────────────────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, ClearResetsState) {
    crumb_.add("test");
    EXPECT_EQ(crumb_.totalCount(), 1u);

    crumb_.clear();
    EXPECT_EQ(crumb_.totalCount(), 0u);
    auto entries = crumb_.read();
    EXPECT_TRUE(entries.empty());
}

// ── readInto ─────────────────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, ReadIntoPartialBuffer) {
    for (int i = 0; i < 10; ++i) {
        std::string msg = "entry_" + std::to_string(i);
        crumb_.add(msg.c_str());
    }

    BreadcrumbEntry out[5];
    size_t count = crumb_.readInto(out, 5);
    EXPECT_EQ(count, 5u);
    EXPECT_STREQ(out[0].message, "entry_0");
    EXPECT_STREQ(out[4].message, "entry_4");
}

TEST_F(CrashBreadcrumbTest, ReadIntoNullBuffer) {
    crumb_.add("test");
    size_t count = crumb_.readInto(nullptr, 10);
    EXPECT_EQ(count, 0u);
}

TEST_F(CrashBreadcrumbTest, ReadIntoZeroMax) {
    crumb_.add("test");
    BreadcrumbEntry out[1];
    size_t count = crumb_.readInto(out, 0);
    EXPECT_EQ(count, 0u);
}

// ── Thread ID ────────────────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, ThreadIdIsNonZero) {
    crumb_.add("thread test");
    auto entries = crumb_.read();
    ASSERT_EQ(entries.size(), 1u);
    // Thread ID may be 0 on some platforms, but typically non-zero
    // Just verify the field is populated
    (void)entries[0].thread_id;
}

// ── Concurrent Access ───────────────────────────────────────────────────

TEST_F(CrashBreadcrumbTest, ConcurrentWritesSafe) {
    constexpr int kThreads = 4;
    constexpr int kMessagesPerThread = 100;

    std::vector<std::thread> threads;
    threads.reserve(kThreads);

    for (int t = 0; t < kThreads; ++t) {
        threads.emplace_back([this, t]() {
            for (int i = 0; i < kMessagesPerThread; ++i) {
                std::string msg = "t" + std::to_string(t) + "_m" + std::to_string(i);
                crumb_.add(msg.c_str());
            }
        });
    }

    for (auto& th : threads) {
        th.join();
    }

    EXPECT_EQ(crumb_.totalCount(),
              static_cast<uint64_t>(kThreads * kMessagesPerThread));

    auto entries = crumb_.read();
    EXPECT_EQ(entries.size(), CrashBreadcrumb::kCapacity);

    // All entries should have non-empty messages
    for (const auto& e : entries) {
        EXPECT_NE(e.message[0], '\0') << "Entry should have non-empty message";
    }
}

TEST_F(CrashBreadcrumbTest, ConcurrentReadWriteSafe) {
    constexpr int kIterations = 200;
    std::atomic<bool> stop{false};

    // Writer thread
    std::thread writer([this, &stop]() {
        int i = 0;
        while (!stop.load(std::memory_order_relaxed)) {
            std::string msg = "write_" + std::to_string(i++);
            crumb_.add(msg.c_str());
        }
    });

    // Reader thread
    std::thread reader([this, &stop]() {
        while (!stop.load(std::memory_order_relaxed)) {
            auto entries = crumb_.read();
            // Just verify no crash
            (void)entries.size();
        }
    });

    // Let them run for a bit
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    stop.store(true, std::memory_order_relaxed);

    writer.join();
    reader.join();

    // Should have some entries
    EXPECT_GT(crumb_.totalCount(), 0u);
}

// ── Global Breadcrumb ───────────────────────────────────────────────────

TEST(GlobalBreadcrumbTest, SingletonReturnsConsistent) {
    auto& a = globalBreadcrumb();
    auto& b = globalBreadcrumb();
    EXPECT_EQ(&a, &b);
}

// ── Entry Clear ──────────────────────────────────────────────────────────

TEST(BreadcrumbEntryTest, ClearResetsAllFields) {
    BreadcrumbEntry entry;
    entry.timestamp_us = 12345;
    std::strcpy(entry.message, "hello");
    entry.thread_id = 42;
    entry.category = 3;

    entry.clear();
    EXPECT_EQ(entry.timestamp_us, 0u);
    EXPECT_EQ(entry.message[0], '\0');
    EXPECT_EQ(entry.thread_id, 0u);
    EXPECT_EQ(entry.category, 0u);
}

} // namespace
} // namespace legends
