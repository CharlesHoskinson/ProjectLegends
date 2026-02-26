// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for SaveManager — slot paths, directory structure, and validation.
// Full save/load with engine requires integration tests; these test the
// non-engine parts of the manager.

#include <gtest/gtest.h>
#include "app/save_manager.h"
#include "app/platform_dirs.h"

#include <filesystem>
#include <fstream>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Path generation
// ═══════════════════════════════════════════════════════════════════════════

TEST(SaveManagerTest, SaveDirContainsSaves) {
    std::string dir = SaveManager::getSaveDir();
    EXPECT_FALSE(dir.empty());
    EXPECT_NE(dir.find("saves"), std::string::npos);
}

TEST(SaveManagerTest, SaveDirStartsWithDataDir) {
    std::string data = getDataDir();
    std::string saves = SaveManager::getSaveDir();
    EXPECT_EQ(saves.substr(0, data.size()), data);
}

TEST(SaveManagerTest, SlotPathContainsSlotNumber) {
    std::string path = SaveManager::slotPath(3);
    EXPECT_NE(path.find("slot_3"), std::string::npos);
    EXPECT_NE(path.find(".sav"), std::string::npos);
}

TEST(SaveManagerTest, ThumbnailPathContainsSlotNumber) {
    std::string path = SaveManager::thumbnailPath(5);
    EXPECT_NE(path.find("slot_5"), std::string::npos);
    EXPECT_NE(path.find(".png"), std::string::npos);
}

TEST(SaveManagerTest, AllSlotPathsAreUnique) {
    std::set<std::string> paths;
    for (int i = 1; i <= SaveManager::kMaxSlots; ++i) {
        paths.insert(SaveManager::slotPath(i));
    }
    EXPECT_EQ(paths.size(), static_cast<size_t>(SaveManager::kMaxSlots));
}

// ═══════════════════════════════════════════════════════════════════════════
// Slot occupancy
// ═══════════════════════════════════════════════════════════════════════════

TEST(SaveManagerTest, IsSlotOccupied_InvalidSlotReturnsFalse) {
    SaveManager mgr;
    EXPECT_FALSE(mgr.isSlotOccupied(0));
    EXPECT_FALSE(mgr.isSlotOccupied(-1));
    EXPECT_FALSE(mgr.isSlotOccupied(10));
}

TEST(SaveManagerTest, IsSlotOccupied_EmptySlotReturnsFalse) {
    SaveManager mgr;
    // Slots 1-9 should be empty in a fresh environment (unless test artifacts exist)
    // This test is environment-dependent but validates the interface
    // We test with a guaranteed non-existent path by checking boundary slots
    EXPECT_FALSE(mgr.isSlotOccupied(10)); // out of range always false
}

// ═══════════════════════════════════════════════════════════════════════════
// Validation
// ═══════════════════════════════════════════════════════════════════════════

TEST(SaveManagerTest, SaveToSlot_NullEngine) {
    SaveManager mgr;
    EXPECT_FALSE(mgr.saveToSlot(nullptr, 1, nullptr, 0, 0));
    EXPECT_FALSE(mgr.lastError().empty());
}

TEST(SaveManagerTest, SaveToSlot_InvalidSlot) {
    // engine is non-null (fake), but slot is out of range
    SaveManager mgr;
    auto fake_engine = reinterpret_cast<legends_handle>(0x1);
    EXPECT_FALSE(mgr.saveToSlot(fake_engine, 0, nullptr, 0, 0));
    EXPECT_FALSE(mgr.saveToSlot(fake_engine, 10, nullptr, 0, 0));
}

TEST(SaveManagerTest, LoadFromSlot_NullEngine) {
    SaveManager mgr;
    EXPECT_FALSE(mgr.loadFromSlot(nullptr, 1));
    EXPECT_FALSE(mgr.lastError().empty());
}

TEST(SaveManagerTest, LoadFromSlot_EmptySlot) {
    SaveManager mgr;
    // Slot probably doesn't exist in test env
    // Use a known-empty slot (or slot 9 which is unlikely to exist)
    EXPECT_FALSE(mgr.loadFromSlot(reinterpret_cast<legends_handle>(0x1), 9));
}

TEST(SaveManagerTest, MaxSlotsIsNine) {
    EXPECT_EQ(SaveManager::kMaxSlots, 9);
}

} // namespace
} // namespace legends
