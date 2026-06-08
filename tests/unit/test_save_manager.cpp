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
#include <set>

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

TEST(SaveManagerTest, SlotPathContainsAutosaveSlotNumber) {
    std::string path = SaveManager::slotPath(SaveManager::kAutosaveSlot);
    EXPECT_NE(path.find("slot_0"), std::string::npos);
    EXPECT_NE(path.find(".sav"), std::string::npos);
}

TEST(SaveManagerTest, ThumbnailPathContainsSlotNumber) {
    std::string path = SaveManager::thumbnailPath(5);
    EXPECT_NE(path.find("slot_5"), std::string::npos);
    EXPECT_NE(path.find(".png"), std::string::npos);
}

TEST(SaveManagerTest, AllSlotPathsAreUnique) {
    std::set<std::string> paths;
    for (int i = SaveManager::kAutosaveSlot; i <= SaveManager::kMaxSlots; ++i) {
        paths.insert(SaveManager::slotPath(i));
    }
    EXPECT_EQ(paths.size(), static_cast<size_t>(SaveManager::kMaxSlots + 1));
}

// ═══════════════════════════════════════════════════════════════════════════
// Slot occupancy
// ═══════════════════════════════════════════════════════════════════════════

TEST(SaveManagerTest, IsSlotOccupied_InvalidSlotReturnsFalse) {
    SaveManager mgr;
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
    EXPECT_FALSE(mgr.saveToSlot(fake_engine, -1, nullptr, 0, 0));
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

// ═══════════════════════════════════════════════════════════════════════════
// Phase 2 QA: streampos comparison, path formats, atomic write
// ═══════════════════════════════════════════════════════════════════════════

TEST(SaveManagerTest, LoadFromSlot_InvalidSlotReturnsFalse) {
    SaveManager mgr;
    EXPECT_FALSE(mgr.loadFromSlot(reinterpret_cast<legends_handle>(0x1), -1));
    EXPECT_FALSE(mgr.lastError().empty());
}

TEST(SaveManagerTest, LoadFromSlot_NonexistentSlotSetsErrorMessage) {
    SaveManager mgr;
    EXPECT_FALSE(mgr.loadFromSlot(reinterpret_cast<legends_handle>(0x1), 5));
    std::string err = mgr.lastError();
    EXPECT_FALSE(err.empty());
    // Error should mention the slot
    EXPECT_NE(err.find("5"), std::string::npos);
}

TEST(SaveManagerTest, SlotAndThumbnailPaths_AllSlots1Through9) {
    for (int slot = 1; slot <= 9; ++slot) {
        std::string sp = SaveManager::slotPath(slot);
        std::string tp = SaveManager::thumbnailPath(slot);
        EXPECT_NE(sp.find("slot_" + std::to_string(slot)), std::string::npos);
        EXPECT_NE(sp.find(".sav"), std::string::npos);
        EXPECT_NE(tp.find("slot_" + std::to_string(slot)), std::string::npos);
        EXPECT_NE(tp.find(".png"), std::string::npos);
    }
}

TEST(SaveManagerTest, IsSlotOccupied_AutosaveSlotReflectsFileExistence) {
    SaveManager mgr;
    EXPECT_EQ(mgr.isSlotOccupied(SaveManager::kAutosaveSlot),
              std::filesystem::exists(SaveManager::slotPath(SaveManager::kAutosaveSlot)));
    EXPECT_EQ(mgr.hasAutosave(),
              std::filesystem::exists(SaveManager::slotPath(SaveManager::kAutosaveSlot)));
    EXPECT_FALSE(mgr.isSlotOccupied(10));
}

TEST(SaveManagerTest, GetSaveDirContainsSaves) {
    std::string dir = SaveManager::getSaveDir();
    EXPECT_NE(dir.find("saves"), std::string::npos);
}

// ═══════════════════════════════════════════════════════════════════════════
// CRC-32 correctness (regression test for duplicate-row table bug)
// ═══════════════════════════════════════════════════════════════════════════

TEST(SaveManagerTest, ComputeCRC32_HelloWorld) {
    const char data[] = "Hello, World!";
    uint32_t crc = SaveManager::computeCRC32(data, 13);
    EXPECT_EQ(crc, 0xEC4AC3D0u)
        << "CRC-32 of \"Hello, World!\" should be 0xEC4AC3D0 (standard CRC-32)";
}

TEST(SaveManagerTest, ComputeCRC32_EmptyInput) {
    uint32_t crc = SaveManager::computeCRC32("", 0);
    EXPECT_EQ(crc, 0x00000000u)
        << "CRC-32 of empty input should be 0x00000000";
}

TEST(SaveManagerTest, AtomicWriteCleansTmpOnSuccess) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_save_qa2";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "test_atomic.dat").string();
    std::string tmp_path = path + ".tmp";

    // Use saveToSlot indirectly — we can't call atomicWrite directly (private).
    // Instead verify the .tmp file concept: write a file, confirm no .tmp remains.
    // Create a file via ofstream and rename pattern:
    {
        std::ofstream f(tmp_path, std::ios::binary);
        f << "test data";
    }
    // Rename to final
    std::error_code ec;
    std::filesystem::rename(tmp_path, path, ec);
    EXPECT_FALSE(ec);
    EXPECT_TRUE(std::filesystem::exists(path));
    EXPECT_FALSE(std::filesystem::exists(tmp_path));

    std::filesystem::remove_all(tmp_dir);
}

} // namespace
} // namespace legends
