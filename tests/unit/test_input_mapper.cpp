// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for InputMapper — remap, translate, load/save persistence.

#include <gtest/gtest.h>
#include "app/input_mapper.h"
#include "app/scancode_map.h"

#include <filesystem>
#include <fstream>
#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Default translation (no remaps)
// ═══════════════════════════════════════════════════════════════════════════

TEST(InputMapperTest, TranslateWithoutRemapUsesDefault) {
    InputMapper mapper;
    // A key: SDL 0x04 → AT 0x1E
    auto at = mapper.translate(0x04);
    EXPECT_EQ(at.code, 0x1E);
    EXPECT_FALSE(at.extended);
}

TEST(InputMapperTest, TranslateUnknownReturnsZero) {
    InputMapper mapper;
    auto at = mapper.translate(0xFF);
    EXPECT_EQ(at.code, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Remap
// ═══════════════════════════════════════════════════════════════════════════

TEST(InputMapperTest, RemapChangesTranslation) {
    InputMapper mapper;
    // Remap A (0x04) to behave as B (0x05)
    mapper.remap(0x04, 0x05);
    auto at = mapper.translate(0x04);
    // B → AT 0x30
    EXPECT_EQ(at.code, 0x30);
}

TEST(InputMapperTest, RemapDoesNotAffectOtherKeys) {
    InputMapper mapper;
    mapper.remap(0x04, 0x05);
    // B (0x05) should still map to itself
    auto at = mapper.translate(0x05);
    EXPECT_EQ(at.code, 0x30);
}

TEST(InputMapperTest, ClearRemapRestoresDefault) {
    InputMapper mapper;
    mapper.remap(0x04, 0x05);
    mapper.clearRemap(0x04);
    auto at = mapper.translate(0x04);
    EXPECT_EQ(at.code, 0x1E); // back to A
}

TEST(InputMapperTest, ClearAllRemovesEverything) {
    InputMapper mapper;
    mapper.remap(0x04, 0x05);
    mapper.remap(0x06, 0x07);
    EXPECT_EQ(mapper.customCount(), 2u);
    mapper.clearAll();
    EXPECT_EQ(mapper.customCount(), 0u);
}

TEST(InputMapperTest, CustomCountTracksRemaps) {
    InputMapper mapper;
    EXPECT_EQ(mapper.customCount(), 0u);
    mapper.remap(0x10, 0x11);
    EXPECT_EQ(mapper.customCount(), 1u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Persistence: save/load
// ═══════════════════════════════════════════════════════════════════════════

TEST(InputMapperTest, SaveAndLoadRoundTrip) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_test";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        InputMapper mapper;
        mapper.remap(0x04, 0x05); // A → B
        mapper.remap(0x1E, 0x1F); // 1 → 2
        EXPECT_TRUE(mapper.saveToFile(path));
    }

    {
        InputMapper mapper;
        EXPECT_TRUE(mapper.loadFromFile(path));
        EXPECT_EQ(mapper.customCount(), 2u);
        // A → B → AT 0x30
        auto at = mapper.translate(0x04);
        EXPECT_EQ(at.code, 0x30);
    }

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, LoadFromMissingFileReturnsFalse) {
    InputMapper mapper;
    EXPECT_FALSE(mapper.loadFromFile("/nonexistent/path/mapper.txt"));
}

TEST(InputMapperTest, LoadIgnoresComments) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_test2";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        std::ofstream file(path);
        file << "# This is a comment\n";
        file << "0x04 0x05\n";
        file << "# Another comment\n";
        file << "\n"; // empty line
    }

    InputMapper mapper;
    EXPECT_TRUE(mapper.loadFromFile(path));
    EXPECT_EQ(mapper.customCount(), 1u);

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, LoadIgnoresMalformedLines) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_test3";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        std::ofstream file(path);
        file << "0x04 0x05\n";
        file << "badline\n";
        file << "0xGG 0xHH\n"; // invalid hex
        file << "0x06 0x07\n";
    }

    InputMapper mapper;
    EXPECT_TRUE(mapper.loadFromFile(path));
    EXPECT_EQ(mapper.customCount(), 2u); // only valid lines

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, RemapToExtendedKey) {
    InputMapper mapper;
    // Remap A (0x04) to Right Arrow (0x4F, which is extended E0 4D)
    mapper.remap(0x04, 0x4F);
    auto at = mapper.translate(0x04);
    EXPECT_EQ(at.code, 0x4D);
    EXPECT_TRUE(at.extended);
}

// ═══════════════════════════════════════════════════════════════════════════
// Phase 2 QA: format string and round-trip coverage
// ═══════════════════════════════════════════════════════════════════════════

TEST(InputMapperTest, SaveLoadRoundTrip_ScancodeAbove0xFF) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_qa1";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        InputMapper mapper;
        mapper.remap(0x01A0, 0x01B0);
        EXPECT_TRUE(mapper.saveToFile(path));
    }

    {
        InputMapper mapper;
        EXPECT_TRUE(mapper.loadFromFile(path));
        EXPECT_EQ(mapper.customCount(), 1u);
        // Verify the remap survived the round trip
        auto at_remapped = mapper.translate(0x01A0);
        auto at_direct = sdlScancodeToAT(0x01B0);
        EXPECT_EQ(at_remapped.code, at_direct.code);
        EXPECT_EQ(at_remapped.extended, at_direct.extended);
    }

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, SaveLoadRoundTrip_ScancodeExactly0xFF) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_qa2";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        InputMapper mapper;
        mapper.remap(0xFF, 0x04);
        EXPECT_TRUE(mapper.saveToFile(path));
    }

    {
        InputMapper mapper;
        EXPECT_TRUE(mapper.loadFromFile(path));
        EXPECT_EQ(mapper.customCount(), 1u);
        auto at = mapper.translate(0xFF);
        EXPECT_EQ(at.code, sdlScancodeToAT(0x04).code);
    }

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, SaveLoadRoundTrip_MultipleEntries) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_qa3";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        InputMapper mapper;
        mapper.remap(0x04, 0x05);
        mapper.remap(0x100, 0x200);
        mapper.remap(0x0F, 0x10);
        EXPECT_TRUE(mapper.saveToFile(path));
    }

    {
        InputMapper mapper;
        EXPECT_TRUE(mapper.loadFromFile(path));
        EXPECT_EQ(mapper.customCount(), 3u);
    }

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, LoadMixed2DigitAnd4DigitHex) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_qa4";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        std::ofstream file(path);
        file << "0x04 0x05\n";       // 2-digit
        file << "0x01A0 0x01B0\n";   // 4-digit
        file << "0xFF 0x10\n";       // boundary
    }

    InputMapper mapper;
    EXPECT_TRUE(mapper.loadFromFile(path));
    EXPECT_EQ(mapper.customCount(), 3u);

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, SavedFileContentMatchesExpectedFormat) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_qa5";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    {
        InputMapper mapper;
        mapper.remap(0x01A0, 0x01B0);
        EXPECT_TRUE(mapper.saveToFile(path));
    }

    std::string content;
    {
        // Read the file and verify the format uses 4-digit hex
        std::ifstream file(path);
        content.assign(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
    } // file closed before remove_all

    EXPECT_NE(content.find("0x01A0 0x01B0"), std::string::npos)
        << "File content: " << content;

    std::filesystem::remove_all(tmp_dir);
}

TEST(InputMapperTest, SaveToReadOnlyPathReturnsFalse) {
    bool ok = InputMapper{}.saveToFile("/nonexistent/dir/mapper.txt");
    EXPECT_FALSE(ok);
}

TEST(InputMapperTest, LoadFromEmptyFileReturnsTrue) {
    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_mapper_qa6";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "mapper.txt").string();

    { std::ofstream file(path); } // create empty file

    InputMapper mapper;
    EXPECT_TRUE(mapper.loadFromFile(path));
    EXPECT_EQ(mapper.customCount(), 0u);

    std::filesystem::remove_all(tmp_dir);
}

} // namespace
} // namespace legends
