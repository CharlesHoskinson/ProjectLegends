// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for PrinterManager.

#include <gtest/gtest.h>
#include "app/printer_manager.h"

#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Default state
// ═══════════════════════════════════════════════════════════════════════════

TEST(PrinterManagerTest, DefaultOutputDirectoryEmpty) {
    PrinterManager pm;
    EXPECT_TRUE(pm.outputDirectory().empty());
}

TEST(PrinterManagerTest, DefaultNotEnabled) {
    PrinterManager pm;
    EXPECT_FALSE(pm.isEnabled());
}

TEST(PrinterManagerTest, DefaultFilesWrittenZero) {
    PrinterManager pm;
    EXPECT_EQ(pm.filesWritten(), 0u);
}

TEST(PrinterManagerTest, DefaultNotConfigured) {
    PrinterManager pm;
    EXPECT_FALSE(pm.isConfigured());
}

// ═══════════════════════════════════════════════════════════════════════════
// setOutputDirectory / isConfigured
// ═══════════════════════════════════════════════════════════════════════════

TEST(PrinterManagerTest, SetOutputDirectory_Stores) {
    PrinterManager pm;
    pm.setOutputDirectory("/tmp/printer");
    EXPECT_EQ(pm.outputDirectory(), "/tmp/printer");
}

TEST(PrinterManagerTest, IsConfigured_TrueWhenDirSet) {
    PrinterManager pm;
    pm.setOutputDirectory("/tmp/printer");
    EXPECT_TRUE(pm.isConfigured());
}

TEST(PrinterManagerTest, MultipleSetOutputDirectoryCalls) {
    PrinterManager pm;
    pm.setOutputDirectory("/first");
    EXPECT_EQ(pm.outputDirectory(), "/first");
    pm.setOutputDirectory("/second");
    EXPECT_EQ(pm.outputDirectory(), "/second");
}

// ═══════════════════════════════════════════════════════════════════════════
// setEnabled / isEnabled
// ═══════════════════════════════════════════════════════════════════════════

TEST(PrinterManagerTest, SetEnabled_True) {
    PrinterManager pm;
    pm.setEnabled(true);
    EXPECT_TRUE(pm.isEnabled());
}

TEST(PrinterManagerTest, SetEnabled_False) {
    PrinterManager pm;
    pm.setEnabled(true);
    pm.setEnabled(false);
    EXPECT_FALSE(pm.isEnabled());
}

// ═══════════════════════════════════════════════════════════════════════════
// generateFilename
// ═══════════════════════════════════════════════════════════════════════════

TEST(PrinterManagerTest, GenerateFilename_Initial) {
    PrinterManager pm;
    EXPECT_EQ(pm.generateFilename(), "print_0000.prn");
}

TEST(PrinterManagerTest, GenerateFilename_AfterFileWritten) {
    PrinterManager pm;
    pm.fileWritten();
    EXPECT_EQ(pm.generateFilename(), "print_0001.prn");
}

TEST(PrinterManagerTest, GenerateFilename_CustomExtension) {
    PrinterManager pm;
    EXPECT_EQ(pm.generateFilename("txt"), "print_0000.txt");
}

TEST(PrinterManagerTest, GenerateFilename_EmptyExtension) {
    PrinterManager pm;
    EXPECT_EQ(pm.generateFilename(""), "print_0000");
}

TEST(PrinterManagerTest, GenerateFilename_Padding) {
    PrinterManager pm;
    for (int i = 0; i < 42; ++i) {
        pm.fileWritten();
    }
    EXPECT_EQ(pm.generateFilename(), "print_0042.prn");
}

TEST(PrinterManagerTest, GenerateFilename_LargeCount) {
    PrinterManager pm;
    for (int i = 0; i < 10000; ++i) {
        pm.fileWritten();
    }
    // 10000 overflows 4-digit padding; std::setw widens automatically.
    std::string name = pm.generateFilename();
    EXPECT_NE(name.find("10000"), std::string::npos);
}

// ═══════════════════════════════════════════════════════════════════════════
// nextOutputPath
// ═══════════════════════════════════════════════════════════════════════════

TEST(PrinterManagerTest, NextOutputPath_CombinesDirAndFilename) {
    PrinterManager pm;
    pm.setOutputDirectory("/output");
    EXPECT_EQ(pm.nextOutputPath(), "/output/print_0000.prn");
}

TEST(PrinterManagerTest, NextOutputPath_WithTrailingSlash) {
    // The implementation always adds "/", so trailing slash produces "//".
    // This tests current behaviour, not necessarily ideal behaviour.
    PrinterManager pm;
    pm.setOutputDirectory("/output/");
    std::string path = pm.nextOutputPath();
    // Should contain the filename.
    EXPECT_NE(path.find("print_0000.prn"), std::string::npos);
}

TEST(PrinterManagerTest, NextOutputPath_WithoutTrailingSlash) {
    PrinterManager pm;
    pm.setOutputDirectory("/output");
    EXPECT_EQ(pm.nextOutputPath(), "/output/print_0000.prn");
}

// ═══════════════════════════════════════════════════════════════════════════
// fileWritten
// ═══════════════════════════════════════════════════════════════════════════

TEST(PrinterManagerTest, FileWritten_Increments) {
    PrinterManager pm;
    EXPECT_EQ(pm.filesWritten(), 0u);
    pm.fileWritten();
    EXPECT_EQ(pm.filesWritten(), 1u);
    pm.fileWritten();
    EXPECT_EQ(pm.filesWritten(), 2u);
}

TEST(PrinterManagerTest, FileWritten_MultipleIncrements) {
    PrinterManager pm;
    for (int i = 0; i < 100; ++i) {
        pm.fileWritten();
    }
    EXPECT_EQ(pm.filesWritten(), 100u);
}

TEST(PrinterManagerTest, FilesWritten_DoesNotResetOnDirectoryChange) {
    PrinterManager pm;
    pm.setOutputDirectory("/first");
    pm.fileWritten();
    pm.fileWritten();
    pm.setOutputDirectory("/second");
    EXPECT_EQ(pm.filesWritten(), 2u);
}

} // namespace
} // namespace legends
