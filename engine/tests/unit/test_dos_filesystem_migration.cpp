/**
 * @file test_dos_filesystem_migration.cpp
 * @brief Unit tests for DOS filesystem state in DOSBoxContext.
 *
 * Tests for Files array, Drives array, Devices array, and related state.
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"

using namespace dosbox;

// ===============================================================================
// Unit Tests
// ===============================================================================

/**
 * TEST-P09-U01: Files Array Default (all NULL)
 * Verify new context has NULL files array before initialization.
 */
TEST(DosFilesystemMigration, FilesArrayDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.dos_filesystem.files, nullptr);
    EXPECT_EQ(ctx.dos_filesystem.files_count, DosFilesystemState::DEFAULT_FILES);
}

/**
 * TEST-P09-U02: Drives Array Default (all NULL)
 * Verify new context has all drive pointers set to NULL.
 */
TEST(DosFilesystemMigration, DrivesArrayDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    for (size_t i = 0; i < DosFilesystemState::MAX_DRIVES; ++i) {
        EXPECT_EQ(ctx.dos_filesystem.drives[i], nullptr)
            << "Drive " << i << " should be NULL";
    }
}

/**
 * TEST-P09-U03: Devices Array Default (all NULL)
 * Verify new context has all device pointers set to NULL.
 */
TEST(DosFilesystemMigration, DevicesArrayDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    for (size_t i = 0; i < DosFilesystemState::MAX_DEVICES; ++i) {
        EXPECT_EQ(ctx.dos_filesystem.devices[i], nullptr)
            << "Device " << i << " should be NULL";
    }
}

/**
 * TEST-P09-U04: Files Count Configuration
 * Verify files_count can be configured and has correct default.
 */
TEST(DosFilesystemMigration, FilesCountConfiguration) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Default value
    EXPECT_EQ(ctx.dos_filesystem.files_count, 127u);

    // Modify
    ctx.dos_filesystem.files_count = 255;
    EXPECT_EQ(ctx.dos_filesystem.files_count, 255u);
}

/**
 * TEST-P09-U05: DOS Filesystem State Reset
 * Verify reset clears appropriate fields.
 */
TEST(DosFilesystemMigration, FilesystemStateReset) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Set some values
    ctx.dos_filesystem.force_sfn = true;
    ctx.dos_filesystem.sdrive = 5;
    ctx.dos_filesystem.lfn_filefind_handle = 10;

    // Simulate a mounted drive (just the pointer, not actual object)
    int dummy_drive = 42;
    ctx.dos_filesystem.drives[2] = reinterpret_cast<DOS_Drive*>(&dummy_drive);

    // Reset
    ctx.dos_filesystem.reset();

    // Check reset values
    EXPECT_FALSE(ctx.dos_filesystem.force_sfn);
    EXPECT_EQ(ctx.dos_filesystem.sdrive, 0);
    EXPECT_EQ(ctx.dos_filesystem.lfn_filefind_handle, -1);

    // Drives array should be cleared
    for (size_t i = 0; i < DosFilesystemState::MAX_DRIVES; ++i) {
        EXPECT_EQ(ctx.dos_filesystem.drives[i], nullptr);
    }
}

// ===============================================================================
// Integration Tests
// ===============================================================================

/**
 * TEST-P09-I01: Files Isolation Between Instances
 * Verify files array is isolated per instance.
 */
TEST(DosFilesystemMigration, FilesIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    // Set different files counts
    ctx1.dos_filesystem.files_count = 64;
    ctx2.dos_filesystem.files_count = 256;

    // Verify isolation
    EXPECT_EQ(ctx1.dos_filesystem.files_count, 64u);
    EXPECT_EQ(ctx2.dos_filesystem.files_count, 256u);
}

/**
 * TEST-P09-I02: Drives Isolation Between Instances
 * Verify drives array is isolated per instance.
 */
TEST(DosFilesystemMigration, DrivesIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    // Simulate different drives mounted (just pointers, not actual objects)
    int dummy1 = 1, dummy2 = 2;
    ctx1.dos_filesystem.drives[0] = reinterpret_cast<DOS_Drive*>(&dummy1);  // A:
    ctx2.dos_filesystem.drives[2] = reinterpret_cast<DOS_Drive*>(&dummy2);  // C:

    // Verify isolation
    EXPECT_NE(ctx1.dos_filesystem.drives[0], nullptr);
    EXPECT_EQ(ctx1.dos_filesystem.drives[2], nullptr);

    EXPECT_EQ(ctx2.dos_filesystem.drives[0], nullptr);
    EXPECT_NE(ctx2.dos_filesystem.drives[2], nullptr);
}

/**
 * TEST-P09-I03: Devices Isolation Between Instances
 * Verify devices array is isolated per instance.
 */
TEST(DosFilesystemMigration, DevicesIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    // Simulate different devices registered (just pointers)
    int dummy1 = 1, dummy2 = 2;
    ctx1.dos_filesystem.devices[0] = reinterpret_cast<DOS_Device*>(&dummy1);
    ctx2.dos_filesystem.devices[5] = reinterpret_cast<DOS_Device*>(&dummy2);

    // Verify isolation
    EXPECT_NE(ctx1.dos_filesystem.devices[0], nullptr);
    EXPECT_EQ(ctx1.dos_filesystem.devices[5], nullptr);

    EXPECT_EQ(ctx2.dos_filesystem.devices[0], nullptr);
    EXPECT_NE(ctx2.dos_filesystem.devices[5], nullptr);
}

/**
 * TEST-P09-I04: Additional File State Isolation
 * Verify force_sfn, sdrive, lfn_filefind_handle are isolated.
 */
TEST(DosFilesystemMigration, AdditionalStateIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    // Modify ctx1
    ctx1.dos_filesystem.force_sfn = true;
    ctx1.dos_filesystem.sdrive = 3;
    ctx1.dos_filesystem.lfn_filefind_handle = 42;

    // Modify ctx2 differently
    ctx2.dos_filesystem.force_sfn = false;
    ctx2.dos_filesystem.sdrive = 7;
    ctx2.dos_filesystem.lfn_filefind_handle = 99;

    // Verify isolation
    EXPECT_TRUE(ctx1.dos_filesystem.force_sfn);
    EXPECT_EQ(ctx1.dos_filesystem.sdrive, 3);
    EXPECT_EQ(ctx1.dos_filesystem.lfn_filefind_handle, 42);

    EXPECT_FALSE(ctx2.dos_filesystem.force_sfn);
    EXPECT_EQ(ctx2.dos_filesystem.sdrive, 7);
    EXPECT_EQ(ctx2.dos_filesystem.lfn_filefind_handle, 99);
}
