// SPDX-License-Identifier: GPL-2.0-or-later
#include <gtest/gtest.h>
#include "engine_host/cli_parser.h"

using namespace legends::engine_host;

TEST(EngineHostCliTest, ValidArgs) {
    const char* argv[] = {"engine_host", "--pipe", "test_pipe", "--shm", "test_shm"};
    auto result = parse_cli(5, argv);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->pipe_name, "test_pipe");
    EXPECT_EQ(result->shm_name, "test_shm");
    EXPECT_FALSE(result->version);
}

TEST(EngineHostCliTest, MissingPipe) {
    const char* argv[] = {"engine_host", "--shm", "test_shm"};
    auto result = parse_cli(3, argv);
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), CliError::MissingPipe);
}

TEST(EngineHostCliTest, MissingShm) {
    const char* argv[] = {"engine_host", "--pipe", "test_pipe"};
    auto result = parse_cli(3, argv);
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), CliError::MissingShm);
}

TEST(EngineHostCliTest, VersionFlag) {
    const char* argv[] = {"engine_host", "--version"};
    auto result = parse_cli(2, argv);
    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result->version);
}

TEST(EngineHostCliTest, UnknownFlag) {
    const char* argv[] = {"engine_host", "--unknown"};
    auto result = parse_cli(2, argv);
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), CliError::UnknownFlag);
}

TEST(EngineHostCliTest, PipeValueMissing) {
    const char* argv[] = {"engine_host", "--pipe"};
    auto result = parse_cli(2, argv);
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), CliError::MissingPipe);
}
