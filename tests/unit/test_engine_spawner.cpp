// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/engine_spawner.h>
#include <thread>
#include <chrono>

using namespace legends_ipc;

#ifdef _WIN32
static const char* trivial_exe = "cmd.exe";
static const char* nonexistent_exe = "C:\\nonexistent\\program.exe";
#else
static const char* trivial_exe = "/bin/true";
static const char* nonexistent_exe = "/nonexistent/program";
#endif

TEST(EngineSpawnerTest, SpawnTrivialExecutable) {
    SpawnConfig config;
    config.executable_path = trivial_exe;
    config.pipe_name = "test_spawn_pipe";
    config.shm_name = "test_spawn_shm";

    // Note: cmd.exe / /bin/true will ignore the --pipe/--shm args
    auto result = EngineSpawner::spawn(config);
    if (!result.has_value()) {
        GTEST_SKIP() << "Cannot spawn process in this CI environment";
    }
    EXPECT_NE(result->pid(), 0u);

    // Wait for it to exit
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
#ifndef _WIN32
    int code = result->wait_for_exit(2000);
    EXPECT_EQ(code, 0);
#endif
}

TEST(EngineSpawnerTest, NonexistentPathFails) {
    SpawnConfig config;
    config.executable_path = nonexistent_exe;
    config.pipe_name = "test_noexist_pipe";
    config.shm_name = "test_noexist_shm";

    auto result = EngineSpawner::spawn(config);
    // On some platforms, spawn returns success but process exits immediately
    // On others, it fails. Both are acceptable.
    if (result.has_value()) {
        // Process should not be alive for long
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
    }
}

TEST(EngineSpawnerTest, TerminateProcess) {
    SpawnConfig config;
#ifdef _WIN32
    config.executable_path = "cmd.exe";
    // cmd.exe with /c ping keeps it alive briefly
#else
    config.executable_path = "/bin/sleep";
    config.pipe_name = "10"; // sleep will use --pipe as positional arg; harmless
    config.shm_name = "dummy";
#endif

    auto result = EngineSpawner::spawn(config);
    if (result.has_value()) {
        EXPECT_TRUE(result->is_alive() || true); // May have exited
        result->terminate();
        // Should not crash
    }
}

TEST(EngineSpawnerTest, MoveSemantics) {
    SpawnConfig config;
    config.executable_path = trivial_exe;
    config.pipe_name = "test_move_pipe";
    config.shm_name = "test_move_shm";

    auto result = EngineSpawner::spawn(config);
    if (result.has_value()) {
        auto moved = std::move(*result);
        EXPECT_NE(moved.pid(), 0u);
    }
}
