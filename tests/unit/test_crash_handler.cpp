// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include <legends_ipc/engine_spawner.h>
#include <atomic>
#include <chrono>
#include <thread>

// Include crash_handler directly since it's in legends_proxy private sources
// For testing, we replicate the interface or use a minimal test harness.

namespace legends_proxy {

using CrashCallback = std::function<void()>;

class CrashHandler {
public:
    ~CrashHandler() { stop(); }

    void start(legends_ipc::EngineProcess* process, CrashCallback callback) {
        stop();
        process_ = process;
        callback_ = std::move(callback);
        running_.store(true);
        monitor_thread_ = std::thread(&CrashHandler::monitor_loop, this);
    }

    void stop() {
        running_.store(false);
        if (monitor_thread_.joinable())
            monitor_thread_.join();
    }

    bool restart(const legends_ipc::SpawnConfig& config) {
        stop();
        auto result = legends_ipc::EngineSpawner::spawn(config);
        if (!result.has_value()) return false;
        return true;
    }

private:
    void monitor_loop() {
        while (running_.load()) {
            if (process_ && !process_->is_alive()) {
                if (callback_) callback_();
                break;
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(200));
        }
    }

    legends_ipc::EngineProcess* process_ = nullptr;
    CrashCallback callback_;
    std::atomic<bool> running_{false};
    std::thread monitor_thread_;
};

} // namespace legends_proxy

// Mock EngineProcess for testing
namespace {

class MockProcess {
public:
    explicit MockProcess(bool alive = true) : alive_(alive) {}
    bool is_alive() const { return alive_.load(); }
    void kill() { alive_.store(false); }

private:
    std::atomic<bool> alive_;
};

} // namespace

class CrashHandlerTest : public ::testing::Test {
protected:
    void SetUp() override {
        callback_fired_.store(false);
        callback_count_.store(0);
    }

    std::atomic<bool> callback_fired_{false};
    std::atomic<int> callback_count_{0};
};

// Test: Callback fires when monitored process dies
TEST_F(CrashHandlerTest, CallbackFiresOnProcessDeath) {
    // We can't easily use EngineProcess directly since it manages OS handles.
    // Instead, test the CrashHandler logic with a real short-lived process.

    // Use a trivial command that exits immediately
#ifdef _WIN32
    legends_ipc::SpawnConfig config;
    config.executable_path = "cmd.exe";
    config.arguments = {"/c", "exit", "0"};
#else
    legends_ipc::SpawnConfig config;
    config.executable_path = "/bin/true";
#endif

    auto result = legends_ipc::EngineSpawner::spawn(config);
    if (!result.has_value()) {
        GTEST_SKIP() << "Cannot spawn test process";
        return;
    }

    auto process = std::move(result.value());

    // Wait for the trivial process to exit
    std::this_thread::sleep_for(std::chrono::milliseconds(500));

    legends_proxy::CrashHandler handler;
    handler.start(&process, [this]() {
        callback_fired_.store(true);
        callback_count_.fetch_add(1);
    });

    // The process is already dead, callback should fire within ~200ms poll
    auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(2);
    while (!callback_fired_.load() && std::chrono::steady_clock::now() < deadline) {
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
    }

    EXPECT_TRUE(callback_fired_.load()) << "Callback should fire when process is dead";
    EXPECT_EQ(callback_count_.load(), 1) << "Callback should fire exactly once";
}

// Test: No callback when process is alive and handler is stopped
TEST_F(CrashHandlerTest, NoCallbackWhenStopped) {
    // Spawn a long-running process
#ifdef _WIN32
    legends_ipc::SpawnConfig config;
    config.executable_path = "ping";
    config.arguments = {"-n", "31", "127.0.0.1"};
#else
    legends_ipc::SpawnConfig config;
    config.executable_path = "/bin/sleep";
    config.arguments = {"30"};
#endif

    auto result = legends_ipc::EngineSpawner::spawn(config);
    if (!result.has_value()) {
        GTEST_SKIP() << "Cannot spawn test process";
        return;
    }

    auto process = std::move(result.value());

    // EngineSpawner injects --pipe/--shm args; if the process doesn't
    // understand them it will exit immediately. Verify it's still alive.
    std::this_thread::sleep_for(std::chrono::milliseconds(200));
    if (!process.is_alive()) {
        process.terminate();
        GTEST_SKIP() << "Spawned process exited immediately (extra args not supported)";
        return;
    }

    legends_proxy::CrashHandler handler;
    handler.start(&process, [this]() {
        callback_fired_.store(true);
    });

    // Wait briefly then stop
    std::this_thread::sleep_for(std::chrono::milliseconds(300));
    handler.stop();

    EXPECT_FALSE(callback_fired_.load()) << "No callback while process is alive";

    // Clean up
    process.terminate();
}

// Test: Restart with invalid config fails gracefully
TEST_F(CrashHandlerTest, RestartWithInvalidConfigFails) {
    legends_proxy::CrashHandler handler;

    legends_ipc::SpawnConfig bad_config;
    bad_config.executable_path = "/nonexistent/binary/path";

    bool ok = handler.restart(bad_config);
    EXPECT_FALSE(ok) << "Restart with nonexistent binary should fail";
}

// Test: Handler destructor stops cleanly
TEST_F(CrashHandlerTest, DestructorStopsCleanly) {
#ifdef _WIN32
    legends_ipc::SpawnConfig config;
    config.executable_path = "ping";
    config.arguments = {"-n", "31", "127.0.0.1"};
#else
    legends_ipc::SpawnConfig config;
    config.executable_path = "/bin/sleep";
    config.arguments = {"30"};
#endif

    auto result = legends_ipc::EngineSpawner::spawn(config);
    if (!result.has_value()) {
        GTEST_SKIP() << "Cannot spawn test process";
        return;
    }

    auto process = std::move(result.value());

    std::this_thread::sleep_for(std::chrono::milliseconds(200));
    if (!process.is_alive()) {
        process.terminate();
        GTEST_SKIP() << "Spawned process exited immediately (extra args not supported)";
        return;
    }

    {
        legends_proxy::CrashHandler handler;
        handler.start(&process, [this]() {
            callback_fired_.store(true);
        });
        // Destructor should join cleanly
    }

    EXPECT_FALSE(callback_fired_.load());
    process.terminate();
}

// Test: Multiple start/stop cycles
TEST_F(CrashHandlerTest, MultipleStartStopCycles) {
#ifdef _WIN32
    legends_ipc::SpawnConfig config;
    config.executable_path = "ping";
    config.arguments = {"-n", "31", "127.0.0.1"};
#else
    legends_ipc::SpawnConfig config;
    config.executable_path = "/bin/sleep";
    config.arguments = {"30"};
#endif

    auto result = legends_ipc::EngineSpawner::spawn(config);
    if (!result.has_value()) {
        GTEST_SKIP() << "Cannot spawn test process";
        return;
    }

    auto process = std::move(result.value());

    std::this_thread::sleep_for(std::chrono::milliseconds(200));
    if (!process.is_alive()) {
        process.terminate();
        GTEST_SKIP() << "Spawned process exited immediately (extra args not supported)";
        return;
    }

    legends_proxy::CrashHandler handler;

    for (int i = 0; i < 3; ++i) {
        handler.start(&process, [this]() {
            callback_fired_.store(true);
        });
        std::this_thread::sleep_for(std::chrono::milliseconds(250));
        handler.stop();
    }

    EXPECT_FALSE(callback_fired_.load());
    process.terminate();
}
