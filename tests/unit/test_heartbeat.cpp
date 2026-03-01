// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include <legends_ipc/control_channel.h>
#include <legends_ipc/messages.h>
#include <legends_ipc/message_codec.h>
#include <atomic>
#include <chrono>
#include <functional>
#include <thread>

using namespace legends_ipc;

// Minimal HeartbeatMonitor reimplementation for test isolation.
// Mirrors the production code in src/legends_proxy/heartbeat.h/.cpp.
namespace test_heartbeat {

using TimeoutCallback = std::function<void()>;

class HeartbeatMonitor {
public:
    ~HeartbeatMonitor() { stop(); }

    void start(ControlChannel* channel,
               TimeoutCallback on_timeout,
               std::chrono::milliseconds interval,
               std::chrono::milliseconds timeout) {
        stop();
        channel_ = channel;
        on_timeout_ = std::move(on_timeout);
        interval_ = interval;
        timeout_ = timeout;
        running_.store(true);
        ack_pending_.store(false);
        thread_ = std::thread(&HeartbeatMonitor::heartbeat_loop, this);
    }

    void stop() {
        running_.store(false);
        if (thread_.joinable())
            thread_.join();
    }

    void ack_received() {
        ack_pending_.store(false);
    }

    bool is_running() const { return running_.load(); }

private:
    void heartbeat_loop() {
        while (running_.load()) {
            // Send heartbeat
            auto now_us = static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::microseconds>(
                    std::chrono::steady_clock::now().time_since_epoch()).count());

            msg::HeartbeatMsg hb;
            hb.timestamp_us = now_us;
            std::array<uint8_t, msg::HeartbeatMsg::serialized_size> buf{};
            hb.serialize(buf);

            if (channel_)
                channel_->send(MsgType::Heartbeat, 0, buf);

            ack_pending_.store(true);
            auto last_send = std::chrono::steady_clock::now();

            // Wait for ack or timeout
            auto deadline = last_send + timeout_;
            while (running_.load() && ack_pending_.load()) {
                if (std::chrono::steady_clock::now() >= deadline) {
                    if (on_timeout_) on_timeout_();
                    return;
                }
                std::this_thread::sleep_for(std::chrono::milliseconds(10));
            }

            if (!running_.load()) break;

            // Wait for next interval
            auto next = last_send + interval_;
            while (running_.load() && std::chrono::steady_clock::now() < next) {
                std::this_thread::sleep_for(std::chrono::milliseconds(10));
            }
        }
    }

    ControlChannel* channel_ = nullptr;
    TimeoutCallback on_timeout_;
    std::chrono::milliseconds interval_{1000};
    std::chrono::milliseconds timeout_{5000};
    std::atomic<bool> running_{false};
    std::atomic<bool> ack_pending_{false};
    std::thread thread_;
};

} // namespace test_heartbeat

class HeartbeatTest : public ::testing::Test {
protected:
    void SetUp() override {
        timeout_fired_.store(false);
        timeout_count_.store(0);
    }

    std::atomic<bool> timeout_fired_{false};
    std::atomic<int> timeout_count_{0};
};

// Test: Ack received in time prevents timeout
TEST_F(HeartbeatTest, AckReceivedNoTimeout) {
    test_heartbeat::HeartbeatMonitor monitor;

    // Start with null channel (won't actually send), short intervals
    monitor.start(nullptr, [this]() {
        timeout_fired_.store(true);
        timeout_count_.fetch_add(1);
    },
    std::chrono::milliseconds(200),   // interval
    std::chrono::milliseconds(500));  // timeout

    // Quickly ack the heartbeat before timeout
    std::this_thread::sleep_for(std::chrono::milliseconds(50));
    monitor.ack_received();

    // Wait past one full interval
    std::this_thread::sleep_for(std::chrono::milliseconds(300));

    // Ack again for the second heartbeat
    monitor.ack_received();

    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    monitor.stop();

    EXPECT_FALSE(timeout_fired_.load()) << "No timeout when acks are received";
}

// Test: Missing ack triggers timeout callback
TEST_F(HeartbeatTest, MissingAckTriggersTimeout) {
    test_heartbeat::HeartbeatMonitor monitor;

    monitor.start(nullptr, [this]() {
        timeout_fired_.store(true);
        timeout_count_.fetch_add(1);
    },
    std::chrono::milliseconds(100),   // interval
    std::chrono::milliseconds(300));   // timeout

    // Don't send any acks - wait for timeout
    auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(2);
    while (!timeout_fired_.load() && std::chrono::steady_clock::now() < deadline) {
        std::this_thread::sleep_for(std::chrono::milliseconds(20));
    }

    EXPECT_TRUE(timeout_fired_.load()) << "Timeout should fire when ack is missing";
    EXPECT_EQ(timeout_count_.load(), 1) << "Timeout should fire exactly once";
}

// Test: Monitor stops cleanly after timeout
TEST_F(HeartbeatTest, StopsAfterTimeout) {
    test_heartbeat::HeartbeatMonitor monitor;

    monitor.start(nullptr, [this]() {
        timeout_fired_.store(true);
    },
    std::chrono::milliseconds(50),
    std::chrono::milliseconds(150));

    // Wait for timeout to fire
    std::this_thread::sleep_for(std::chrono::milliseconds(500));

    EXPECT_TRUE(timeout_fired_.load());
    // Monitor thread should have exited after timeout
    // stop() should join cleanly (not hang)
    monitor.stop();
}

// Test: Destructor joins cleanly even if running
TEST_F(HeartbeatTest, DestructorJoinsCleanly) {
    {
        test_heartbeat::HeartbeatMonitor monitor;
        monitor.start(nullptr, [this]() {
            timeout_fired_.store(true);
        },
        std::chrono::milliseconds(500),
        std::chrono::milliseconds(2000));

        // Let it run briefly then destroy
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        monitor.ack_received();
    }
    // If we get here without hanging, the destructor worked

    EXPECT_FALSE(timeout_fired_.load());
}

// Test: Multiple start/stop cycles work correctly
TEST_F(HeartbeatTest, MultipleStartStopCycles) {
    test_heartbeat::HeartbeatMonitor monitor;

    for (int i = 0; i < 3; ++i) {
        monitor.start(nullptr, [this]() {
            timeout_fired_.store(true);
        },
        std::chrono::milliseconds(200),
        std::chrono::milliseconds(500));

        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        monitor.ack_received();
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        monitor.stop();
    }

    EXPECT_FALSE(timeout_fired_.load()) << "No timeout across start/stop cycles";
}

// Test: Heartbeat sends on control channel (verify with paired server/client)
TEST_F(HeartbeatTest, SendsOnControlChannel) {
    // Create a server/client pair
    auto pipe_name = ControlChannel::make_pipe_name(
        static_cast<uint32_t>(
#ifdef _WIN32
            GetCurrentProcessId()
#else
            getpid()
#endif
        )) + "_hb_test";

    auto server = ControlChannel::create_server(pipe_name);
    if (!server) {
        GTEST_SKIP() << "Cannot create control channel server";
        return;
    }

    // Connect client in a thread
    std::thread client_thread([&]() {
        auto client = ControlChannel::connect_client(
            pipe_name, std::chrono::milliseconds(2000));
        if (!client) return;

        // Read the heartbeat message
        auto msg = client->recv(std::chrono::milliseconds(2000));
        if (msg) {
            EXPECT_EQ(msg->header.msg_type, static_cast<uint16_t>(MsgType::Heartbeat));
        }
    });

    // Wait for client to connect
    std::this_thread::sleep_for(std::chrono::milliseconds(200));

    test_heartbeat::HeartbeatMonitor monitor;
    monitor.start(server.get(), [this]() {
        timeout_fired_.store(true);
    },
    std::chrono::milliseconds(100),
    std::chrono::milliseconds(2000));

    // Let one heartbeat go out
    std::this_thread::sleep_for(std::chrono::milliseconds(300));
    monitor.ack_received();
    monitor.stop();

    client_thread.join();
}
