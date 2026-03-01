// SPDX-License-Identifier: MIT
#ifndef LEGENDS_PROXY_HEARTBEAT_H
#define LEGENDS_PROXY_HEARTBEAT_H

#include <atomic>
#include <chrono>
#include <functional>
#include <thread>
#include <legends_ipc/control_channel.h>

namespace legends_proxy {

using TimeoutCallback = std::function<void()>;

class HeartbeatMonitor {
public:
    ~HeartbeatMonitor();

    void start(legends_ipc::ControlChannel* channel,
               TimeoutCallback on_timeout,
               std::chrono::milliseconds interval = std::chrono::seconds(1),
               std::chrono::milliseconds timeout = std::chrono::seconds(5));

    void stop();
    void ack_received();

private:
    void heartbeat_loop();

    legends_ipc::ControlChannel* channel_ = nullptr;
    TimeoutCallback on_timeout_;
    std::chrono::milliseconds interval_{1000};
    std::chrono::milliseconds timeout_{5000};
    std::atomic<bool> running_{false};
    std::atomic<bool> ack_pending_{false};
    std::chrono::steady_clock::time_point last_send_;
    std::thread thread_;
};

} // namespace legends_proxy

#endif // LEGENDS_PROXY_HEARTBEAT_H
