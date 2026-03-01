// SPDX-License-Identifier: MIT
#include "heartbeat.h"
#include <legends_ipc/messages.h>
#include <array>

namespace legends_proxy {

using namespace legends_ipc;

HeartbeatMonitor::~HeartbeatMonitor() { stop(); }

void HeartbeatMonitor::start(ControlChannel* channel,
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

void HeartbeatMonitor::stop() {
    running_.store(false);
    if (thread_.joinable())
        thread_.join();
}

void HeartbeatMonitor::ack_received() {
    ack_pending_.store(false);
}

void HeartbeatMonitor::heartbeat_loop() {
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
            (void)channel_->send(MsgType::Heartbeat, 0, buf);

        ack_pending_.store(true);
        last_send_ = std::chrono::steady_clock::now();

        // Wait for ack or timeout
        auto deadline = last_send_ + timeout_;
        while (running_.load() && ack_pending_.load()) {
            if (std::chrono::steady_clock::now() >= deadline) {
                if (on_timeout_) on_timeout_();
                return; // stop monitoring after timeout
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(50));
        }

        if (!running_.load()) break;

        // Wait for next interval
        auto next = last_send_ + interval_;
        while (running_.load() && std::chrono::steady_clock::now() < next) {
            std::this_thread::sleep_for(std::chrono::milliseconds(50));
        }
    }
}

} // namespace legends_proxy
