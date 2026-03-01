// SPDX-License-Identifier: MIT
#include "crash_handler.h"
#include <chrono>

namespace legends_proxy {

CrashHandler::~CrashHandler() { stop(); }

void CrashHandler::start(legends_ipc::EngineProcess* process, CrashCallback callback) {
    stop();
    process_ = process;
    callback_ = std::move(callback);
    running_.store(true);
    monitor_thread_ = std::thread(&CrashHandler::monitor_loop, this);
}

void CrashHandler::stop() {
    running_.store(false);
    if (monitor_thread_.joinable())
        monitor_thread_.join();
}

void CrashHandler::monitor_loop() {
    while (running_.load()) {
        if (process_ && !process_->is_alive()) {
            if (callback_) callback_();
            break;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(200));
    }
}

bool CrashHandler::restart(const legends_ipc::SpawnConfig& config) {
    stop();
    auto result = legends_ipc::EngineSpawner::spawn(config);
    if (!result.has_value()) return false;
    // Caller must manage the new process lifetime
    return true;
}

} // namespace legends_proxy
