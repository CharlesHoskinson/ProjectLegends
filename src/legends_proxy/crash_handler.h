// SPDX-License-Identifier: MIT
#ifndef LEGENDS_PROXY_CRASH_HANDLER_H
#define LEGENDS_PROXY_CRASH_HANDLER_H

#include <atomic>
#include <functional>
#include <thread>
#include <legends_ipc/engine_spawner.h>

namespace legends_proxy {

using CrashCallback = std::function<void()>;

class CrashHandler {
public:
    ~CrashHandler();

    void start(legends_ipc::EngineProcess* process, CrashCallback callback);
    void stop();

    bool restart(const legends_ipc::SpawnConfig& config);

private:
    void monitor_loop();

    legends_ipc::EngineProcess* process_ = nullptr;
    CrashCallback callback_;
    std::atomic<bool> running_{false};
    std::thread monitor_thread_;
};

} // namespace legends_proxy

#endif // LEGENDS_PROXY_CRASH_HANDLER_H
