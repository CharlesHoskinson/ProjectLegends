// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_ENGINE_SPAWNER_H
#define LEGENDS_IPC_ENGINE_SPAWNER_H

#include <cstdint>
#include <expected>
#include <string>
#include <vector>
#include <legends_ipc/ipc_error.h>

namespace legends_ipc {

struct SpawnConfig {
    std::string executable_path; // Path to legends_engine_host
    std::string pipe_name;
    std::string shm_name;
    std::vector<std::string> arguments; // Extra command-line arguments
};

// Represents a spawned engine host process.
class EngineProcess {
public:
    ~EngineProcess();

    EngineProcess(const EngineProcess&) = delete;
    EngineProcess& operator=(const EngineProcess&) = delete;
    EngineProcess(EngineProcess&& other) noexcept;
    EngineProcess& operator=(EngineProcess&& other) noexcept;

    bool is_alive() const;
    int wait_for_exit(uint32_t timeout_ms = 5000);
    void terminate();
    uint32_t pid() const { return pid_; }

private:
    friend class EngineSpawner;
    EngineProcess() = default;

    uint32_t pid_ = 0;
#ifdef _WIN32
    void* process_handle_ = nullptr;
#endif
    void cleanup();
};

class EngineSpawner {
public:
    static std::expected<EngineProcess, IpcError>
    spawn(const SpawnConfig& config);
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_ENGINE_SPAWNER_H
