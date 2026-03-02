// SPDX-License-Identifier: MIT
#ifndef _WIN32

#include <legends_ipc/engine_spawner.h>
#include <spawn.h>
#include <sys/wait.h>
#include <signal.h>
#include <unistd.h>
#include <chrono>
#include <cstring>
#include <vector>

extern char** environ;

namespace legends_ipc {

EngineProcess::~EngineProcess() { cleanup(); }

EngineProcess::EngineProcess(EngineProcess&& other) noexcept
    : pid_(other.pid_)
{
    other.pid_ = 0;
}

EngineProcess& EngineProcess::operator=(EngineProcess&& other) noexcept {
    if (this != &other) {
        cleanup();
        pid_ = other.pid_;
        other.pid_ = 0;
    }
    return *this;
}

void EngineProcess::cleanup() {
    pid_ = 0;
}

bool EngineProcess::is_alive() const {
    if (pid_ == 0) return false;
    int status;
    pid_t result = waitpid(static_cast<pid_t>(pid_), &status, WNOHANG);
    return result == 0; // 0 means still running
}

int EngineProcess::wait_for_exit(uint32_t timeout_ms) {
    if (pid_ == 0) return -1;

    // Simple polling wait
    auto start = std::chrono::steady_clock::now();
    while (true) {
        int status;
        pid_t result = waitpid(static_cast<pid_t>(pid_), &status, WNOHANG);
        if (result > 0) {
            if (WIFEXITED(status)) return WEXITSTATUS(status);
            return -1;
        }
        auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - start).count();
        if (static_cast<uint32_t>(elapsed) >= timeout_ms) return -1;
        usleep(10000);
    }
}

void EngineProcess::terminate() {
    if (pid_ != 0) {
        kill(static_cast<pid_t>(pid_), SIGTERM);
        usleep(100000);
        kill(static_cast<pid_t>(pid_), SIGKILL);
        int status;
        waitpid(static_cast<pid_t>(pid_), &status, 0);
    }
}

std::expected<EngineProcess, IpcError>
EngineSpawner::spawn(const SpawnConfig& config) {
    std::vector<std::string> arg_strings = {
        config.executable_path,
        "--pipe", config.pipe_name,
        "--shm", config.shm_name
    };

    std::vector<char*> argv;
    for (auto& s : arg_strings) argv.push_back(const_cast<char*>(s.c_str()));
    argv.push_back(nullptr);

    pid_t child_pid;
    int ret = posix_spawn(&child_pid, config.executable_path.c_str(),
                          nullptr, nullptr, argv.data(), environ);
    if (ret != 0)
        return std::unexpected(IpcError::SpawnFailed);

    EngineProcess proc;
    proc.pid_ = static_cast<uint32_t>(child_pid);
    return proc;
}

} // namespace legends_ipc

#endif // !_WIN32
