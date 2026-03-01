// SPDX-License-Identifier: MIT
#ifdef _WIN32

#include <legends_ipc/engine_spawner.h>
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <string>
#include <utility>

namespace legends_ipc {

EngineProcess::~EngineProcess() { cleanup(); }

EngineProcess::EngineProcess(EngineProcess&& other) noexcept
    : pid_(other.pid_)
    , process_handle_(other.process_handle_)
{
    other.pid_ = 0;
    other.process_handle_ = nullptr;
}

EngineProcess& EngineProcess::operator=(EngineProcess&& other) noexcept {
    if (this != &other) {
        cleanup();
        pid_ = other.pid_;
        process_handle_ = other.process_handle_;
        other.pid_ = 0;
        other.process_handle_ = nullptr;
    }
    return *this;
}

void EngineProcess::cleanup() {
    if (process_handle_) {
        CloseHandle(process_handle_);
        process_handle_ = nullptr;
    }
    pid_ = 0;
}

bool EngineProcess::is_alive() const {
    if (!process_handle_) return false;
    DWORD exit_code = 0;
    if (!GetExitCodeProcess(process_handle_, &exit_code)) return false;
    return exit_code == STILL_ACTIVE;
}

int EngineProcess::wait_for_exit(uint32_t timeout_ms) {
    if (!process_handle_) return -1;
    WaitForSingleObject(process_handle_, timeout_ms);
    DWORD exit_code = 0;
    GetExitCodeProcess(process_handle_, &exit_code);
    return static_cast<int>(exit_code);
}

void EngineProcess::terminate() {
    if (process_handle_) {
        TerminateProcess(process_handle_, 1);
        WaitForSingleObject(process_handle_, 3000);
    }
}

std::expected<EngineProcess, IpcError>
EngineSpawner::spawn(const SpawnConfig& config) {
    std::string cmd = "\"" + config.executable_path + "\"" +
                      " --pipe " + config.pipe_name +
                      " --shm " + config.shm_name;

    STARTUPINFOA si{};
    si.cb = sizeof(si);
    PROCESS_INFORMATION pi{};

    BOOL ok = CreateProcessA(
        nullptr,
        const_cast<char*>(cmd.c_str()),
        nullptr, nullptr, FALSE,
        CREATE_NO_WINDOW,
        nullptr, nullptr,
        &si, &pi);

    if (!ok)
        return std::unexpected(IpcError::SpawnFailed);

    CloseHandle(pi.hThread);

    EngineProcess proc;
    proc.pid_ = pi.dwProcessId;
    proc.process_handle_ = pi.hProcess;
    return std::move(proc);
}

} // namespace legends_ipc

#endif // _WIN32
