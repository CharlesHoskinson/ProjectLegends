// SPDX-License-Identifier: MIT
#ifdef _WIN32

#include <legends_ipc/engine_spawner.h>
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <string>
#include <vector>

namespace legends_ipc {
namespace {

std::string quote_arg(const std::string& arg) {
    if (arg.empty()) {
        return "\"\"";
    }

    bool needs_quotes = false;
    for (char ch : arg) {
        if (ch == ' ' || ch == '\t' || ch == '"') {
            needs_quotes = true;
            break;
        }
    }
    if (!needs_quotes) {
        return arg;
    }

    std::string quoted = "\"";
    for (char ch : arg) {
        if (ch == '"') {
            quoted += '\\';
        }
        quoted += ch;
    }
    quoted += '"';
    return quoted;
}

std::string build_command_line(const SpawnConfig& config) {
    std::vector<std::string> args;
    args.push_back(config.executable_path);
    args.insert(args.end(), config.arguments.begin(), config.arguments.end());
    if (!config.pipe_name.empty()) {
        args.push_back("--pipe");
        args.push_back(config.pipe_name);
    }
    if (!config.shm_name.empty()) {
        args.push_back("--shm");
        args.push_back(config.shm_name);
    }

    std::string command_line;
    for (const auto& arg : args) {
        if (!command_line.empty()) {
            command_line += ' ';
        }
        command_line += quote_arg(arg);
    }
    return command_line;
}

} // namespace

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
    std::string cmd = build_command_line(config);

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
    return proc;
}

} // namespace legends_ipc

#endif // _WIN32
