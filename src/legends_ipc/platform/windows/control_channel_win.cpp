// SPDX-License-Identifier: MIT
#ifdef _WIN32

#include <legends_ipc/control_channel.h>
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <sstream>

namespace legends_ipc {

ControlChannel::~ControlChannel() { cleanup(); }

ControlChannel::ControlChannel(ControlChannel&& other) noexcept
    : name_(std::move(other.name_))
    , is_server_(other.is_server_)
    , codec_(std::move(other.codec_))
    , handle_(other.handle_)
{
    other.handle_ = nullptr;
}

ControlChannel& ControlChannel::operator=(ControlChannel&& other) noexcept {
    if (this != &other) {
        cleanup();
        name_ = std::move(other.name_);
        is_server_ = other.is_server_;
        codec_ = std::move(other.codec_);
        handle_ = other.handle_;
        other.handle_ = nullptr;
    }
    return *this;
}

void ControlChannel::cleanup() {
    if (handle_ && handle_ != INVALID_HANDLE_VALUE) {
        if (is_server_) {
            DisconnectNamedPipe(handle_);
        }
        CloseHandle(handle_);
        handle_ = nullptr;
    }
}

std::string ControlChannel::make_pipe_name(uint32_t pid) {
    std::ostringstream oss;
    oss << "\\\\.\\pipe\\legends_" << pid;
    return oss.str();
}

std::expected<ControlChannel, IpcError>
ControlChannel::create_server(const std::string& pipe_name, uint32_t timeout_ms) {
    std::string full_name = pipe_name;
    if (full_name.find("\\\\.\\pipe\\") == std::string::npos)
        full_name = "\\\\.\\pipe\\legends_" + pipe_name;

    HANDLE h = CreateNamedPipeA(
        full_name.c_str(),
        PIPE_ACCESS_DUPLEX | FILE_FLAG_OVERLAPPED,
        PIPE_TYPE_BYTE | PIPE_READMODE_BYTE | PIPE_WAIT,
        1, // max instances
        65536, 65536, // buffer sizes
        timeout_ms,
        nullptr);

    if (h == INVALID_HANDLE_VALUE)
        return std::unexpected(IpcError::SpawnFailed);

    // Wait for client connection
    OVERLAPPED ov{};
    ov.hEvent = CreateEventA(nullptr, TRUE, FALSE, nullptr);
    if (!ov.hEvent) {
        CloseHandle(h);
        return std::unexpected(IpcError::SpawnFailed);
    }

    BOOL connected = ConnectNamedPipe(h, &ov);
    if (!connected) {
        DWORD err = GetLastError();
        if (err == ERROR_IO_PENDING) {
            DWORD wait = WaitForSingleObject(ov.hEvent, timeout_ms);
            if (wait != WAIT_OBJECT_0) {
                CancelIo(h);
                CloseHandle(ov.hEvent);
                CloseHandle(h);
                return std::unexpected(IpcError::Timeout);
            }
        } else if (err != ERROR_PIPE_CONNECTED) {
            CloseHandle(ov.hEvent);
            CloseHandle(h);
            return std::unexpected(IpcError::SpawnFailed);
        }
    }
    CloseHandle(ov.hEvent);

    ControlChannel ch;
    ch.name_ = full_name;
    ch.is_server_ = true;
    ch.handle_ = h;
    return ch;
}

std::expected<ControlChannel, IpcError>
ControlChannel::connect_client(const std::string& pipe_name, uint32_t timeout_ms) {
    std::string full_name = pipe_name;
    if (full_name.find("\\\\.\\pipe\\") == std::string::npos)
        full_name = "\\\\.\\pipe\\legends_" + pipe_name;

    DWORD start = GetTickCount();
    HANDLE h = INVALID_HANDLE_VALUE;

    while (true) {
        h = CreateFileA(
            full_name.c_str(),
            GENERIC_READ | GENERIC_WRITE,
            0, nullptr,
            OPEN_EXISTING,
            FILE_FLAG_OVERLAPPED,
            nullptr);

        if (h != INVALID_HANDLE_VALUE) break;

        DWORD err = GetLastError();
        if (err != ERROR_PIPE_BUSY && err != ERROR_FILE_NOT_FOUND) {
            return std::unexpected(IpcError::NotConnected);
        }

        if (GetTickCount() - start >= timeout_ms) {
            return std::unexpected(IpcError::Timeout);
        }

        if (!WaitNamedPipeA(full_name.c_str(), 100)) {
            if (GetTickCount() - start >= timeout_ms)
                return std::unexpected(IpcError::Timeout);
        }
    }

    ControlChannel ch;
    ch.name_ = full_name;
    ch.is_server_ = false;
    ch.handle_ = h;
    return ch;
}

std::expected<void, IpcError>
ControlChannel::send(MsgType msg_type, uint32_t sequence_id,
                     std::span<const uint8_t> payload) {
    auto wire = MessageCodec::encode(msg_type, sequence_id, payload);
    auto result = raw_write(wire);
    if (!result.has_value())
        return std::unexpected(result.error());
    return {};
}

std::expected<MessageCodec::DecodedMessage, IpcError>
ControlChannel::recv(uint32_t timeout_ms) {
    // Try to decode from existing buffer first
    auto msg = codec_.try_decode();
    if (msg.has_value()) return msg;

    // Read more data
    uint8_t buf[8192];
    auto n = raw_read(buf, timeout_ms);
    if (!n.has_value()) return std::unexpected(n.error());
    if (*n == 0) return std::unexpected(IpcError::Timeout);

    codec_.feed(std::span<const uint8_t>(buf, *n));
    return codec_.try_decode();
}

bool ControlChannel::is_connected() const {
    return handle_ != nullptr && handle_ != INVALID_HANDLE_VALUE;
}

std::expected<size_t, IpcError>
ControlChannel::raw_write(std::span<const uint8_t> data) {
    if (!is_connected()) return std::unexpected(IpcError::NotConnected);

    OVERLAPPED ov{};
    ov.hEvent = CreateEventA(nullptr, TRUE, FALSE, nullptr);
    DWORD written = 0;

    BOOL ok = WriteFile(handle_, data.data(),
                        static_cast<DWORD>(data.size()), &written, &ov);
    if (!ok) {
        DWORD err = GetLastError();
        if (err == ERROR_IO_PENDING) {
            if (!GetOverlappedResult(handle_, &ov, &written, TRUE)) {
                CloseHandle(ov.hEvent);
                return std::unexpected(IpcError::BrokenPipe);
            }
        } else {
            CloseHandle(ov.hEvent);
            return std::unexpected(IpcError::BrokenPipe);
        }
    }
    CloseHandle(ov.hEvent);
    return static_cast<size_t>(written);
}

std::expected<size_t, IpcError>
ControlChannel::raw_read(std::span<uint8_t> buffer, uint32_t timeout_ms) {
    if (!is_connected()) return std::unexpected(IpcError::NotConnected);

    OVERLAPPED ov{};
    ov.hEvent = CreateEventA(nullptr, TRUE, FALSE, nullptr);
    DWORD bytes_read = 0;

    BOOL ok = ReadFile(handle_, buffer.data(),
                       static_cast<DWORD>(buffer.size()), &bytes_read, &ov);
    if (!ok) {
        DWORD err = GetLastError();
        if (err == ERROR_IO_PENDING) {
            DWORD wait = WaitForSingleObject(ov.hEvent, timeout_ms);
            if (wait == WAIT_TIMEOUT) {
                CancelIo(handle_);
                CloseHandle(ov.hEvent);
                return size_t{0};
            }
            if (!GetOverlappedResult(handle_, &ov, &bytes_read, FALSE)) {
                CloseHandle(ov.hEvent);
                return std::unexpected(IpcError::BrokenPipe);
            }
        } else if (err == ERROR_BROKEN_PIPE || err == ERROR_PIPE_NOT_CONNECTED) {
            CloseHandle(ov.hEvent);
            return std::unexpected(IpcError::BrokenPipe);
        } else {
            CloseHandle(ov.hEvent);
            return std::unexpected(IpcError::BrokenPipe);
        }
    }
    CloseHandle(ov.hEvent);
    return static_cast<size_t>(bytes_read);
}

} // namespace legends_ipc

#endif // _WIN32
