// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_CONTROL_CHANNEL_H
#define LEGENDS_IPC_CONTROL_CHANNEL_H

#include <cstdint>
#include <expected>
#include <span>
#include <string>
#include <vector>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/message_codec.h>

namespace legends_ipc {

// Named pipe (Win) / Unix domain socket (POSIX) control channel.
// Server creates the pipe, client connects.
// Messages are framed by MessageCodec (header + payload).
class ControlChannel {
public:
    ~ControlChannel();

    ControlChannel(const ControlChannel&) = delete;
    ControlChannel& operator=(const ControlChannel&) = delete;
    ControlChannel(ControlChannel&& other) noexcept;
    ControlChannel& operator=(ControlChannel&& other) noexcept;

    // Create server-side channel. Blocks until client connects (up to timeout_ms).
    static std::expected<ControlChannel, IpcError>
    create_server(const std::string& pipe_name, uint32_t timeout_ms = 5000);

    // Connect as client to an existing server.
    static std::expected<ControlChannel, IpcError>
    connect_client(const std::string& pipe_name, uint32_t timeout_ms = 5000);

    // Send a framed message (header + payload).
    std::expected<void, IpcError> send(
        MsgType msg_type, uint32_t sequence_id,
        std::span<const uint8_t> payload);

    // Receive a complete framed message. Blocks up to timeout_ms.
    // Returns BufferTooSmall if timeout fires (no data).
    std::expected<MessageCodec::DecodedMessage, IpcError>
    recv(uint32_t timeout_ms = 5000);

    bool is_connected() const;
    const std::string& pipe_name() const { return name_; }

    // Generate platform-appropriate pipe name from PID.
    static std::string make_pipe_name(uint32_t pid);

private:
    ControlChannel() = default;

    std::string name_;
    bool is_server_ = false;
    MessageCodec codec_;

#ifdef _WIN32
    void* handle_ = nullptr; // HANDLE (INVALID_HANDLE_VALUE = not connected)
#else
    int fd_ = -1;
    int listen_fd_ = -1;
#endif

    // Low-level read/write (platform-specific).
    std::expected<size_t, IpcError> raw_write(std::span<const uint8_t> data);
    std::expected<size_t, IpcError> raw_read(std::span<uint8_t> buffer, uint32_t timeout_ms);

    void cleanup();
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_CONTROL_CHANNEL_H
