// SPDX-License-Identifier: MIT
#ifndef _WIN32

#include <legends_ipc/control_channel.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <poll.h>
#include <unistd.h>
#include <sstream>
#include <cstring>

namespace legends_ipc {

ControlChannel::~ControlChannel() { cleanup(); }

ControlChannel::ControlChannel(ControlChannel&& other) noexcept
    : name_(std::move(other.name_))
    , is_server_(other.is_server_)
    , codec_(std::move(other.codec_))
    , fd_(other.fd_)
    , listen_fd_(other.listen_fd_)
{
    other.fd_ = -1;
    other.listen_fd_ = -1;
}

ControlChannel& ControlChannel::operator=(ControlChannel&& other) noexcept {
    if (this != &other) {
        cleanup();
        name_ = std::move(other.name_);
        is_server_ = other.is_server_;
        codec_ = std::move(other.codec_);
        fd_ = other.fd_;
        listen_fd_ = other.listen_fd_;
        other.fd_ = -1;
        other.listen_fd_ = -1;
    }
    return *this;
}

void ControlChannel::cleanup() {
    if (fd_ >= 0) { close(fd_); fd_ = -1; }
    if (listen_fd_ >= 0) {
        close(listen_fd_);
        listen_fd_ = -1;
        if (!name_.empty()) unlink(name_.c_str());
    }
}

std::string ControlChannel::make_pipe_name(uint32_t pid) {
    std::ostringstream oss;
    oss << "/tmp/legends_" << pid << ".sock";
    return oss.str();
}

std::expected<ControlChannel, IpcError>
ControlChannel::create_server(const std::string& pipe_name, uint32_t timeout_ms) {
    std::string path = pipe_name;
    if (path.find('/') == std::string::npos)
        path = "/tmp/legends_" + pipe_name + ".sock";

    unlink(path.c_str());

    int lfd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (lfd < 0) return std::unexpected(IpcError::SpawnFailed);

    struct sockaddr_un addr{};
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, path.c_str(), sizeof(addr.sun_path) - 1);

    if (bind(lfd, reinterpret_cast<struct sockaddr*>(&addr), sizeof(addr)) < 0) {
        close(lfd);
        return std::unexpected(IpcError::SpawnFailed);
    }

    if (listen(lfd, 1) < 0) {
        close(lfd);
        unlink(path.c_str());
        return std::unexpected(IpcError::SpawnFailed);
    }

    struct pollfd pfd{};
    pfd.fd = lfd;
    pfd.events = POLLIN;

    int ret = poll(&pfd, 1, static_cast<int>(timeout_ms));
    if (ret <= 0) {
        close(lfd);
        unlink(path.c_str());
        return std::unexpected(IpcError::Timeout);
    }

    int cfd = accept(lfd, nullptr, nullptr);
    if (cfd < 0) {
        close(lfd);
        unlink(path.c_str());
        return std::unexpected(IpcError::SpawnFailed);
    }

    ControlChannel ch;
    ch.name_ = path;
    ch.is_server_ = true;
    ch.fd_ = cfd;
    ch.listen_fd_ = lfd;
    return std::move(ch);
}

std::expected<ControlChannel, IpcError>
ControlChannel::connect_client(const std::string& pipe_name, uint32_t timeout_ms) {
    std::string path = pipe_name;
    if (path.find('/') == std::string::npos)
        path = "/tmp/legends_" + pipe_name + ".sock";

    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return std::unexpected(IpcError::NotConnected);

    struct sockaddr_un addr{};
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, path.c_str(), sizeof(addr.sun_path) - 1);

    // Retry connect until timeout
    auto start = std::chrono::steady_clock::now();
    while (true) {
        if (connect(fd, reinterpret_cast<struct sockaddr*>(&addr), sizeof(addr)) == 0)
            break;

        auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - start).count();
        if (elapsed >= timeout_ms) {
            close(fd);
            return std::unexpected(IpcError::Timeout);
        }
        usleep(10000); // 10ms
    }

    ControlChannel ch;
    ch.name_ = path;
    ch.is_server_ = false;
    ch.fd_ = fd;
    return std::move(ch);
}

std::expected<void, IpcError>
ControlChannel::send(MsgType msg_type, uint32_t sequence_id,
                     std::span<const uint8_t> payload) {
    auto wire = MessageCodec::encode(msg_type, sequence_id, payload);
    auto result = raw_write(wire);
    if (!result.has_value()) return std::unexpected(result.error());
    return {};
}

std::expected<MessageCodec::DecodedMessage, IpcError>
ControlChannel::recv(uint32_t timeout_ms) {
    auto msg = codec_.try_decode();
    if (msg.has_value()) return msg;

    uint8_t buf[8192];
    auto n = raw_read(buf, timeout_ms);
    if (!n.has_value()) return std::unexpected(n.error());
    if (*n == 0) return std::unexpected(IpcError::Timeout);

    codec_.feed(std::span<const uint8_t>(buf, *n));
    return codec_.try_decode();
}

bool ControlChannel::is_connected() const {
    return fd_ >= 0;
}

std::expected<size_t, IpcError>
ControlChannel::raw_write(std::span<const uint8_t> data) {
    if (!is_connected()) return std::unexpected(IpcError::NotConnected);

    size_t total = 0;
    while (total < data.size()) {
        ssize_t n = write(fd_, data.data() + total, data.size() - total);
        if (n <= 0) return std::unexpected(IpcError::BrokenPipe);
        total += static_cast<size_t>(n);
    }
    return total;
}

std::expected<size_t, IpcError>
ControlChannel::raw_read(std::span<uint8_t> buffer, uint32_t timeout_ms) {
    if (!is_connected()) return std::unexpected(IpcError::NotConnected);

    struct pollfd pfd{};
    pfd.fd = fd_;
    pfd.events = POLLIN;

    int ret = poll(&pfd, 1, static_cast<int>(timeout_ms));
    if (ret == 0) return size_t{0};
    if (ret < 0) return std::unexpected(IpcError::BrokenPipe);

    ssize_t n = read(fd_, buffer.data(), buffer.size());
    if (n <= 0) return std::unexpected(IpcError::BrokenPipe);
    return static_cast<size_t>(n);
}

} // namespace legends_ipc

#endif // !_WIN32
