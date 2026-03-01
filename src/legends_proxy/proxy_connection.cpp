// SPDX-License-Identifier: MIT
#include "proxy_connection.h"

namespace legends_proxy {

using namespace legends_ipc;

ProxyConnection& ProxyConnection::instance() {
    static ProxyConnection inst;
    return inst;
}

std::expected<void, IpcError> ProxyConnection::connect(
    const std::string& pipe_name,
    const std::string& shm_name,
    uint32_t max_fb_width,
    uint32_t max_fb_height,
    uint32_t audio_ring_frames)
{
    std::lock_guard lock(mutex_);
    if (connected_)
        return std::unexpected(IpcError::AlreadyConnected);

    // Create shared memory regions (server side creates them)
    auto fb = FramebufferShm::create(shm_name, max_fb_width, max_fb_height);
    if (!fb) return std::unexpected(fb.error());

    auto audio = AudioRingBuffer::create(shm_name, audio_ring_frames, 2, 44100);
    if (!audio) return std::unexpected(audio.error());

    // Create named pipe server
    auto ch = ControlChannel::create_server(pipe_name, 10000);
    if (!ch) return std::unexpected(ch.error());

    // Wait for HandshakeAck from engine
    auto msg = ch->recv(5000);
    if (!msg) return std::unexpected(msg.error());
    if (msg->header.msg_type != MsgType::HandshakeAck)
        return std::unexpected(IpcError::HandshakeFailed);

    auto ack = msg::HandshakeAck::deserialize(msg->payload);
    if (!ack || ack->error_code != 0)
        return std::unexpected(IpcError::HandshakeFailed);

    channel_ = std::make_unique<ControlChannel>(std::move(*ch));
    fb_ = std::make_unique<FramebufferShm>(std::move(*fb));
    audio_ = std::make_unique<AudioRingBuffer>(std::move(*audio));
    connected_ = true;
    next_seq_.store(1);
    return {};
}

void ProxyConnection::disconnect() {
    std::lock_guard lock(mutex_);
    if (connected_ && channel_) {
        msg::ShutdownMsg shutdown;
        shutdown.reason = 0;
        std::array<uint8_t, 4> buf{};
        shutdown.serialize(buf);
        channel_->send(MsgType::Shutdown, 0, buf);
        // Wait briefly for ack
        channel_->recv(1000);
    }
    channel_.reset();
    fb_.reset();
    audio_.reset();
    connected_ = false;
}

bool ProxyConnection::is_connected() const {
    return connected_;
}

std::expected<MessageCodec::DecodedMessage, IpcError>
ProxyConnection::send_and_recv(MsgType req_type, std::span<const uint8_t> payload) {
    std::lock_guard lock(mutex_);
    if (!connected_ || !channel_)
        return std::unexpected(IpcError::NotConnected);

    uint32_t seq = next_seq_.fetch_add(1);
    auto send_result = channel_->send(req_type, seq, payload);
    if (!send_result) return std::unexpected(send_result.error());

    // Read response (with timeout)
    auto msg = channel_->recv(5000);
    if (!msg) return std::unexpected(msg.error());
    return msg;
}

} // namespace legends_proxy
