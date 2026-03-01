// SPDX-License-Identifier: MIT
#ifndef LEGENDS_PROXY_PROXY_CONNECTION_H
#define LEGENDS_PROXY_PROXY_CONNECTION_H

#include <atomic>
#include <cstdint>
#include <expected>
#include <mutex>
#include <span>
#include <vector>
#include <legends_ipc/control_channel.h>
#include <legends_ipc/framebuffer_shm.h>
#include <legends_ipc/audio_ring.h>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/message_types.h>
#include <legends_ipc/messages.h>

namespace legends_proxy {

// Singleton managing the IPC connection to the engine host process.
class ProxyConnection {
public:
    static ProxyConnection& instance();

    // Connect to an existing engine host (or auto-spawn one).
    std::expected<void, legends_ipc::IpcError> connect(
        const std::string& pipe_name,
        const std::string& shm_name,
        uint32_t max_fb_width = 1920,
        uint32_t max_fb_height = 1080,
        uint32_t audio_ring_frames = 2048);

    // Disconnect and cleanup.
    void disconnect();

    bool is_connected() const;

    // Send a request and wait for the matching response.
    template<typename Resp>
    std::expected<Resp, legends_ipc::IpcError>
    request(legends_ipc::MsgType req_type, std::span<const uint8_t> payload) {
        auto msg = send_and_recv(req_type, payload);
        if (!msg) return std::unexpected(msg.error());
        return Resp::deserialize(msg->payload);
    }

    // Access shared memory regions.
    legends_ipc::FramebufferShm* framebuffer() { return fb_.get(); }
    legends_ipc::AudioRingBuffer* audio_ring() { return audio_.get(); }

private:
    ProxyConnection() = default;

    std::expected<legends_ipc::MessageCodec::DecodedMessage, legends_ipc::IpcError>
    send_and_recv(legends_ipc::MsgType req_type, std::span<const uint8_t> payload);

    std::mutex mutex_;
    std::unique_ptr<legends_ipc::ControlChannel> channel_;
    std::unique_ptr<legends_ipc::FramebufferShm> fb_;
    std::unique_ptr<legends_ipc::AudioRingBuffer> audio_;
    std::atomic<uint32_t> next_seq_{1};
    bool connected_ = false;
};

} // namespace legends_proxy

#endif // LEGENDS_PROXY_PROXY_CONNECTION_H
