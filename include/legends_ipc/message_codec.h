// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_MESSAGE_CODEC_H
#define LEGENDS_IPC_MESSAGE_CODEC_H

#include <cstdint>
#include <expected>
#include <span>
#include <vector>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/message_header.h>
#include <legends_ipc/message_types.h>

namespace legends_ipc {

// Framing layer: encode header+payload into a wire buffer,
// decode messages from a byte stream (accumulating partial reads).
class MessageCodec {
public:
    // Maximum allowed payload size (64 MB).  Messages claiming a larger
    // payload are rejected immediately to prevent unbounded allocation
    // from untrusted wire data.
    static constexpr uint32_t kMaxPayloadSize = 64 * 1024 * 1024;

    struct DecodedMessage {
        MessageHeader header;
        std::vector<uint8_t> payload;
    };

    // Encode a header + payload into a contiguous wire buffer.
    // Returns header bytes followed by payload bytes.
    static std::vector<uint8_t> encode(
        MsgType msg_type,
        uint32_t sequence_id,
        std::span<const uint8_t> payload);

    // Feed incoming bytes into the decoder.
    void feed(std::span<const uint8_t> data);

    // Try to extract a complete message from the internal buffer.
    // Returns the message if enough data is available, or an error.
    // Returns IpcError::BufferTooSmall if not enough data yet (not a real error,
    // just means "call feed() more").
    std::expected<DecodedMessage, IpcError> try_decode();

    // Reset internal buffer state (e.g. after error).
    void reset();

    // How many bytes are buffered but not yet decoded.
    size_t buffered_bytes() const { return buffer_.size(); }

private:
    std::vector<uint8_t> buffer_;
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_MESSAGE_CODEC_H
