// SPDX-License-Identifier: MIT
#include <legends_ipc/message_codec.h>
#include <algorithm>
#include <cstring>

namespace legends_ipc {

std::vector<uint8_t> MessageCodec::encode(
    MsgType msg_type,
    uint32_t sequence_id,
    std::span<const uint8_t> payload)
{
    std::vector<uint8_t> wire(HeaderSize + payload.size());
    MessageHeader hdr;
    hdr.msg_type     = msg_type;
    hdr.payload_size = static_cast<uint32_t>(payload.size());
    hdr.sequence_id  = sequence_id;
    hdr.serialize(std::span<uint8_t>(wire.data(), HeaderSize));
    if (!payload.empty())
        std::memcpy(wire.data() + HeaderSize, payload.data(), payload.size());
    return wire;
}

void MessageCodec::feed(std::span<const uint8_t> data) {
    buffer_.insert(buffer_.end(), data.begin(), data.end());
}

std::expected<MessageCodec::DecodedMessage, IpcError> MessageCodec::try_decode() {
    if (buffer_.size() < HeaderSize)
        return std::unexpected(IpcError::BufferTooSmall);

    auto hdr_result = MessageHeader::deserialize(
        std::span<const uint8_t>(buffer_.data(), HeaderSize));
    if (!hdr_result.has_value())
        return std::unexpected(hdr_result.error());

    auto& hdr = *hdr_result;
    size_t total = HeaderSize + hdr.payload_size;
    if (buffer_.size() < total)
        return std::unexpected(IpcError::BufferTooSmall);

    DecodedMessage msg;
    msg.header = hdr;
    if (hdr.payload_size > 0) {
        msg.payload.assign(
            buffer_.begin() + HeaderSize,
            buffer_.begin() + static_cast<ptrdiff_t>(total));
    }

    buffer_.erase(buffer_.begin(), buffer_.begin() + static_cast<ptrdiff_t>(total));
    return msg;
}

void MessageCodec::reset() {
    buffer_.clear();
}

} // namespace legends_ipc
