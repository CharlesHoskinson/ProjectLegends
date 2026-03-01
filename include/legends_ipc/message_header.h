// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_MESSAGE_HEADER_H
#define LEGENDS_IPC_MESSAGE_HEADER_H

#include <cstdint>
#include <expected>
#include <span>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/message_types.h>
#include <legends_ipc/wire_format.h>

namespace legends_ipc {

// 10-byte message header: msg_type(2) + payload_size(4) + sequence_id(4)
static constexpr size_t HeaderSize = 10;

struct MessageHeader {
    MsgType  msg_type    = MsgType::Handshake;
    uint32_t payload_size = 0;
    uint32_t sequence_id  = 0;

    // Serialize into buf at offset 0. buf must be >= HeaderSize.
    void serialize(std::span<uint8_t> buf) const {
        gsl_Expects(buf.size() >= HeaderSize);
        wire::write_u16_le(buf, 0, static_cast<uint16_t>(msg_type));
        wire::write_u32_le(buf, 2, payload_size);
        wire::write_u32_le(buf, 6, sequence_id);
    }

    // Deserialize from buf. buf must be >= HeaderSize.
    static std::expected<MessageHeader, IpcError>
    deserialize(std::span<const uint8_t> buf) {
        if (buf.size() < HeaderSize)
            return std::unexpected(IpcError::BufferTooSmall);
        MessageHeader h;
        h.msg_type     = static_cast<MsgType>(wire::read_u16_le(buf, 0));
        h.payload_size = wire::read_u32_le(buf, 2);
        h.sequence_id  = wire::read_u32_le(buf, 6);
        return h;
    }
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_MESSAGE_HEADER_H
