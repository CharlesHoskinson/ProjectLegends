// SPDX-License-Identifier: GPL-2.0-or-later
#ifndef LEGENDS_ENGINE_HOST_ENGINE_DISPATCHER_H
#define LEGENDS_ENGINE_HOST_ENGINE_DISPATCHER_H

#include <cstdint>
#include <expected>
#include <span>
#include <vector>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/message_types.h>

namespace legends::engine_host {

// Dispatch result: response message type + serialized payload.
struct DispatchResult {
    legends_ipc::MsgType response_type;
    std::vector<uint8_t> payload;
};

// Dispatch an incoming IPC message to the corresponding legends_*() function.
// Returns the response message type and serialized payload.
std::expected<DispatchResult, legends_ipc::IpcError>
dispatch(legends_ipc::MsgType msg_type, std::span<const uint8_t> payload);

} // namespace legends::engine_host

#endif // LEGENDS_ENGINE_HOST_ENGINE_DISPATCHER_H
