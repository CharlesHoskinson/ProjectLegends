// SPDX-License-Identifier: MIT
#ifndef LEGENDS_PROXY_IPC_ERROR_MAPPING_H
#define LEGENDS_PROXY_IPC_ERROR_MAPPING_H

#include <legends_ipc/ipc_error.h>
#include <legends/legends_embed.h>

namespace legends_proxy {

inline legends_error_t map_ipc_error(legends_ipc::IpcError err) {
    switch (err) {
    case legends_ipc::IpcError::Ok:              return LEGENDS_OK;
    case legends_ipc::IpcError::BufferTooSmall:  return LEGENDS_ERR_BUFFER_TOO_SMALL;
    case legends_ipc::IpcError::NotConnected:    return LEGENDS_ERR_NOT_INITIALIZED;
    case legends_ipc::IpcError::Timeout:         return LEGENDS_ERR_IO_FAILED;
    case legends_ipc::IpcError::BrokenPipe:      return LEGENDS_ERR_IO_FAILED;
    case legends_ipc::IpcError::SpawnFailed:     return LEGENDS_ERR_INTERNAL;
    case legends_ipc::IpcError::EngineError:     return LEGENDS_ERR_INTERNAL;
    case legends_ipc::IpcError::OutOfMemory:     return LEGENDS_ERR_OUT_OF_MEMORY;
    case legends_ipc::IpcError::InvalidArgument: return LEGENDS_ERR_INVALID_CONFIG;
    case legends_ipc::IpcError::VersionMismatch: return LEGENDS_ERR_VERSION_MISMATCH;
    default:                                     return LEGENDS_ERR_INTERNAL;
    }
}

} // namespace legends_proxy

#endif // LEGENDS_PROXY_IPC_ERROR_MAPPING_H
