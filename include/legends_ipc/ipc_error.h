// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_ERROR_H
#define LEGENDS_IPC_ERROR_H

#include <cstdint>

namespace legends_ipc {

enum class IpcError : uint8_t {
    Ok                = 0,
    BufferTooSmall    = 1,
    InvalidHeader     = 2,
    UnknownMessage    = 3,
    DeserializeFailed = 4,
    NotConnected      = 5,
    Timeout           = 6,
    BrokenPipe        = 7,
    SpawnFailed       = 8,
    HandshakeFailed   = 9,
    EngineError       = 10,
    OutOfMemory       = 11,
    InvalidArgument   = 12,
    AlreadyConnected  = 13,
    VersionMismatch   = 14,
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_ERROR_H
