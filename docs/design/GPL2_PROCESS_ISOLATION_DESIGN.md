# GPL v2 Process Isolation Design

## Overview

Project Legends embeds a GPL-licensed DOSBox-X engine (`aibox_core`) in a proprietary application shell. This design separates all GPL code into a child process communicating via IPC, so the shell binary contains zero GPL object code.

## Architecture

```
project_legends (non-GPL) --> legends_proxy (MIT) --> legends_ipc (MIT)
                          --> legends_pal

legends_engine_host (GPL) --> legends_core (GPL) --> aibox_core (GPL)
                          --> legends_ipc (MIT)
```

The application shell links only MIT-licensed libraries. The GPL engine runs in a separate process (`legends_engine_host`) and communicates via three IPC channels.

## IPC Channels

### Control Channel (Named Pipe)
- **Windows**: `\\.\pipe\legends_<pid>`
- **POSIX**: Unix domain socket at `/tmp/legends_<pid>.sock`
- Bidirectional request/response carrying serialized messages
- Message framing: 10-byte header + variable payload

### Framebuffer (Shared Memory)
- Double-buffered RGBA32 framebuffer
- Atomic frame index for lock-free flip
- Default: 2 x (1920 x 1080 x 4) = ~16 MB

### Audio Ring (Shared Memory)
- Lock-free SPSC ring buffer
- S16LE stereo @ 44100 Hz
- Default: 2048 frames (~16 KB)

## Wire Protocol

### Message Header (10 bytes)
| Offset | Size | Field | Description |
|--------|------|-------|-------------|
| 0 | 2 | msg_type | `MsgType` enum (LE) |
| 2 | 4 | payload_size | Payload byte count (LE) |
| 6 | 4 | sequence_id | Request-response matching (LE) |

All multi-byte fields are little-endian. The wire format uses byte-shift serialization for portability.

### Message Catalog

Control messages (0x00xx): Handshake, Shutdown, Heartbeat, ErrorResponse.

API messages (0x01xx+): Each `legends_embed.h` function maps to a request/response pair. See `include/legends_ipc/message_types.h` for the full catalog.

### Handshake Sequence
1. Shell creates named pipe server + shared memory regions
2. Shell spawns `legends_engine_host --pipe <name> --shm <name>`
3. Engine connects to pipe, opens shared memory
4. Engine sends `HandshakeAck` with protocol version and engine version
5. Shell validates version compatibility

### Request-Response Flow
1. Shell serializes request message, writes header+payload to pipe
2. Engine reads header, reads payload, dispatches to `legends_*()` function
3. Engine writes framebuffer to shared memory, audio to ring buffer
4. Engine serializes response, writes header+payload to pipe
5. Shell reads response, matches by sequence_id

## Shared Memory Layouts

### Framebuffer
```
Offset  Type             Field
0       u32              max_width
4       u32              max_height
8       atomic<u64>      frame_index
16      atomic<u32>      active_buffer (0 or 1)
20      u32              current_width
24      u32              current_height
28      u32              padding
32      u8[buf_size]     buffer_0
32+bs   u8[buf_size]     buffer_1
```
Where `buf_size = max_width * max_height * 4`.

### Audio Ring
```
Offset  Type             Field
0       u32              capacity_frames
4       u32              channels
8       u32              sample_rate
12      u32              padding
16      atomic<u32>      write_index
20      atomic<u32>      read_index
24      u8[8]            padding
32      i16[cap*ch]      samples
```

## Performance Budget

IPC overhead must be < 0.83 ms/frame (5% of 16.6 ms at 60 FPS).

## Crash Recovery

- Proxy sends `Heartbeat` every 1s, expects `HeartbeatAck` within 5s
- On engine death: callback fires, proxy can `restart()` with cached autosave
- `SaveState` periodically cached in proxy for fast recovery

## Linker Verification

Post-build step reads linker map file and fails if any GPL symbols appear in the shell binary.
