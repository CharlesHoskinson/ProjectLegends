# Phase ISO: Process Isolation Design

Status: IN PROGRESS

## Architecture

Two-process model with three IPC channels:
- Control channel: named pipe for request-response
- Framebuffer: shared memory, double-buffered, atomic flip
- Audio: shared memory, lock-free SPSC ring buffer

## Key Decisions

1. MIT wire format is independently written, not derived from GPL `dosbox::wire`
2. 10-byte message header: msg_type(2) + payload_size(4) + sequence_id(4)
3. Shared memory sizes negotiated at handshake
4. IPC library uses `gsl_lite::` directly (not `legends::gsl::` which is GPL-layer)
5. Proxy mirrors function signatures exactly for linker-level backend switch
6. Crash recovery uses locally cached autosave buffer

## Wire Protocol

See `docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md` for full specification.

## Build Configuration

```cmake
if(LEGENDS_USE_IPC)
    target_link_libraries(project_legends PRIVATE legends_proxy legends_pal)
else()
    target_link_libraries(project_legends PRIVATE legends_core legends_pal)
endif()
```

## Performance Budget

IPC overhead < 0.83 ms/frame (5% of 16.6 ms at 60 FPS).
