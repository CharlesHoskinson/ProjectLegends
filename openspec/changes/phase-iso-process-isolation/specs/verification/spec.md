# Verification Specification

**Phase**: Process Isolation
**Requirements**: REQ-ISO-014, REQ-ISO-016

## Overview

This specification defines the verification mechanisms that ensure the GPL
process isolation layer is working correctly: crash recovery handles engine
failures, performance meets budget, and the linker proves the shell binary
contains zero GPL object code.

## REQ-ISO-014: Crash Recovery

### Crash Handler

The `CrashHandler` class monitors the engine host process and fires a callback
when the process unexpectedly terminates.

**Behavior**:
- Polls `EngineProcess::is_alive()` every 200ms
- On death detection: invokes the registered `CrashCallback`
- Callback fires at most once per monitoring session
- `stop()` joins the monitor thread cleanly
- `restart()` spawns a new engine host using `EngineSpawner::spawn()`

### Heartbeat Monitor

The `HeartbeatMonitor` provides application-level liveness detection via the
IPC control channel.

**Behavior**:
- Sends `Heartbeat` message every `interval` (default 1s)
- Expects `HeartbeatAck` within `timeout` (default 5s)
- If ack not received: fires `TimeoutCallback` and stops
- `ack_received()` clears the pending flag
- Thread-safe: all shared state uses `std::atomic`

### Recovery Flow

1. Heartbeat timeout or crash detected
2. Callback notifies proxy
3. Proxy requests `SaveState` from last known good state (cached)
4. Proxy calls `CrashHandler::restart()` with `SpawnConfig`
5. New engine connects, receives `LoadState` with cached buffer
6. Emulation resumes

## REQ-ISO-016: Performance Budget

### Budget

Total IPC overhead must be < 0.83 ms per frame (5% of 16.6 ms at 60 FPS).

### Benchmarks

The `bench_ipc_overhead.cpp` file uses Google Benchmark to measure:

| Benchmark | Measures | Budget Share |
|-----------|----------|--------------|
| `BM_CodecRoundTrip` | MessageCodec encode + decode | < 0.1 ms |
| `BM_FramebufferFlipRead` | Shared memory write + atomic flip + read | < 0.3 ms |
| `BM_AudioPushPop` | SPSC ring push + pop (2048 frames) | < 0.1 ms |
| `BM_StepMsRespSerialize` | Message serialize + deserialize | < 0.05 ms |

### Running

```bash
./build-ipc/benchmarks/legends_ipc_benchmarks --benchmark_min_time=5
```

## REQ-ISO-016: Linker Verification

### verify_gpl_isolation.py

Python script that scans linker map files for GPL symbols.

**GPL patterns** (must NOT appear in shell binary):
- `aibox_core`, `legends_core`, `dosbox` object files
- `DOSBox_`, `CPU_Core_`, `GFX_`, `RENDER_`, `MIXER_` symbol prefixes
- `DOS_`, `BIOS_`, `IO_`, `PIC_`, `DMA_`, `INT10_` hardware symbols
- `legends_engine_host`, `engine_dispatcher` engine-side code

**Allowlist** (MIT-licensed, expected in shell):
- `legends_ipc`, `legends_proxy`, `legends_pal`
- IPC classes: `MessageCodec`, `ControlChannel`, `SharedMemory`, etc.

**Exit codes**:
- `0`: No GPL symbols found (PASS)
- `1`: GPL symbols detected (FAIL)
- `2`: File not found or other error

### VerifyGPLIsolation.cmake

CMake module that:
1. Enables linker map generation (`/MAP` for MSVC, `-Wl,-Map` for GCC/Clang)
2. Adds a post-build step running `verify_gpl_isolation.py`
3. Only active when `LEGENDS_USE_IPC=ON`

### Integration

```cmake
# In CMakeLists.txt, after project_legends target:
if(LEGENDS_USE_IPC)
    include(VerifyGPLIsolation)
endif()
```

## Test Matrix

| Test | Requirement | Method |
|------|------------|--------|
| Engine dies -> callback fires | REQ-ISO-014 | test_crash_handler.cpp |
| Heartbeat ack prevents timeout | REQ-ISO-014 | test_heartbeat.cpp |
| Missing ack triggers timeout | REQ-ISO-014 | test_heartbeat.cpp |
| Restart with valid config | REQ-ISO-014 | test_crash_handler.cpp |
| IPC overhead < 0.83ms | REQ-ISO-016 | bench_ipc_overhead.cpp |
| Clean map passes | REQ-ISO-016 | test_verify_gpl_isolation.py |
| GPL map fails | REQ-ISO-016 | test_verify_gpl_isolation.py |
| Nonexistent file errors | REQ-ISO-016 | test_verify_gpl_isolation.py |

## Acceptance Criteria

- [ ] Crash handler detects process death within 1 second
- [ ] Heartbeat timeout fires within configured timeout window
- [ ] Restart spawns new engine and returns true
- [ ] All benchmarks run without assertion failures
- [ ] P95 total IPC overhead < 0.83ms at 60 FPS
- [ ] `verify_gpl_isolation.py` exits 0 on clean IPC build
- [ ] `verify_gpl_isolation.py` exits 1 on monolithic build map
- [ ] Post-build verification runs automatically with `LEGENDS_USE_IPC=ON`
