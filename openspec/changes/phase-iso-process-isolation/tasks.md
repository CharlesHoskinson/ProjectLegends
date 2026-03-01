# Phase ISO: Process Isolation Tasks

## Sprint 1: MIT Wire Format + Message Catalog
- [x] 1.1 Create `include/legends_ipc/wire_format.h` (MIT LE helpers)
- [x] 1.2 Create `include/legends_ipc/ipc_error.h` (error enum)
- [x] 1.3 Create `include/legends_ipc/message_types.h` (47 API function pairs)
- [x] 1.4 Create `include/legends_ipc/message_header.h` (10-byte header)
- [x] 1.5 Create `include/legends_ipc/messages.h` + `src/legends_ipc/messages.cpp`
- [x] 1.6 Tests: `test_ipc_wire_format.cpp`, `test_ipc_message_header.cpp`, `test_ipc_messages.cpp`
- [x] 1.7 Update CMakeLists.txt: sources + gsl-lite dep

## Sprint 2: Message Codec + Protocol Spec
- [x] 2.1 Create `include/legends_ipc/message_codec.h` + `src/legends_ipc/message_codec.cpp`
- [x] 2.2 Test: `test_ipc_message_codec.cpp`
- [x] 2.3 Create `docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md`
- [x] 2.4 Create OpenSpec documents (proposal, design, tasks, wire-format spec)

## Sprint 3: Shared Memory Primitives
- [ ] 3.1 Create `include/legends_ipc/shared_memory.h`
- [ ] 3.2 Create `include/legends_ipc/framebuffer_shm.h` + cpp
- [ ] 3.3 Create `include/legends_ipc/audio_ring.h` + cpp
- [ ] 3.4 Platform: `shared_memory_win.cpp`, `shared_memory_posix.cpp`
- [ ] 3.5 Tests: shared memory, framebuffer, audio ring
- [ ] 3.6 OpenSpec: shared-memory spec

## Sprint 4: Named Pipe Control Channel
- [ ] 4.1 Create `include/legends_ipc/control_channel.h` + cpp
- [ ] 4.2 Platform: `control_channel_win.cpp`, `control_channel_posix.cpp`
- [ ] 4.3 Test: `test_ipc_control_channel.cpp`
- [ ] 4.4 OpenSpec: control-channel spec, platform-support spec

## Sprint 5: Engine Host Executable
- [ ] 5.1 Replace `src/engine_host/main.cpp` stub
- [ ] 5.2 Create `engine_dispatcher.h/.cpp`, `cli_parser.h/.cpp`, `version_info.cpp`
- [ ] 5.3 Tests: `test_engine_dispatcher.cpp`, `test_engine_host_cli.cpp`
- [ ] 5.4 OpenSpec: engine-host spec

## Sprint 6: Proxy Library + Backend Switch
- [ ] 6.1 Replace `src/legends_proxy/proxy_api.cpp` stub
- [ ] 6.2 Create `proxy_connection.h/.cpp`, `ipc_error_mapping.h`
- [ ] 6.3 Backend switch in CMakeLists.txt
- [ ] 6.4 Tests: `test_proxy_api.cpp`, `test_proxy_connection.cpp`
- [ ] 6.5 OpenSpec: proxy-library spec

## Sprint 7: Process Spawning + Integration
- [ ] 7.1 Create `include/legends_ipc/engine_spawner.h` + platform impls
- [ ] 7.2 Update proxy_connection for auto-spawn
- [ ] 7.3 Tests: spawner + integration
- [ ] 7.4 OpenSpec: process-lifecycle spec

## Sprint 8: Crash Recovery + Performance + Verification
- [ ] 8.1 Create crash_handler + heartbeat
- [ ] 8.2 Benchmark: `bench_ipc_overhead.cpp`
- [ ] 8.3 Linker verification: `verify_gpl_isolation.py` + CMake integration
- [ ] 8.4 Tests: crash handler, heartbeat, linker verification
- [ ] 8.5 OpenSpec: verification spec
