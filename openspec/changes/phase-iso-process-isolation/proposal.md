# Phase ISO: GPL v2 Process Isolation

## Problem

Project Legends currently links DOSBox-X engine code (GPL v2) monolithically into the application shell. This means the entire binary must be distributed under GPL v2, preventing proprietary distribution of the shell.

## Proposed Solution

Separate GPL code into a child process (`legends_engine_host`) communicating with the application shell via IPC. The shell links only MIT-licensed libraries (`legends_proxy`, `legends_ipc`), containing zero GPL object code.

## New Capabilities

1. **wire-format**: MIT-licensed wire serialization for IPC messages (REQ-ISO-003, REQ-ISO-004)
2. **shared-memory**: Double-buffered framebuffer and lock-free audio ring via shared memory (REQ-ISO-007, REQ-ISO-008)
3. **control-channel**: Named pipe control channel for request-response messaging (REQ-ISO-009)
4. **engine-host**: GPL-licensed engine host executable (REQ-ISO-005, REQ-ISO-006)
5. **proxy-library**: MIT-licensed proxy implementing legends_embed.h over IPC (REQ-ISO-010, REQ-ISO-011)
6. **process-lifecycle**: Engine process spawning and management (REQ-ISO-012, REQ-ISO-013)
7. **platform-support**: Windows and POSIX platform implementations (REQ-ISO-015)
8. **verification**: Linker scan and performance benchmarks (REQ-ISO-014, REQ-ISO-016)

## Impacted Files

- `include/legends_ipc/` — new MIT headers
- `src/legends_ipc/` — new MIT implementation
- `src/engine_host/` — engine host executable
- `src/legends_proxy/` — proxy library
- `CMakeLists.txt` — build targets and backend switch
- `cmake/ModuleManifest.cmake` — DAG entries
