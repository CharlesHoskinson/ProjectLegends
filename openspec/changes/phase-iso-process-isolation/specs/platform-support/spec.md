# Platform Support Specification

Requirement: REQ-ISO-015

## REQ-ISO-015: Cross-Platform IPC

### Scenario: Windows named pipe implementation

Given `PLATFORM_ID` is Windows
When `ControlChannel::create_server()` is called
Then the underlying transport uses `CreateNamedPipeW` / overlapped I/O
And the pipe name follows the pattern `\\.\pipe\legends_<pid>`

### Scenario: POSIX Unix domain socket implementation

Given `PLATFORM_ID` is not Windows
When `ControlChannel::create_server()` is called
Then the underlying transport uses Unix domain sockets
And the socket path follows the pattern `/tmp/legends_<pid>.sock`

### Scenario: Platform-specific shared memory

Given `PLATFORM_ID` is Windows
When `SharedMemoryRegion::create()` is called
Then it uses `CreateFileMappingW` / `MapViewOfFile`

Given `PLATFORM_ID` is not Windows
When `SharedMemoryRegion::create()` is called
Then it uses `shm_open` / `mmap`

### Scenario: No #ifdef in protocol headers

Given the protocol and serialization headers in `include/legends_ipc/`
Then no file contains `#ifdef _WIN32` or platform-specific `#if` directives
And all platform variance is isolated to `src/legends_ipc/platform/`
