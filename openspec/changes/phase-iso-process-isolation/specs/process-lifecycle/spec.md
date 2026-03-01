# Process Lifecycle Specification

Requirement: REQ-ISO-012, REQ-ISO-013

## REQ-ISO-012: Engine Process Spawning

### Scenario: Spawn engine host

Given a valid path to `legends_engine_host`
When `EngineSpawner::spawn()` is called with pipe and shm names
Then a child process is started with `--pipe` and `--shm` arguments
And `is_alive()` returns true while the process runs

### Scenario: Nonexistent executable

Given an invalid executable path
When `EngineSpawner::spawn()` is called
Then it returns `IpcError::SpawnFailed`

### Scenario: Auto-spawn on first create

Given `ProxyConnection` is not connected
When `legends_create()` is called through the proxy
Then the proxy generates a pipe name from PID
And creates shared memory regions and named pipe server
And spawns `legends_engine_host`
And waits for the handshake

## REQ-ISO-013: Crash Recovery

### Scenario: Engine process dies unexpectedly

Given a connected engine host process
When the engine process terminates unexpectedly
Then the crash handler callback fires within 1 second
And the proxy can restart the engine with cached autosave state
