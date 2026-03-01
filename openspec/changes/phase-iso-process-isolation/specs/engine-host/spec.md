# Engine Host Specification

Requirements: REQ-ISO-005, REQ-ISO-006

## REQ-ISO-005: Engine Host Executable

### Scenario: CLI argument parsing

Given `legends_engine_host` is invoked with `--pipe <name> --shm <name>`
Then the engine connects to the named pipe and opens shared memory
And enters the message dispatch loop

### Scenario: Version flag

Given `legends_engine_host --version`
Then it prints the engine version and GPL v2 license notice
And exits with code 0

### Scenario: Missing required arguments

Given `legends_engine_host` is invoked without `--pipe`
Then it prints an error message and exits with code 1

## REQ-ISO-006: Message Dispatch

### Scenario: Request dispatch to legends_*() functions

Given a connected engine host
When a `CreateReq` message arrives on the control channel
Then the dispatcher calls `legends_create()` with the config from the message
And sends a `CreateResp` with the error code

### Scenario: Unknown message type

Given a message with an unrecognized type
When dispatched
Then the engine returns an `ErrorResponse` with `LEGENDS_ERR_NOT_SUPPORTED`

### Scenario: Shutdown sequence

Given a running engine host with an active instance
When a `Shutdown` message is received
Then `legends_destroy()` is called
And a `ShutdownAck` is sent
And the process exits cleanly
