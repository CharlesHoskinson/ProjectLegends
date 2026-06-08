## ADDED Requirements

### Requirement: Core RuntimeHost Proxy APIs
The IPC proxy SHALL support `legends_get_config`, `legends_capture_text`, `legends_save_state`, `legends_load_state`, `legends_verify_determinism`, and `legends_get_last_error`.

#### Scenario: Proxy forwards core requests
- **GIVEN** a proxy client is connected to an engine host with a created engine
- **WHEN** one of the core APIs is invoked
- **THEN** the proxy SHALL send a typed IPC request
- **AND** the engine dispatcher SHALL call the corresponding direct `legends_*` function
- **AND** the API SHALL NOT return `LEGENDS_ERR_NOT_SUPPORTED` from the proxy body

### Requirement: Two-Call Buffer Semantics
The proxy SHALL preserve the public C ABI two-call pattern for variable-size outputs.

#### Scenario: Query then fill
- **GIVEN** a caller invokes text capture, save state, or last-error retrieval with a null output buffer
- **WHEN** the engine host returns the required count, byte size, or string length
- **THEN** the proxy SHALL write that value to the caller's out parameter and return `LEGENDS_OK`
- **AND** a later call with a sufficient buffer SHALL copy the returned payload

#### Scenario: Too-small caller buffer
- **GIVEN** a caller provides an output buffer smaller than the required payload
- **WHEN** the proxy receives the engine response
- **THEN** the proxy SHALL return `LEGENDS_ERR_BUFFER_TOO_SMALL`
- **AND** SHALL write the required count, byte size, or string length to the caller's out parameter

### Requirement: Variable Payload Safety
Variable-size IPC payloads SHALL be length-prefixed and bounds-checked.

#### Scenario: Payload decode
- **GIVEN** a response or request contains trailing payload bytes
- **WHEN** deserialization reads the fixed header
- **THEN** it SHALL validate that the declared payload length fits inside the received buffer
- **AND** SHALL fail with `IpcError::BufferTooSmall` or an existing equivalent IPC error when the buffer is truncated
