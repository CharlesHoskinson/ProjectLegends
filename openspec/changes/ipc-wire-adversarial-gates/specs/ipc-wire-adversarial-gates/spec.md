## ADDED Requirements

### Requirement: Dynamic IPC Payload Rejection
Dynamic IPC message deserializers SHALL reject malformed payloads.

#### Scenario: Payload is truncated
- **GIVEN** a dynamic IPC payload declares more bytes than are present
- **WHEN** the message is deserialized
- **THEN** deserialization SHALL fail with an IPC error

#### Scenario: Payload is oversized
- **GIVEN** a dynamic IPC payload contains more typed elements than the declared count permits
- **WHEN** the message is deserialized
- **THEN** deserialization SHALL fail with an IPC error

#### Scenario: Typed payload has odd byte count
- **GIVEN** a typed payload stores fixed-width cells or samples
- **WHEN** the payload length is not divisible by the element size
- **THEN** deserialization SHALL fail with an IPC error

### Requirement: Dispatcher Allocation Safety
Dispatcher handlers SHALL query required output sizes before allocating variable-size response storage.

#### Scenario: Caller count is hostile
- **GIVEN** a capture request includes a very large caller-provided count
- **WHEN** the dispatcher handles the request
- **THEN** the dispatcher SHALL call the direct API in query mode first
- **AND** SHALL NOT allocate storage based only on the caller-provided count

#### Scenario: Caller count is too small
- **GIVEN** the direct API reports a required output count larger than the caller-provided count
- **WHEN** the dispatcher handles the request
- **THEN** the dispatcher SHALL return `LEGENDS_ERR_BUFFER_TOO_SMALL`
- **AND** SHALL include the required count in the response
