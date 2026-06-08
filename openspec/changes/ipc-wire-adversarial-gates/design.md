## Design

Create a small, explicit malformed-payload corpus in unit tests rather than a heavyweight fuzzing dependency.

Dynamic message families to cover:

- Save-state request and response payloads.
- Load-state request payloads.
- Text capture typed cell payloads.
- MIDI capture typed sample payloads.
- String-backed requests such as text input, MIDI paths, printer output, IPX server, and capability name.

Dispatcher behavior should be verified for:

- Caller-provided count smaller than required output count.
- Very large caller-provided counts that must not drive allocation before the required-size query.
- Malformed dynamic payloads returning an IPC error response rather than invoking direct engine calls.

The tests may use local fake payload builders, but they must avoid brittle ad hoc byte offsets when an existing serializer can generate the valid prefix.

## CI

No new heavy CI job is required. These tests belong in the normal unit-test binary.
