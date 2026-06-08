## Why

The proxy parity implementation added broad IPC message coverage, but Codex had to harden malformed dynamic payload handling afterward. IPC messages with declared sizes, trailing payloads, typed arrays, and two-call buffers need adversarial tests as a standing requirement.

## What Changes

Add a focused hostile-payload test layer for IPC wire messages and dispatcher allocation behavior.

The sprint should cover:

- Truncated payloads.
- Oversized payloads.
- Declared size smaller or larger than actual payload.
- Odd byte count for typed arrays.
- Dispatcher query-before-allocation behavior for capture requests.
- Error-code expectations for malformed requests.

## Scope

In scope:

- Unit tests under `tests/unit/test_ipc_messages.cpp`.
- Dispatcher tests under `tests/unit/test_engine_dispatcher.cpp`.
- Optional dependency-free helper builders for malformed payload construction.
- A short architecture note explaining dynamic IPC safety rules.

Out of scope:

- Network fuzzing.
- Long-running randomized fuzz tests in required CI.
- Replacing the IPC protocol.

## Audit Strategy

Codex will audit that each dynamic message family has at least one malformed-input test and that dispatcher tests prove hostile counts do not cause large allocations.
