## Why

The RuntimeHost proxy parity sprint proved that implementation workers can quickly add broad proxy coverage, but they miss ABI edge cases unless the contract is explicit and testable. Codex had to fix null-handle behavior, required output pointer checks, initialized default structs, and two-call size-query behavior after implementation.

## What Changes

Add a machine-readable ABI parity gate that records the negative and boundary cases required for public `legends_*` APIs, then add focused tests for the newly proxied RuntimeHost surface.

The sprint should cover at least:

- Null handle behavior.
- Null required output pointer behavior.
- Query/fill two-call buffer behavior.
- Undersized output buffer behavior.
- Initialized default output structs.
- Direct/proxy return-code parity where the proxy can be exercised locally.

## Scope

In scope:

- A dependency-free manifest and checker under `docs/architecture` and `scripts`.
- Focused unit tests for RuntimeHost/proxy-facing APIs.
- CI wiring through the existing fast quality gate.
- QA reporting that lists every covered API and any explicitly deferred case.

Out of scope:

- Implementing callback streaming.
- Implementing video capture or TTF proxy support.
- Rewriting the public C ABI.

## Audit Strategy

Codex will audit the checker logic, the manifest coverage, and the tests for failure-mode assertions rather than only success-path assertions.
