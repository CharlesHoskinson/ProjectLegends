---
type: entity
entity_kind: system
aliases: ["legends_ipc", "legends_proxy", "engine_host"]
tags: [entity, type/entity, topic/audit, topic/ipc]
created: 2026-06-09
updated: 2026-06-09
status: draft
related:
  - "[[IPC Trust Boundary Gaps]]"
  - "[[Licensing Inconsistency]]"
sources:
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
---

# IPC Runtime (Project Legends)

## Overview

The out-of-process runtime: `src/legends_ipc` (108 message types, 89 structs), `src/legends_proxy` (MIT-side client), `src/engine_host` (GPL-side dispatcher, 43 cases). Built as the GPL-isolation boundary. Roughly 2,700 lines of real code that nonetheless cannot boot end-to-end: no production code establishes the connection, and the protocol, parity, and platform coverage all lag the in-process runtime.

## Facts

- IPC mode cannot actually run — no production path establishes the connection.^[from [[API & Architecture Audit (2026-06)]] — "IPC mode cannot actually run"]
- `ProxyConnection::connect()` is only called from tests.^[from [[API & Architecture Audit (2026-06)]] — "is only called from tests"]
- The two runtimes do not expose identical C ABI semantics.^[from [[API & Architecture Audit (2026-06)]] — "The two runtimes do not expose identical semantics"]
- Its message layer is the largest hand-rolled parser in the project.^[from [[Security Audit (2026-06)]] — "the largest hand-rolled parser in the project"]
- One receive timeout permanently desynchronizes the channel.^[from [[Concurrency & Determinism Audit (2026-06)]] — "one timeout permanently desynchronizes the channel"]
- The engine host never writes the shared-memory framebuffer, so IPC capture silently diverges from in-process behavior.^[from [[Concurrency & Determinism Audit (2026-06)]] — "silently diverging from in-process behavior"]
- The cross-process audio ring is not linearizable: both sides store the read index.^[from [[Concurrency & Determinism Audit (2026-06)]] — "the queue is not linearizable"]
- Six C ABI functions return NOT_SUPPORTED in IPC mode.^[from [[Backlog Verification Audit (2026-06)]] — "for 6 APIs in IPC mode"]
- The host and proxy are never built or tested on Windows.^[from [[Build & CI Audit (2026-06)]] — "never built or tested on Windows"]
- The only true cross-process E2E test is permanently disabled.^[from [[Test Coverage Audit (2026-06)]] — "Disabled tests never run under ctest"]
- Yet TODO.md's "STUB ONLY" label is stale-pessimistic — thousands of lines of real IPC/proxy/host code exist.^[from [[Docs & Licensing Audit (2026-06)]] — "lines of real IPC/proxy/host code exist"]

## Related

- [[IPC Trust Boundary Gaps]] — its security posture
- [[Licensing Inconsistency]] — the legal load this boundary is supposed to carry
- [[Legends C API Layer]] — the contract it must match
