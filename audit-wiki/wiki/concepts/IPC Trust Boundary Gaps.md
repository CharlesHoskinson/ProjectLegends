---
type: concept
aliases: ["IPC security gaps", "GPL trust boundary gaps"]
tags: [concept, type/concept, topic/audit, topic/security, topic/ipc]
created: 2026-06-09
updated: 2026-06-09
status: draft
parent: [[overview]]
related:
  - "[[IPC Runtime (Project Legends)]]"
  - "[[Licensing Inconsistency]]"
sources:
  - "[[Security Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
claims_status: supported
---

# IPC Trust Boundary Gaps

## Definition

The IPC layer (proxy ⇄ engine host) is the intended GPL-isolation and security boundary, by design the component that contains untrusted guest execution. The 2026-06 audit found it lacks the properties a trust boundary needs: peer authentication, response correlation, input fuzzing, and parity verification. (The reported shared-memory framebuffer-geometry OOB read, SEC-01, was refuted under adversarial verification and is excluded.)

## Claims

- IPC endpoints accept any same-privilege peer: no authentication, predictable names, default ACLs.^[from [[Security Audit (2026-06)]] — "no peer authentication and use predictable, world-reachable names"]
- The shell cannot verify it is talking to the engine host it spawned.^[from [[Security Audit (2026-06)]] — "the handshake carries no token"]
- One unsolicited or out-of-order message permanently desynchronizes the request/response stream.^[from [[Security Audit (2026-06)]] — "the entire request/response stream desynchronizes thereafter"]
- Uncorrelated responses let stale data be accepted as the next reply.^[from [[API & Architecture Audit (2026-06)]] — "garbage accepted as valid, stream desynchronized"]
- The GetStateHash handler serializes uninitialized stack memory across the process boundary.^[from [[API & Architecture Audit (2026-06)]] — "leaking up to 32 bytes of engine-host stack"]
- A shell/engine-host version mismatch is undetectable at create time because version data never crosses the boundary.^[from [[API & Architecture Audit (2026-06)]] — "talking to a 1.0 engine host is undetectable at create time"]
- The audio ring consumer trusts a capacity field read from shared memory without validation.^[from [[Concurrency & Determinism Audit (2026-06)]] — "trusts `header_->capacity_frames` from the shared region"]
- A zero or corrupted capacity value crashes the embedder.^[from [[Concurrency & Determinism Audit (2026-06)]] — "a divide-by-zero in the embedder process"]
- Only 8 of 43 dispatcher message handlers have direct tests, all happy-path.^[from [[Test Coverage Audit (2026-06)]] — "the dispatcher has direct tests for 8 of 43 message cases"]
- Nothing verifies the two runtimes agree, and the codec/dispatcher is never fuzzed.^[from [[Test Coverage Audit (2026-06)]] — "no in-process-vs-proxy parity suite and no IPC fuzz target"]
- The security auditor's conclusion: IPC mode is a functional transport but not a verifiable isolation boundary.^[from [[Security Audit (2026-06)]] — "not yet a trustworthy isolation boundary"]

## Related

- [[IPC Runtime (Project Legends)]] — the subsystem these gaps live in
- [[Licensing Inconsistency]] — GPL isolation is the reason this boundary exists
- [[Sprint Plan Derivation (2026-06)]] — Sprints 3 and 4
