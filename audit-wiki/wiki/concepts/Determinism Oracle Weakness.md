---
type: concept
aliases: ["Weak state hash", "H7", "conc-07"]
tags: [concept, type/concept, topic/audit, topic/determinism]
created: 2026-06-09
updated: 2026-06-09
status: draft
parent: [[overview]]
related:
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Project Legends Test Suite]]"
sources:
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
claims_status: supported
---

# Determinism Oracle Weakness

## Definition

Project Legends sells deterministic execution, and its determinism and save/load tests compare state hashes. But the Fast-mode hash those tests use excludes CPU registers, guest RAM, and VRAM — so the oracle passes executions that actually diverge. The product's central claim is verified by an instrument that cannot see most violations of it.

## Claims

- The Fast-mode CPU hash covers no architectural register state.^[from [[Concurrency & Determinism Audit (2026-06)]] — "no GPRs, no EIP, no EFLAGS, no segment registers"]
- The auditor's summary judgment of the verification instrument: the oracle is weak.^[from [[Concurrency & Determinism Audit (2026-06)]] — "the oracle is weak"]
- Every determinism and roundtrip test asserts on a hash that omits guest RAM.^[from [[Test Coverage Audit (2026-06)]] — "Fast-mode state hash, which excludes guest RAM"]
- A load that corrupted memory would still pass the roundtrip tests.^[from [[Test Coverage Audit (2026-06)]] — "a save/load that corrupted RAM would still roundtrip"]
- Progress exists: Full mode now hashes conventional memory.^[from [[Backlog Verification Audit (2026-06)]] — "now hashes full conventional memory"]
- But Full mode has no callers in production or tests.^[from [[Test Coverage Audit (2026-06)]] — "now hashes guest RAM in Full mode"]
- VGA and device coverage is deferred by comment to Phase B.^[from [[Backlog Verification Audit (2026-06)]] — "VGA and device state will be added in Phase B"]
- The header contract still promises more than the implementation delivers (prior H7, open).^[from [[Backlog Verification Audit (2026-06)]] — "Contract still overstates by VGA + devices"]
- The test architecture itself is sound — two-instance identity, midpoint save/load, replay traces.^[from [[Concurrency & Determinism Audit (2026-06)]] — "Test design is right-shaped: two-instance hash identity"]

## Related

- [[Vacuous Interrupt Delivery (C2)]] — the weak oracle is why a vacuous fix could pass determinism CI
- [[Project Legends Test Suite]] — where the oracle is consumed
- [[Sprint Plan Derivation (2026-06)]] — Sprint 2 ("trustworthy oracles" precedes engine-time work)
