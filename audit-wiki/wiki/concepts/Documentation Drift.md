---
type: concept
aliases: ["Doc drift", "Stale records"]
tags: [concept, type/concept, topic/audit, topic/docs]
created: 2026-06-09
updated: 2026-06-09
status: draft
parent: [[overview]]
related:
  - "[[Project Legends Documentation Corpus]]"
  - "[[Prior-Audit Remediation Status]]"
  - "[[Licensing Inconsistency]]"
sources:
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
claims_status: supported
---

# Documentation Drift

## Definition

The project's documents of record (roadmap, TODO, CHANGELOG, README, REQUIREMENTS, conformance docs) have drifted from the code in both directions — claiming things that don't exist (Wasm, TLS) while failing to record real progress (22 resolved findings, fixed TLA invariants). Every auditor independently hit this; it is the audit's most universal theme and it actively corrupts planning.

## Claims

- The March source-verified roadmap was overwritten in June by a stale-stamped 4,061-line document.^[from [[Backlog Verification Audit (2026-06)]] — "was clobbered back to a 4,061-line document in June"]
- CHANGELOG claims TLS verification, but no HTTP/TLS transport exists anywhere in the code.^[from [[Backlog Verification Audit (2026-06)]] — "no HTTP/TLS transport exists anywhere"]
- TODO.md is 3.5 months stale and internally contradictory.^[from [[Backlog Verification Audit (2026-06)]] — "TODO.md is 3.5 months stale and internally contradictory"]
- README advertises a Wasm sandbox whose referenced artifacts have never existed in git history.^[from [[Docs & Licensing Audit (2026-06)]] — "have never existed in git history"]
- The Wasm capability bullet is the doc set's clearest truthfulness defect.^[from [[Docs & Licensing Audit (2026-06)]] — "the clearest truthfulness defect in the doc set"]
- TODO.md marks the same requirement IDs both complete and missing.^[from [[Docs & Licensing Audit (2026-06)]] — "TODO.md contradicts itself and reality"]
- RELEASING.md asserts CI behavior that the June 8 demotion removed.^[from [[Build & CI Audit (2026-06)]] — "asserts CI behavior that no longer exists"]
- The roadmap marks dependency scanning Done while the scanner invocation can never produce a finding.^[from [[Build & CI Audit (2026-06)]] — "a green checkbox backed by a command"]
- README and ARCHITECTURE present IPC mode as a working build mode while it cannot boot.^[from [[API & Architecture Audit (2026-06)]] — "present IPC mode as a working build mode"]
- TLA+ conformance claims are stale in both directions: real fixes unrecorded, real gaps still advertised as conformant.^[from [[Concurrency & Determinism Audit (2026-06)]] — "stated conformance (33/49) is stale in both directions"]
- The README test badge is hardcoded markup, not CI output.^[from [[Test Coverage Audit (2026-06)]] — "a hardcoded static badge linking to nothing"]
- On IPC, the paper trail understates the code while overstating the guarantees.^[from [[Security Audit (2026-06)]] — "understates the code while overstating the guarantees"]

> [!check] SUBSTANTIALLY RESOLVED 2026-06-10 (Sprint 1)
> Fixed on branch `sprint-1/truthful-record` (audited PASS 8/8): roadmap case collision eliminated and stamp corrected; TODO/AUDIT/CHANGELOG reconciled (6 contradictions, IPC label, 22/8 tally, accurate TLS scope); Wasm demoted to planned with git-history proof; REQUIREMENTS + TLA conformance re-baselined with `verified-at` stamps; README API/error tables generated; ARCHITECTURE constants fixed; three new CI guard scripts added. Residual drift will be caught mechanically by the new checks. Provenance: [[Sprint 1 Implementation Audit (2026-06-10)]].

## Related

- [[Project Legends Documentation Corpus]] — the entity this concept describes the failure mode of
- [[Prior-Audit Remediation Status]] — drift hides 22 real resolutions
- [[Sprint 1 Implementation Audit (2026-06-10)]] — the remediation and its audit
- [[Sprint Plan Derivation (2026-06)]] — Sprint 1 ("truthful record")
