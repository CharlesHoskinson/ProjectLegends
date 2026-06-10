---
type: map
aliases: ["Audit Overview MOC"]
tags: [moc, type/map, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
scope: End-to-end audit of Project Legends — findings, subsystem assessments, sprint planning
---

# Project Legends Audit Overview (MOC)

Root map for the 2026-06 end-to-end audit (8-role agent fleet, HEAD `ef11f20`). Verdict in one line: the code outran its instruments — see [[Audit Verdict (2026-06)]]; execution order in [[Sprint Plan Derivation (2026-06)]].

## Syntheses

- [[Audit Verdict (2026-06)]] — overall thesis, grades, and what was refuted
- [[Sprint Plan Derivation (2026-06)]] — the eight-sprint program and its rationale

## Remediation audits

- [[Sprint 0 Implementation Audit (2026-06-10)]] — GPT 5.5 Codex Sprint 0 verdict: PASS 5/5, no code defects (mem-01, lic-01, mem-02, CI gates, fuzzer)
- [[Sprint 1 Implementation Audit (2026-06-10)]] — Sprint 1 (Truthful Record) verdict: PASS 8/8, all three corrections honored; docs reconciled, CI guards added

## Sources

- [[Backlog Verification Audit (2026-06)]] — 22 of 30 prior findings verified resolved; record-keeping defects
- [[API & Architecture Audit (2026-06)]] — C ABI solid; IPC runtime cannot boot and diverges semantically
- [[Memory Safety Audit (2026-06)]] — prior backlog genuinely fixed; new critical load-path overflow
- [[Security Audit (2026-06)]] — save-state path hardened; IPC boundary lacks auth/fuzzing/verification
- [[Concurrency & Determinism Audit (2026-06)]] — C2 fix vacuous at link level; weak determinism hash
- [[Build & CI Audit (2026-06)]] — gates demoted; GPL enforcement orphaned; release pipeline never run
- [[Test Coverage Audit (2026-06)]] — broad suite, weak oracles, stub integration tests
- [[Docs & Licensing Audit (2026-06)]] — MIT root LICENSE over GPL code; Wasm claims; stale statuses

## Concepts

- [[Save-State Load Path Overflow]] — confirmed critical heap overflow (mem-01), contested vs security read
- [[IPC Trust Boundary Gaps]] — no auth, no correlation, no fuzzing on the GPL boundary
- [[Vacuous Interrupt Delivery (C2)]] — contested: PIC calls present but linked to a no-op stub
- [[Determinism Oracle Weakness]] — the hash can't see registers, RAM, or VRAM
- [[Quality Gate Demotion (2026-06-08)]] — sanitizers/fuzz/TLA+ pulled off the merge gate
- [[Licensing Inconsistency]] — critical LICENSE defect plus unenforced isolation
- [[Documentation Drift]] — records wrong in both directions, every auditor hit it
- [[Prior-Audit Remediation Status]] — 22/30 resolved, 8 open, none recorded

## Entities

- [[Legends C API Layer]] — strongest layer; joystick/reentrancy/doc soft spots
- [[IPC Runtime (Project Legends)]] — ~2,700 real lines that cannot boot end-to-end
- [[Engine Bridge (DOSBox-X)]] — hosts mem-01 and the C2 stub linkage
- [[Build & CI System (Project Legends)]] — broad machinery, unwired enforcement
- [[Project Legends Test Suite]] — wide but under-enforced, weak oracles
- [[Project Legends Documentation Corpus]] — two eras: verified-fresh vs drifted-stale
