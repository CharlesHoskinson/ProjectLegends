---
type: synthesis
aliases: ["Sprint derivation", "Audit sprint rationale"]
tags: [synthesis, type/synthesis, topic/audit, topic/planning]
created: 2026-06-09
updated: 2026-06-09
status: draft
question: What sequence of implementation sprints should follow the 2026-06 audit, and why that order?
sources:
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Memory Safety Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
concepts:
  - "[[Save-State Load Path Overflow]]"
  - "[[IPC Trust Boundary Gaps]]"
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Determinism Oracle Weakness]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Licensing Inconsistency]]"
  - "[[Documentation Drift]]"
confidence: moderate
---

# Sprint Plan Derivation (2026-06)

Eight sprints, ~12-14 team-weeks. Full executable plan: `docs/superpowers/plans/2026-06-09-audit-implementation-sprints.md` in the repo. Derivation logic below; severity/effort data comes from the eight fleet reports (see Sources), ordering is synthesis.

- **Sprint 0 — Stop the bleeding (1 wk).** The four items that are individually small but unbounded in downside: the [[Save-State Load Path Overflow]] (critical, S effort), the create-error-path leak that bricks the library, re-arming the merge gates reversed by the [[Quality Gate Demotion (2026-06-08)]], and rewriting the root LICENSE ([[Licensing Inconsistency]], critical, S). Rationale: every later sprint merges code; the gates must gate first, and known-exploitable/legal-critical items never wait.
- **Sprint 1 — Truthful record (1 wk).** [[Documentation Drift]] remediation: roadmap case-collision restore, TODO/AUDIT/CHANGELOG/REQUIREMENTS reconciliation, Wasm claim demotion, README API table generation, OpenSpec hygiene. Plus two decision gates (Wasm: spike or defer; GPL -only vs -or-later). Rationale: planning data is corrupt until the record is fixed; cheap, parallelizable with Sprint 0.
- **Sprint 2 — Trustworthy oracles (2 wks).** [[Determinism Oracle Weakness]]: registers + RAM/VRAM into the hash, Full-mode in determinism CI, implement the 8 stub integration tests, fuzzer CRC wall fix, coverage ratchet. Includes the C2 verification spike. Rationale: must precede engine-time work — you cannot safely modify what you cannot measure.
- **Sprint 3 — IPC made real (2 wks).** Boot path, version handshake, sequence-ID correlation, SPSC ring fix, SHM producers, runtime parity suite ([[IPC Trust Boundary Gaps]], api-01..04). Rationale: largest functional gap; precedes hardening because you harden what runs.
- **Sprint 4 — Trust boundary hardening (1.5 wks).** Peer auth, SHM field validation, IPC fuzzers, stack-leak fix, load atomicity. Rationale: converts the now-running boundary into a defensible one.
- **Sprint 5 — GPL isolation enforceable (1 wk).** Wire VerifyGPLIsolation + DAG coverage + symbol firewall into CI, Windows IPC job, header-licensing decision ([[Licensing Inconsistency]]). Rationale: the legal promise becomes mechanical only after Sprints 3-4 give it something real to verify.
- **Sprint 6 — Make time real (3-4 wks, XL).** [[Vacuous Interrupt Delivery (C2)]]: deterministic PIC/PIT queue in library mode, per-ms execute_cycles slices, scheduler-queue serialization, TLA re-baseline. Rationale: deepest engineering risk, deliberately late — it lands on top of trustworthy oracles (Sprint 2) and re-armed gates (Sprint 0).
- **Sprint 7 — Debt burn-down & release dry run (1.5 wks).** Dead-path deletion (H3/H4/M5/M10/L3), TSan green, supply-chain pinning, ccache, first-ever release-pipeline execution via an rc tag. Rationale: close the audit cycle and prove the ship process before v1.0 pressure.

Dependency spine: 0 → (1 ∥ 2) → 3 → 4 → 5 → 7, with 6 gated on 2 and runnable parallel to 4-5 if staffing allows. Re-audit checkpoint after Sprint 5.

## Sources

- "[[Backlog Verification Audit (2026-06)]]"
- "[[API & Architecture Audit (2026-06)]]"
- "[[Memory Safety Audit (2026-06)]]"
- "[[Security Audit (2026-06)]]"
- "[[Concurrency & Determinism Audit (2026-06)]]"
- "[[Build & CI Audit (2026-06)]]"
- "[[Test Coverage Audit (2026-06)]]"
- "[[Docs & Licensing Audit (2026-06)]]"
