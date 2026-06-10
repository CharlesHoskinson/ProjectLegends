---
type: synthesis
aliases: ["June 2026 audit verdict"]
tags: [synthesis, type/synthesis, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
question: What is the overall state of Project Legends at HEAD ef11f20 (2026-06-09)?
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
  - "[[Prior-Audit Remediation Status]]"
confidence: moderate
---

# Audit Verdict (2026-06)

**Thesis: the code outran its instruments.** Since February the team genuinely closed 22 of 30 audit findings ([[Prior-Audit Remediation Status]]) and built a real IPC layer — but everything that *measures* the project regressed or lagged: the determinism oracle can't see most divergence ([[Determinism Oracle Weakness]]), the CI gates were demoted the day before this audit ([[Quality Gate Demotion (2026-06-08)]]), the GPL boundary is enforced by comments ([[Licensing Inconsistency]]), and the documents of record contradict the code in both directions ([[Documentation Drift]]). The result is a B-grade codebase wrapped in D-grade verification, with two genuinely critical defects: the [[Save-State Load Path Overflow]] (confirmed exploitable-class heap overflow in the default build) and the bare-MIT root LICENSE over a GPL codebase.

Fleet grades: backlog-miner B; api-architecture, memory-safety, security, concurrency-determinism, build-ci, test-coverage all C; docs-spec D. Two reported findings failed adversarial verification and were excluded (SEC-01 shared-memory geometry OOB; api-05 broken installed package). Two cross-agent contradictions are flagged on their concept pages: whether C2's interrupt fix is real ([[Vacuous Interrupt Delivery (C2)]] — contested, link-level analysis says vacuous) and whether the engine RLE decode is bounded ([[Save-State Load Path Overflow]] — verifier confirmed the overflow).

Priority logic (inference, not directly sourced): fix what is exploitable or legally hazardous first; then make the record and the oracles truthful so later work is verifiable; then finish the IPC boundary the roadmap depends on; defer the open-ended engine-time epic until the oracles can catch its regressions. This ordering is elaborated in [[Sprint Plan Derivation (2026-06)]].

## Sources

- "[[Backlog Verification Audit (2026-06)]]"
- "[[API & Architecture Audit (2026-06)]]"
- "[[Memory Safety Audit (2026-06)]]"
- "[[Security Audit (2026-06)]]"
- "[[Concurrency & Determinism Audit (2026-06)]]"
- "[[Build & CI Audit (2026-06)]]"
- "[[Test Coverage Audit (2026-06)]]"
- "[[Docs & Licensing Audit (2026-06)]]"
