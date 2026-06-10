# Log

Append-only. One line per event: `## [YYYY-MM-DD] <op> | <title>`.

## [2026-06-09] init | Project Legends Audit Wiki
- Created wiki skeleton.
- Domain: end-to-end audit of the Project Legends x86 emulation framework — findings, risks, subsystem assessments, sprint planning.

## [2026-06-09] audit | Dispatched 8-role audit fleet
- Roles: backlog-miner (verify AUDIT.md 2026-02-24 findings at HEAD), api-architecture, memory-safety, security, concurrency-determinism, build-ci, test-coverage, docs-spec.
- New critical/high findings get an adversarial verification pass.
- Agent reports land immutably in `raw/<role>-report.md`; synthesis into wiki pages follows.
- Context going in: legends layer ~21k lines, vendored engine ~1.05M lines (boundary-audit only), prior audit 30 findings (~3.5 months stale), roadmap gaps: Security 6/22, GPL isolation 2/16, Wasm 0/50, UX 2/11.

## [2026-06-09] ingest | Eight fleet reports → wiki synthesis
- Fleet completed: 28 agents, ~21 min. Raw reports + structured JSON archived in `raw/` (immutable).
- 8 source pages written (agent-authored, anchors grep-validated verbatim).
- Synthesized 8 concepts, 6 entities, 2 syntheses; overview/index/_indexes updated.
- Two findings refuted under adversarial verification and excluded: SEC-01 (SHM geometry OOB), api-05 (broken installed package).
- Two contradictions flagged with [!conflict]: C2 fix real-vs-vacuous ([[Vacuous Interrupt Delivery (C2)]], contested → treated OPEN); engine RLE decode bounded-vs-overflow ([[Save-State Load Path Overflow]], verifier confirmed overflow).
- Grades: backlog B; api/mem/sec/conc/ci/test C; docs D. Criticals: mem-01 heap overflow, lic-01 MIT-over-GPL LICENSE.

## [2026-06-09] plan | Eight-sprint program derived
- See [[Sprint Plan Derivation (2026-06)]]; executable plan at `docs/superpowers/plans/2026-06-09-audit-implementation-sprints.md` in the repo.
- Spine: 0 stop-the-bleeding → (1 truthful record ∥ 2 trustworthy oracles) → 3 IPC real → 4 boundary hardening → 5 GPL enforceable → 6 make time real (gated on 2) → 7 debt + release dry run.

## [2026-06-10] audit | Sprint 0 (GPT 5.5 Codex) — PASS 5/5
- Audited branch `sprint-0/stop-the-bleeding` (HEAD 3ff9754, 5 commits). Verdict PASS, no code defects.
- Method: full git-diff review, adversarial source analysis, independent rebuild (`ninja: no work to do`), independent re-run of both regression tests (25/25 + 15/15), independent 60s fuzz (228k execs, 0 crashes), independent actionlint (exit 0).
- mem-01 (critical overflow) fixed at root cause — settles the contested overflow-vs-bounded conflict in favor of the overflow; [[Save-State Load Path Overflow]] now superseded/resolved.
- lic-01, mem-02, CI gate re-arm all PASS; [[Quality Gate Demotion (2026-06-08)]] resolved, [[Licensing Inconsistency]] partially resolved.
- All 6 handoff attestations verified true against the diff. Full report: `raw/sprint-0-audit-2026-06-10.md`, synthesis [[Sprint 0 Implementation Audit (2026-06-10)]].
- Minor process findings folded into the Sprint 1 directive (commit handoff, start-stamp, surface build-flag overrides).
- Full ctest independently re-run after the fact: 4512/4512 passed (219.65s), corroborating the handoff headline exactly.

## [2026-06-10] audit | Sprint 1 (GPT 5.5 Codex) — PASS 8/8
- Audited branch `sprint-1/truthful-record` (HEAD 56f9dfa, 11 commits). Verdict PASS, no defects.
- Method: three-dot diff scope checks (src/engine/audit-wiki diffs empty), independent re-run of all 3 new scripts (case-collision pass/fail, gen_readme byte-identical, openspec staleness), random-subset claim re-verification vs source.
- All three pre-flagged corrections honored and verified: roadmap de-dup (not restore); CHANGELOG TLS reworded (not deleted); REQ-EX-001/002 PARTIAL (confirmed cpu_library_stubs.cpp:56-60 is a real no-op PIC stub — C2 nuance preserved).
- 6 TODO contradictions resolved; AUDIT.md 22/8 tally; ARCHITECTURE constants fixed 64/DBXS/v3; Wasm demoted to planned. Two owner decisions queued (GPL -or-later; Wasm defer).
- [[Documentation Drift]] marked substantially resolved. Full report: `raw/sprint-1-audit-2026-06-10.md`, synthesis [[Sprint 1 Implementation Audit (2026-06-10)]].
- 2026-06-10 — ingest: CI Gate Coverage Map (graphify + ModuleDAG + workflow triggers).
- 2026-06-10 — ingest: CI Run History (2026-06) from gh api run/job records (raw/ci-run-history-2026-06.json).
- 2026-06-10 — ingest: CI Workflows (GitHub Actions) entity (four workflow files inventoried).
- 2026-06-10 — update: Build & CI System (Project Legends) — build system inventory section appended.
- 2026-06-10 — update: Project Legends Test Suite — test infrastructure inventory section appended.
- 2026-06-10 — ingest: Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism) entity.
- 2026-06-10 — ingest: Quality Gate Scripts & Hooks entity.
- 2026-06-10 — ingest: Local Dev Loop entity.
- 2026-06-10 — ingest: CI Design for C++-CMake Monorepos (2026-06) research (raw/research/cpp-cmake-monorepo-ci.md).
- 2026-06-10 — ingest: Compiler Caching on GitHub Actions (2026-06) research (raw/research/compiler-caching-actions.md).
- 2026-06-10 — ingest: Test Impact Analysis & Selection (2026-06) research (raw/research/test-impact-analysis.md).
- 2026-06-10 — ingest: Coverage Policy Ratcheting (2026-06) research (raw/research/coverage-ratcheting.md).
- 2026-06-10 — ingest: Continuous Fuzzing in CI (2026-06) research (raw/research/continuous-fuzzing-ci.md).
- 2026-06-10 — ingest: Flaky-Test Detection & Quarantine (2026-06) research (raw/research/flaky-test-quarantine.md).
- 2026-06-10 — ingest: Vendored & License-Isolated Dependency CI (2026-06) research (raw/research/vendored-license-isolation-ci.md).
- 2026-06-10 — ingest: Local Preflight Design (2026-06) research (raw/research/local-preflight-design.md).
- 2026-06-10 — ingest: Merge Queues & Required Checks (2026-06) research (raw/research/merge-queues-required-checks.md).
- 2026-06-10 — ingest: Sanitizer Lane Strategy (2026-06) research (raw/research/sanitizer-lane-strategy.md); attribution fixes applied after citation review.
- 2026-06-10 — ingest: Gap Analysis — Modularity (2026-06) (M-1..M-8).
- 2026-06-10 — ingest: Gap Analysis — Maintainability (2026-06) (A-1..A-8).
- 2026-06-10 — ingest: Gap Analysis — Test Coverage Intelligence (2026-06) (T-1..T-8).
- 2026-06-10 — ingest: Gap Analysis — Always Green (2026-06) (G-1..G-12).
- 2026-06-10 — fix: globals-registry step count reconciled to ten across CI Workflows entity and gap analyses.
- 2026-06-10 — ingest: Recommendation Review (2026-06) — adversarial pass over M/A/T/G candidates.
