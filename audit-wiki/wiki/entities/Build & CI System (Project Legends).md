---
type: entity
entity_kind: system
aliases: ["ci.yml", "CMake build system"]
tags: [entity, type/entity, topic/audit, topic/ci]
created: 2026-06-09
updated: 2026-06-09
status: draft
related:
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Licensing Inconsistency]]"
sources:
  - "[[Build & CI Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
---

# Build & CI System (Project Legends)

## Overview

Root CMakeLists (63KB) + engine CMake + cmake/ modules + four GitHub workflows + githooks + Python check scripts. Impressive machinery on paper — much of it not actually wired to anything that gates a merge, builds the app, or has ever executed (the release pipeline has literally never run).

## Facts

- The machinery has unusual breadth: a 4-sanitizer matrix, libFuzzer jobs, 17 TLA+ model-checking steps.^[from [[Build & CI Audit (2026-06)]] — "a 4-sanitizer matrix, libFuzzer jobs, 17 TLA+ model-checking steps"]
- The repository has no git tags, so the tag-gated release pipeline and coverage release gate have never executed.^[from [[Build & CI Audit (2026-06)]] — "the repository has no git tags"]
- No workflow uses compiler caching; the 1M-line engine rebuilds cold up to ~12 times per push.^[from [[Build & CI Audit (2026-06)]] — "No workflow uses ccache/sccache"]
- PRs targeting develop bypass the primary pipeline; breakage is discovered only after merge.^[from [[Build & CI Audit (2026-06)]] — "Breakage is discovered only after merge"]
- All FetchContent pins are mutable git tags with no integrity hash.^[from [[Build & CI Audit (2026-06)]] — "All FetchContent pins are mutable git"]
- The IPC CI job never builds the application, masking the boot and link failures.^[from [[API & Architecture Audit (2026-06)]] — "CI never sees any of this"]
- Pre-merge CI is headless-only; SDL backends get no pre-merge execution.^[from [[Test Coverage Audit (2026-06)]] — "CI is headless-only; SDL-backend tests are path-filtered/nightly"]
- Benchmarks exist but are never built in CI; performance can regress silently.^[from [[Test Coverage Audit (2026-06)]] — "Benchmarks exist but are never built in CI"]
- The GPL symbol-isolation scan — the core compliance guarantee — is unenforced.^[from [[Security Audit (2026-06)]] — "This is the core GPL-compliance guarantee and it is unenforced"]
- The isolation verifier is documented as a CI gate but is never executed.^[from [[Docs & Licensing Audit (2026-06)]] — "documented as a CI gate but is never executed"]
- The 2026-06-08 stabilization work itself is verified as landed.^[from [[Backlog Verification Audit (2026-06)]] — "CIFix.md work is in place"]

## Related

- [[Quality Gate Demotion (2026-06-08)]] — its acute failure mode
- [[Licensing Inconsistency]] — the unwired isolation enforcement
- [[Project Legends Test Suite]] — what the gates do (and don't) run
