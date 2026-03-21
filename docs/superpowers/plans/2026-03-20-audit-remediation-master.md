# Audit Remediation Master Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement each sub-plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Address all findings from the 22-agent audit (`AUDIT_REPORT.md`) to reach Release A quality gate.

**Architecture:** Five independent workstreams, each executable in parallel via isolated worktrees. Each produces a self-contained, testable result. Ordered by blast radius — critical bugs first, then infrastructure, then modernization.

**Tech Stack:** C++23, CMake 3.20+, GoogleTest v1.14.0, gsl-lite v1.0.0, SDL3

---

## Workstream Overview

| # | Plan | Priority | Scope | Effort |
|---|------|----------|-------|--------|
| 1 | [Critical Bug Fixes](2026-03-20-plan-1-critical-bugs.md) | P0 | 8 critical bugs + 6 stubs-as-implementations | S-M |
| 2 | [Test Infrastructure](2026-03-20-plan-2-test-infrastructure.md) | P1 | Shared fixtures, monolith split, build improvements | M |
| 3 | [Security & Correctness](2026-03-20-plan-3-security-correctness.md) | P1 | 7 overstated REQ-SECs + QA gaps | M |
| 4 | [C++23 Modernization](2026-03-20-plan-4-cpp23-modernization.md) | P2 | [[nodiscard]], string_view, gsl contracts, span | L |
| 5 | [Release Readiness](2026-03-20-plan-5-release-readiness.md) | P2 | Docs, CI gaps, Phase 3 wiring, packaging | M-L |

## Execution Order

Workstreams 1-3 can run in **parallel** (no shared files). Workstream 4 depends on 2 (test infrastructure must exist before modernizing signatures). Workstream 5 is independent.

```
    ┌──── Plan 1: Critical Bugs ────────┐
    │                                     │
    ├──── Plan 2: Test Infrastructure ───┤──► Plan 4: C++23 Modernization
    │                                     │
    ├──── Plan 3: Security & Correctness ┤
    │                                     │
    └──── Plan 5: Release Readiness ─────┘
```

## Traceability

Every task references the specific audit finding (Agent #, section, line number) it addresses. After completion, update `AUDIT_REPORT.md` section 13 (Top 10 Priorities) to mark items resolved.
