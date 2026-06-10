---
type: entity
entity_kind: system
aliases: ["tests/", "fuzz targets", "benchmarks"]
tags: [entity, type/entity, topic/audit, topic/testing]
created: 2026-06-09
updated: 2026-06-09
status: draft
related:
  - "[[Determinism Oracle Weakness]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
sources:
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
---

# Project Legends Test Suite

## Overview

170 test files (~32k lines) in tests/ plus 82 in engine/tests, ~4,600 TEST macros, four fuzz targets, three benchmark files. The audit's verdict: broad but under-enforced, with oracles weakest exactly where the product's claims are strongest (determinism, save/load fidelity, IPC parity).

## Facts

- Overall verdict: wide but under-enforced, with weak oracles.^[from [[Test Coverage Audit (2026-06)]] — "wide but under-enforced, with weak oracles"]
- A quarter of registered integration tests are skip stubs that report green: 8 of 33 files.^[from [[Test Coverage Audit (2026-06)]] — "8 of 33 registered integration test files"]
- A real boot-to-prompt test is the suite's strongest end-to-end check.^[from [[Test Coverage Audit (2026-06)]] — "the single strongest end-to-end assertion in the suite"]
- IPC unit tests round-trip only well-formed messages — benign, not adversarial.^[from [[Security Audit (2026-06)]] — "those are well-formed inputs, not adversarial"]
- The determinism test architecture is sound; the hash it compares is not.^[from [[Concurrency & Determinism Audit (2026-06)]] — "The test architecture is good"]
- The engine event-scheduler queue is still outside V5 serialization, keeping a save-state test PARTIAL.^[from [[Backlog Verification Audit (2026-06)]] — "engine event-scheduler queue still not serialized"]
- Stated test strictness is contradicted by -Wno-error on the test targets.^[from [[Build & CI Audit (2026-06)]] — "tests should be strict too"]
- The promised soak suite cannot run: no workflow enables it and the cmake label does not exist.^[from [[Build & CI Audit (2026-06)]] — "finds no SOAK reference"]
- Coverage is report-only on pushes; no minimum threshold is enforced.^[from [[Test Coverage Audit (2026-06)]] — "no minimum threshold is enforced by CI yet"]
- The architecture audit recommends one parameterized conformance suite run against both runtimes.^[from [[API & Architecture Audit (2026-06)]] — "Write a single parameterized conformance test suite"]

## Related

- [[Determinism Oracle Weakness]] — the suite's central blind spot
- [[Quality Gate Demotion (2026-06-08)]] — why even existing tests stopped gating
- [[IPC Trust Boundary Gaps]] — the untested boundary
