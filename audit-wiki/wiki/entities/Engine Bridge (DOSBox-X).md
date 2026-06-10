---
type: entity
entity_kind: system
aliases: ["dosbox_library", "cpu_bridge", "aibox layer"]
tags: [entity, type/entity, topic/audit, topic/engine]
created: 2026-06-09
updated: 2026-06-09
status: draft
related:
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Save-State Load Path Overflow]]"
sources:
  - "[[Memory Safety Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
---

# Engine Bridge (DOSBox-X)

## Overview

The adaptation layer between the legends wrapper and the ~1.05M-line vendored DOSBox-X fork: `engine/src/misc/dosbox_library.cpp` (C library facade), `engine/src/misc/cpu_bridge.cpp` (stepped execution), and the `engine/src/aibox` context layer. Real x86 execution flows through here. It carries the audit's worst memory defect (mem-01) and its sharpest correctness dispute (C2 stub linkage).

## Facts

- Its V5 deserializer overwrites the live allocation descriptor verbatim from untrusted input — the critical mem-01 overflow.^[from [[Memory Safety Audit (2026-06)]] — "overwrites the live allocation descriptor verbatim from untrusted input"]
- The real PIC implementation is not part of any CMake target, so library builds link a no-op stub.^[from [[Concurrency & Determinism Audit (2026-06)]] — "is not part of any CMake target"]
- The bridge's cycle accounting only works with the stub; naive relinking would corrupt it.^[from [[Concurrency & Determinism Audit (2026-06)]] — "the bridge's cycle accounting only works with the stub"]
- The dual thread-local context accessors (prior H2) remain tracked engine debt.^[from [[Backlog Verification Audit (2026-06)]] — "Eliminate thread-local current_context() accessors"]
- The seven init_* no-ops are now documented as accepted design delegating to the engine bridge.^[from [[Backlog Verification Audit (2026-06)]] — "These init stubs delegate to DOSBox-X engine bridge"]
- Its V5 load path validates magic, version, and size underflow with CRC and per-section checks.^[from [[Security Audit (2026-06)]] — "magic, forward-compatible version reject, size underflow guard"]
- ARCHITECTURE.md still labels the bridge a stub although the bridge is real.^[from [[Docs & Licensing Audit (2026-06)]] — "the bridge is real"]
- The vendored engine is GPL code the project has no right to relicense.^[from [[Docs & Licensing Audit (2026-06)]] — "code the project has no right to relicense"]
- Root CMake FORCE-settings make every configuration compile the ~33k-line engine test suite.^[from [[Build & CI Audit (2026-06)]] — "compile the ~33k-line engine test suite"]
- Known engine data races (g_active_instance, CrashBreadcrumb) are the stated reason TSan stays muted.^[from [[Concurrency & Determinism Audit (2026-06)]] — "TSan detects pre-existing data races in engine global state"]

## Related

- [[Vacuous Interrupt Delivery (C2)]] — the stub-linkage dispute
- [[Save-State Load Path Overflow]] — mem-01 lives in this layer's loader
- [[Engine Bridge (DOSBox-X)]] facts feed [[Sprint Plan Derivation (2026-06)]] Sprints 0 and 6
