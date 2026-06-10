---
type: entity
entity_kind: system
aliases: ["legends_embed.h", "C ABI layer"]
tags: [entity, type/entity, topic/audit, topic/api]
created: 2026-06-09
updated: 2026-06-09
status: draft
related:
  - "[[Save-State Load Path Overflow]]"
  - "[[IPC Runtime (Project Legends)]]"
sources:
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
  - "[[Memory Safety Audit (2026-06)]]"
---

# Legends C API Layer

## Overview

The public embedding surface: `include/legends/legends_embed.h` (50 `legends_*` C functions) implemented by `src/legends/legends_embed_api.cpp` (~3,220 lines). The strongest-engineered layer in the project, with three soft spots: the joystick API, reentrancy-guard coverage on newer functions, and documentation that covers under half the surface.

## Facts

- The in-process C ABI core is judged professionally engineered.^[from [[API & Architecture Audit (2026-06)]] — "The C ABI core is professional."]
- The API doubled from 22 to 50 functions since February without a version bump.^[from [[API & Architecture Audit (2026-06)]] — "grew from 22 to 50 functions"]
- The config struct promises additive evolution that the exact `struct_size` check defeats.^[from [[API & Architecture Audit (2026-06)]] — "New fields added at end only"]
- The load path validates its header up front.^[from [[Security Audit (2026-06)]] — "validates header size, magic, version"]
- Input events are pre-validated before any state mutation.^[from [[Security Audit (2026-06)]] — "pre-validation pass over input-event types before any mutation"]
- The wrapper loader applies consistent overflow-safe bounds macros.^[from [[Memory Safety Audit (2026-06)]] — "Bounds-validation macro discipline in the wrapper loader"]
- The joystick API violates the error model: state is mutated on a call that reports failure.^[from [[Concurrency & Determinism Audit (2026-06)]] — "state is mutated on a call that reports failure"]
- Joystick input bypasses the deterministic input queue, writing guest RAM directly.^[from [[Concurrency & Determinism Audit (2026-06)]] — "writes joystick axis timer counts and button bits directly into guest RAM"]
- Reentrancy guards are still missing on mutating APIs added since the guard was introduced.^[from [[Concurrency & Determinism Audit (2026-06)]] — "Still missing on mutating APIs added since"]
- About a third of the public ABI has no behavioral verification.^[from [[Test Coverage Audit (2026-06)]] — "roughly a third of the public ABI has no behavioral verification"]
- README documents 23 of the 50 exported functions.^[from [[Docs & Licensing Audit (2026-06)]] — "covers 23 of 50 exported functions"]
- The flagship public header carries no SPDX tag, against the project's own policy.^[from [[Docs & Licensing Audit (2026-06)]] — "with no SPDX tag at all"]

## Related

- [[Save-State Load Path Overflow]] — its load path is the main untrusted-input surface
- [[IPC Runtime (Project Legends)]] — the second backend that must match these semantics
- [[Determinism Oracle Weakness]] — `legends_verify_determinism` consumes the weak hash
