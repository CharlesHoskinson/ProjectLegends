---
type: source
aliases: ["Docs Spec Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: Docs & Licensing Audit (2026-06)
authors: [Claude audit fleet]
url:
publisher:
published: 2026
accessed: 2026-06-09
source_type: report
covers:
  - "[[Legends C API Layer]]"
  - "[[IPC Runtime (Project Legends)]]"
  - "[[Engine Bridge (DOSBox-X)]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[Project Legends Documentation Corpus]]"
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Determinism Oracle Weakness]]"
  - "[[Licensing Inconsistency]]"
  - "[[Documentation Drift]]"
  - "[[Prior-Audit Remediation Status]]"
---

# Docs & Licensing Audit (2026-06)

## Summary

Documentation, spec-drift, and licensing audit of Project Legends at HEAD `ef11f20` (2026-06-09), following up the 2026-02-24 AUDIT.md. Recently refreshed material (README architecture counts, RELEASING.md vs ci.yml) verified exact, but the rest of the doc set has drifted in both directions, and licensing is the most serious area: a bare MIT LICENSE file sits at the root of a mostly-GPL codebase, GPL-2.0-only vs -or-later is contradicted by every SPDX file tag, and a headline "Wasm sandbox" capability references artifacts that were never committed.

## Key takeaways

- LIC-01 (CRITICAL): the root `LICENSE:1-21` is the verbatim MIT license with no component scoping, while `README.md:312` and CHANGELOG.md describe it as a "multi-component license overview" — a license-misrepresentation risk over ~1M lines of vendored GPL DOSBox-X code the project has no right to relicense.
- LIC-02 (HIGH): docs claim GPL-2.0-only (`README.md:355`, `CONTRIBUTING.md:226-233`) but the code is 107 files tagged GPL-2.0-or-later, 18 MIT, zero GPL-2.0-only in `src/`; upstream DOSBox-X is itself GPL-2.0-or-later (`engine/src/cpu/cpu.cpp:4-7`), so README's "consistent with DOSBox-X" claim is wrong about upstream.
- LIC-03 (HIGH): the MIT-tagged proxy (`src/legends_proxy/proxy_api.cpp:1`) includes the GPL-declared `legends_embed.h`; `DEPENDENCIES.md:18` claims the MIT IPC/proxy libraries "do not link any GPL code"; the design doc calls the shell "proprietary" while `src/app/application.cpp:1` is GPL-tagged — the shell cannot be simultaneously proprietary and GPL.
- LIC-04 (MEDIUM): NOTICE lists 8 components but omits vendored stb and glad (both compiled into the app); `DEPENDENCIES.md:5-11` lists only 5 dependencies; NOTICE contains none of the SPDX identifiers or per-directory assignments that README, CONTRIBUTING, and CHANGELOG claim it has.
- DOC-01 (HIGH): "Wasm sandbox support" is advertised present-tense (`README.md:28`) with a 100-line `ARCHITECTURE.md:611-716` section, yet `wasm.md` and `wit/legends-emulator.wit` have never existed in git history; `TODO.md:20` itself says "NOT STARTED | 0 of 50".
- DOC-02 (HIGH): REQUIREMENTS.md statuses are ~3.5 months stale; sampling 10 requirements found at least 6 of 24 GAPs already fixed in code (e.g. REQ-EX-001/002 via `cpu_bridge.cpp:113,119`, REQ-LC-003 via `legends_embed_api.cpp:79-82`), while REQ-DT-004 (HashMode::Full, `state_hash_compat.cpp:48-50`) genuinely remains open.
- DOC-03 (MEDIUM): TODO.md marks the same requirement IDs both complete (`TODO.md:78-92`) and missing (`TODO.md:167-186`); labels IPC "STUB ONLY" while ~2,700 lines of real IPC/proxy/host code exist and `ci.yml:95-126` runs a dedicated linux-ipc job; two checked boxes claim a `LICENSES/` directory that never existed.
- DOC-04 (MEDIUM): `ARCHITECTURE.md:195-198` documents a 96-byte "LEGS" version-2 save-state header, contradicting both README (64 bytes) and code (`legends_embed_api.cpp:92-93`: "DBXS", version 3); it also still labels the real `cpu_bridge.cpp` a stub and omits whole source trees from its file organization.
- DOC-05 (LOW): README's API reference covers 23 of 50 exported `LEGENDS_API` functions and its error table omits 5 defined codes (`legends_embed.h:74-84`); `CONTRIBUTING.md:148` names a nonexistent `legends_status_t` type (actual: `legends_error_t`).
- SPEC-01 (MEDIUM): the GPL-isolation linker-map check — the only technical control behind the "zero GPL object code" shell claim — is documented as a CI gate (`ARCHITECTURE.md:606-607`) but `cmake/VerifyGPLIsolation.cmake` is included nowhere and no workflow references it; the linux-ipc job only verifies the IPC executables exist.
- SPEC-02 (MEDIUM): `openspec/specs/` and `openspec/changes/archive/` are both empty while 17 active change directories include fully-completed February work — OpenSpec has degenerated into a write-only proposal folder despite README presenting it as a live quality gate.
- Prior-audit re-check: C2 (PIC_RunQueue/CPU_Check_NMI) and H5 are resolved in code but REQUIREMENTS.md still claims GAP; H7 (HashMode::Full) remains open; L2 is half-fixed (README corrected, ARCHITECTURE.md not); L1 confirmed-open with a worse ratio (23/50).
- Verified accurate, no finding: README architecture diagram counts (50 C APIs, 108 message types, 89 structs, 43 dispatcher cases) all exact at HEAD; RELEASING.md matches the actual ci.yml job set (sanitizers, fuzz, tlaplus, coverage, packaging-on-tag).
- Suggested remediation: a 1-week licensing reconciliation sprint (LIC-01/02/04 + LICENSES/), 2-3 days to make the isolation claim enforceable (LIC-03 + SPEC-01), a 3-5 day doc-truth sweep (DOC-01..05), and 1-2 days of OpenSpec hygiene (SPEC-02).

## Covers

- [[Legends C API Layer]] — README documents 23 of 50 exported functions, omits 5 error codes, and `legends_embed.h` carries prose GPL text with no SPDX tag.
- [[IPC Runtime (Project Legends)]] — ~2,700 lines of real IPC/proxy/host code contradict TODO.md's "STUB ONLY" label, but the MIT proxy compiles against a GPL header.
- [[Engine Bridge (DOSBox-X)]] — cpu_bridge.cpp is real (not a stub) and vendored DOSBox-X is GPL-2.0-or-later, contradicting two docs.
- [[Build & CI System (Project Legends)]] — RELEASING.md matches ci.yml exactly, but the documented GPL-isolation linker-map gate is wired into nothing.
- [[Project Legends Documentation Corpus]] — the doc set splits into an accurate recently-refreshed era and a stale February era drifted in both directions.
- [[Vacuous Interrupt Delivery (C2)]] — prior C2 is resolved in code at `cpu_bridge.cpp:113,119` while REQUIREMENTS.md still lists the GAP.
- [[Determinism Oracle Weakness]] — REQ-DT-004 / prior H7 remains open: `state_hash_compat.cpp:48-50` still only appends a "FULL_MODE" marker.
- [[Licensing Inconsistency]] — bare MIT root LICENSE, -only vs -or-later contradiction, unexamined GPL header dependency, and missing stb/glad attribution.
- [[Documentation Drift]] — Wasm capability with never-committed artifacts, stale REQUIREMENTS statuses, self-contradicting TODO.md, and wrong save-state constants in ARCHITECTURE.md.
- [[Prior-Audit Remediation Status]] — re-check table for L1, L2, L7, H5, H7, H8, C2: several fixed in code, none reflected in tracking docs.
