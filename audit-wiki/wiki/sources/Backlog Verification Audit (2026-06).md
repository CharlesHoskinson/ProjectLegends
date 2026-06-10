---
type: source
aliases: ["Backlog Miner Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: Backlog Verification Audit (2026-06)
authors: [Claude audit fleet]
url:
publisher:
published: 2026
accessed: 2026-06-09
source_type: report
covers:
  - "[[Prior-Audit Remediation Status]]"
  - "[[Legends C API Layer]]"
  - "[[Engine Bridge (DOSBox-X)]]"
  - "[[IPC Runtime (Project Legends)]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[Project Legends Test Suite]]"
  - "[[Project Legends Documentation Corpus]]"
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Determinism Oracle Weakness]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Documentation Drift]]"
---

# Backlog Verification Audit (2026-06)

## Summary

A 2026-06-09 backlog-miner audit re-verified all 30 findings from the 2026-02-24 AUDIT.md against HEAD `ef11f20` (115 commits later): 22 are verifiably resolved with traceable fix comments and commits, 8 remain open, none critical. The report's headline shift is that the paper trail is now the weak point — it raises five new documentation-of-record findings (N1–N5), including a case-colliding duplicate roadmap that clobbered March's source-verified corrections and a CHANGELOG claim of TLS verification with no transport layer in existence.

## Key takeaways

- 22 of 30 prior AUDIT.md findings are resolved at HEAD `ef11f20`, including both criticals (C1 header duplication, C2 missing PIC_RunQueue/NMI); open remainder is H2, H3, H4+M5, H7 (narrowed), M4, M10, L1, L3 — none critical, mostly accepted-design or hygiene debt.
- C2 (critical) resolved: `engine/src/misc/cpu_bridge.cpp:113` now calls `PIC_RunQueue()` before CPU execution and `:119` calls `CPU_Check_NMI()` after, both with "(C2 fix)" comments.
- H7 (determinism oracle) only narrowed: `engine/src/misc/state_hash.cpp:300-303` now hashes full conventional memory, but `engine/include/dosbox/state_hash.h:40-47` still promises VGA and device state that is not hashed — contract still overstates.
- H2 still open: two unsynchronized thread-local `g_current_context` pointers persist at `engine/src/aibox/machine_context.cpp:20` and `engine/src/misc/dosbox_context.cpp:65`, mitigated by ContextGuard dual-set during step scope.
- H3/M10 open but contained: `MachineContext::step()` remains a counter-incrementing stub, reachable only via deprecated `dosbox_step()` (`engine/src/misc/dosbox_context.cpp:973-976`); REQ-LC-005 stays a GAP until the path is removed.
- N1 (high): `ROADMAP.md` and `roadmap.md` are both tracked as case-colliding identical 209,189-byte blobs; commit `1dd76b4` (2026-06-08) clobbered the March source-verified 427-line ROADMAP (commit `8e3b0b0`) back to a 4,061-line document whose changelog still falsely stamps v4.1.0/2026-02-25.
- N2 (high): `CHANGELOG.md:36-38` claims "TLS verification" while no HTTP/TLS transport exists anywhere (`src/app/ai_http_client.cpp:212` defers libcurl wiring), so REQ-SEC-005 cannot be satisfied as claimed.
- N3 (medium): TODO.md is stale since 2026-02-27 and internally contradictory — REQ-MOUNT-001 appears both complete (`TODO.md:90`) and as a release blocker (`TODO.md:168`); GPL isolation shown as 2/16 "STUB" while the later audit measured 12-13/16.
- N4 (medium): IPC mode silently lacks capability parity — `src/legends_proxy/proxy_api.cpp` returns `LEGENDS_ERR_NOT_SUPPORTED` for 6 APIs (video capture, TTF font, event callbacks) and `src/legends_ipc/protocol.cpp:1` is a stub, contradicting the "GPL isolation MOSTLY COMPLETE" narrative.
- N5 (low): AUDIT.md was never annotated with the 22 resolutions, so anyone triaging from it alone would re-fix solved problems.
- L1 got worse: the C API grew from 22 to 50 functions and 27 of 50 are not mentioned in README.md at all.
- CI stabilization per CIFix.md (2026-06-08) is verified in place: workflows split into primary vs optional lanes, the determinism failure fixed, MSVC `/wd4834` contained to test targets, 4,497 local tests passing per its log.
- Test/spec positives: TLA P0 backlog executed (real INSTANCE composition in `spec/tla/Composition.tla:272-293`, 26 .cfg files, no TRUE stubs); residual gap: the engine event-scheduler queue is still not serialized, so SaveStateTest `EventCountPreserved` stays PARTIAL.
- Suggested sprint themes: make security claims facts (SEC-005/023/024 still open), close the 6 IPC proxy parity gaps, decide the unstarted 0/50 Wasm section, and clear engine-layer debt plus documentation-of-record defects (N1/N3/N5).

## Covers

- [[Prior-Audit Remediation Status]] — verifies all 30 AUDIT.md findings with file:line evidence: 22 resolved, 8 open, disposition table for synthesis
- [[Legends C API Layer]] — H5/H6/H9/M1/M2/M11/L2/L4 fixes confirmed in legends_embed_api.cpp; README API coverage (L1) now worse at 27/50 undocumented
- [[Engine Bridge (DOSBox-X)]] — C2 fix verified in cpu_bridge.cpp; H2 dual thread-locals, H3 stub step, H4 init stubs, and M10 deprecated path remain open
- [[IPC Runtime (Project Legends)]] — protocol.cpp stub plus 6 proxy NOT_SUPPORTED parity gaps undercut the GPL-isolation-complete narrative (N4)
- [[Build & CI System (Project Legends)]] — CIFix.md lane restructure and determinism fix verified; CI check for case-colliding tracked paths recommended
- [[Project Legends Test Suite]] — sentinel-destroy tests fixed (L8), HandleRegistry is test-only dead code (L3), EventCountPreserved still PARTIAL
- [[Project Legends Documentation Corpus]] — four documentation-of-record defects (N1–N3, N5) across ROADMAP, TODO.md, CHANGELOG.md, and AUDIT.md
- [[Vacuous Interrupt Delivery (C2)]] — resolved at cpu_bridge.cpp:113/:119 with traceable "(C2 fix)" comments
- [[Determinism Oracle Weakness]] — H7 narrowed: full conventional-memory hashing landed, VGA/device hashing still missing versus the header contract
- [[Quality Gate Demotion (2026-06-08)]] — the primary-vs-optional lane split and /wd4834 containment from CIFix.md confirmed in place
- [[Documentation Drift]] — clobbered source-verified ROADMAP, false version stamp, stale contradictory TODO.md, and untrue TLS changelog claim
