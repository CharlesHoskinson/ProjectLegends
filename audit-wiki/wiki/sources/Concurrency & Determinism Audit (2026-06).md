---
type: source
aliases: ["Concurrency Determinism Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: Concurrency & Determinism Audit (2026-06)
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
  - "[[Project Legends Test Suite]]"
  - "[[Project Legends Documentation Corpus]]"
  - "[[IPC Trust Boundary Gaps]]"
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Determinism Oracle Weakness]]"
  - "[[Documentation Drift]]"
  - "[[Prior-Audit Remediation Status]]"
---

# Concurrency & Determinism Audit (2026-06)

## Summary

Audit of Project Legends at HEAD `ef11f20` (2026-06-09, 115 commits past the 2026-02-24 baseline) covering threading guarantees, step determinism, event ordering, audio/timer interactions, prior-finding status, and TLA+ conformance. Thread discipline has genuinely improved — four of five non-conformant TLA+ invariants are fixed — but the headline discovery is that the "C2 fix" is vacuous: the library build links a stub `PIC_RunQueue()`, so no device time advances and the determinism story covers raw instruction interpretation only, while the determinism hash itself is blind to registers and RAM.

## Key takeaways

- CRITICAL/HIGH (C2 reconfirmed): `cpu_bridge.cpp:112-119` calls `PIC_RunQueue()`/`CPU_Check_NMI()`, but `aibox_core` compiles the stub from `engine/src/cpu/cpu_library_stubs.cpp:53-60`; the real `engine/src/hardware/pic.cpp` is in no CMake target (engine/CMakeLists.txt:156-199). No PIT/IRQ events ever fire, `TIMER_AddTick()` is never called on the step path, and `events_processed` is always 0 — virtual device time does not advance.
- Latent bug for the eventual C2 fix: the bridge's consumed-cycle math (`CPU_Cycles = budget` at cpu_bridge.cpp:110-113, `consumed` at line 122, restore at 130) only works with the stub; the real PIC's `CPU_CycleLeft` juggling requires restructuring into per-ms Normal_Loop-style slices.
- HIGH (conc-07): the determinism oracle is weak — `legends_get_state_hash` uses `HashMode::Fast`, whose CPU hash covers only cycle counters/flags (dosbox_context.cpp:103-130) and excludes GPRs, EIP, EFLAGS, segments, and RAM contents (Full mode at state_hash.cpp:300-305 has no callers). `legends_verify_determinism` and the at-scale tests will report "deterministic" through register or memory divergence.
- HIGH (conc-09): the IPC proxy never matches responses to requests — `send_and_recv` (proxy_connection.cpp:74-88) ignores both `sequence_id` and `msg_type`; a single >5 s timeout leaves a stale response queued and permanently desynchronizes the channel, making every subsequent response off by one with silently wrong payloads. The dormant `HeartbeatMonitor` (heartbeat.cpp:36-72) would compound this by sending off-mutex.
- MEDIUM (conc-08): `legends_joystick_event` (legends_embed_api.cpp:2906-2956) writes joystick state directly into guest RAM (BDA 0x480/0x488) and then returns `LEGENDS_ERR_NOT_SUPPORTED` — state mutation on a reported failure; it also lacks the `in_step` guard and bypasses the sequenced input queue, breaking replay ordering.
- MEDIUM (conc-10): the cross-process audio ring violates SPSC — the writer mutates `read_index` on overflow (audio_ring.cpp:71-80) while the reader does an unsynchronized read-modify-write, causing lost updates and torn/duplicated audio; `open()` also trusts `header_->capacity_frames` from the shared region, enabling a divide-by-zero in the embedder.
- MEDIUM (conc-13): IPC runtime parity gap — `engine_host` never opens or writes the SHM framebuffer/audio regions the proxy creates, so IPC-mode `legends_capture_rgb` always returns 0 bytes with `LEGENDS_OK` (proxy_api.cpp:223-226), silently diverging from the in-process runtime.
- MEDIUM (conc-11): the TSan CI job is `allow_failure: true` (ci.yml:347-355) with known named races (`g_active_instance`, `CrashBreadcrumb::add()`); the gate was never re-tightened after the REQ-TH-004 mixer fixes landed, so new races land silently.
- Prior-finding status: M7 resolved (`dosbox_lib_get_context_ptr` now runs `LIB_CHECK_THREAD()`, dosbox_library.cpp:655-666); M3 substantially resolved via atomics/mutexes but vacuously, since library mode produces no audio at all; M1 narrowed but mount/unmount/joystick/Phase-3 setters still lack `in_step`; H2 mitigated by dual ContextGuards during step (legends_embed_api.cpp:1098, 1101); H3/H4/M10 remain open as deprecated dead paths recommended for deletion.
- TLA+ conformance at HEAD: 4 of the 5 NON-CONFORMANT invariants are fixed (handle consistency, null-handle, transactional text input), but `TLA_CONFORMANCE.md` still reports the stale 2026-02-24 numbers (33/49) — understating thread conformance while overstating determinism (`TraceDeterminism` marked CONFORMANT despite conc-07).
- ConfigValidation remains PARTIAL: `cpu_cycles` is range-validated (legends_embed_api.cpp:841-847) but `memory_kb` flows unchecked into `mc.memory_size` (line 871); `audio_rate` is still absent from `legends_config_t`.
- The legends-layer `EventQueueState` (instance_state.h:332-342) is serialized, restored, and hashed but has no producer anywhere — `EventCountPreserved`/`EventDigestPreserved` are vacuously conformant dead state.
- Determinism positives: no wall clock enters the step path, single-owner-thread is enforced at both layers, input is FIFO-drained with monotonic sequence numbers and hashed, and the engine-host IPC loop is single-threaded by construction; the two-instance and midpoint save/load test architecture is sound — only the oracle is weak.
- Suggested sprints: (1) make time real — compile a deterministic PIC/PIT event queue into library mode; (2) trustworthy oracle — GPRs/RAM into the hash, fix joystick, re-baseline docs; (3) IPC robustness — sequence matching, SPSC-correct ring, host-side frame publishing; (4) green TSan — fix named races and drop `allow_failure`.

## Covers

- [[Vacuous Interrupt Delivery (C2)]] — the C2 "fix" links a stub PIC, so no timer/IRQ events fire and device time never advances in library mode.
- [[Determinism Oracle Weakness]] — the Fast-mode state hash excludes GPRs/EIP/EFLAGS/segments and RAM, so all determinism verification can miss real divergence.
- [[Legends C API Layer]] — `in_step` guard coverage, transactional text input, joystick error-model violation, and `memory_kb` validation gap in legends_embed_api.cpp.
- [[Engine Bridge (DOSBox-X)]] — cpu_bridge step loop, stub-dependent cycle accounting, context-guard discipline, and the deprecated `MachineContext`/`dosbox_step` dead paths.
- [[IPC Runtime (Project Legends)]] — proxy lacks response-to-request matching (timeout desync), audio ring SPSC violation, and engine_host never publishes SHM framebuffer/audio.
- [[IPC Trust Boundary Gaps]] — `AudioRingBuffer::open()` trusts `capacity_frames` from the shared region, allowing a corrupted header to crash the embedder.
- [[Build & CI System (Project Legends)]] — `hardware/pic.cpp` absent from all CMake targets, TSan job allow-failure with named races, TLC runs on minimal specs only.
- [[Project Legends Test Suite]] — determinism test architecture (two-instance, midpoint save/load) is right-shaped but compares a weak hash; TSan races untriaged.
- [[Project Legends Documentation Corpus]] — TLA_CONFORMANCE.md (33/49, dated 2026-02-24) re-checked invariant by invariant at HEAD.
- [[Documentation Drift]] — conformance docs never re-baselined after fixes landed; stale claims understate threading and overstate determinism (conc-12).
- [[Prior-Audit Remediation Status]] — C2/H2/H3/H4/M1/M3/M7/M10 re-verified at HEAD: one resolved, two substantially/partially resolved, the rest confirmed open or vacuous.
