---
type: source
aliases: ["Memory Safety Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: Memory Safety Audit (2026-06)
authors: [Claude audit fleet]
url:
publisher:
published: 2026
accessed: 2026-06-09
source_type: report
covers:
  - "[[Legends C API Layer]]"
  - "[[Engine Bridge (DOSBox-X)]]"
  - "[[Save-State Load Path Overflow]]"
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Prior-Audit Remediation Status]]"
---

# Memory Safety Audit (2026-06)

## Summary

Memory-safety and C++ correctness audit of Project Legends' wrapper layer and engine boundary at commit ef11f20 (2026-06-09), assigning health grade C. It verifies the prior backlog (H5, H6, H9, M7, M8, M9, M11, C2) as genuinely resolved, but finds a new CRITICAL heap buffer overflow reachable from the public legends_load_state() API and a HIGH engine-handle leak that permanently bricks the library, both in the recently expanded save/load path.

## Key takeaways

- Health grade C: strong remediation of the old backlog, but one critical corruption bug and one library-bricking leak are open in the very paths that were recently expanded (executive summary).
- mem-01 (CRITICAL): dosbox_lib_load_state trusts the attacker-controlled memory.size field and writes it into ctx->memory.size with no validation (dosbox_library.cpp:1300-1319, esp. :1303); EngineStateMemory.size is a uint64_t (engine_state.h:265).
- ctx->memory.base is a fixed bytes+65536 allocation made once at create time (dosbox_context.cpp:39-41) with no separate capacity field, so once memory.size is overwritten the true allocation size is lost.
- The RAM sub-block decodes into ctx->memory.base using the corrupted size as the cap (dosbox_library.cpp:1437-1450; zero_rle.h:84-117); because the codec is RLE, a tiny crafted blob writes hundreds of MB past a ~704 KB allocation.
- Reachability is real: legends_load_state() forwards the engine slice unmodified after only bounds-checking the legends buffer (legends_embed_api.cpp:2442-2449); integrity is plain CRC32 not a MAC (dosbox_library.cpp:1129-1136; legends_embed_api.cpp:2332-2338) so checksums are trivially forged.
- Same root cause yields secondary wild writes even with no RAM blob: dosbox_lib_reset memsets at base+corrupted_size (dosbox_library.cpp:522-527) and read/write bounds checks (1723, 1747) now compare against the corrupted size, exposing the whole heap.
- mem-02 (HIGH): legends_create's terminal catch deletes the wrapper but never destroys an already-created engine handle (legends_embed_api.cpp:951-957), leaking it and leaving g_instance_exists true.
- The leaked engine becomes a zombie: the next legends_create() fails permanently with DOSBOX_LIB_ERR_ALREADY_CREATED until process restart (dosbox_library.cpp:360-363); the catch also lacks a catch(...) arm, so a non-standard throw escapes the extern "C" boundary (UB).
- mem-03 (MEDIUM): M6 is still half-open — fire_event invokes embedder callbacks with no try/catch (legends_embed_api.cpp:744-749) and is called from legends_mount_drive/legends_unmount_drive across the C ABI without surrounding guards (2809/2814, 2841/2846).
- mem-04 (MEDIUM): cross-layer load atomicity gap — the engine is committed in Phase 2 before wrapper staging, where staged_indexed_pixels.resize can throw bad_alloc and return without reverting the engine (legends_embed_api.cpp:2435-2509; same shape in the V2 loader at 2228-2237).
- mem-05 (LOW): V3 sections are written by raw memcpy of padded structs — ScheduledEvent (sizeof 24, instance_state.h:303-310), SaveStateTime/CPU/PIC/FrameHeader (legends_embed_api.cpp:1889-1967) — so indeterminate padding is CRC32-covered and the format is non-portable across ABIs.
- Prior findings re-verified at HEAD: H5, H6, H9, M7, M8, M9, M11 and C2 are all resolved, and the resolutions are real not cosmetic (prior-finding table, lines 44-52).
- C2 resolved: execute_cycles now calls PIC_RunQueue() before the decoder and CPU_Check_NMI() after (cpu_bridge.cpp:113-119).
- Solid areas: bounds-validation macro discipline in the wrapper loader (VALIDATE_SECTION_BOUNDS etc.), single-instance atomic-CAS lifecycle with thread-affinity-checked destroy, and the 64KB 0xF4 guard region after guest RAM (dosbox_context.cpp:39-44).

## Covers

- [[Legends C API Layer]] — wrapper layer (legends_embed_api.cpp) audited for create error-path safety, load-state staging, unguarded callback invocation across the C ABI, and padded-struct serialization.
- [[Engine Bridge (DOSBox-X)]] — dosbox_library/cpu_bridge/dosbox_context deserializer overwrites the live allocation descriptor verbatim from untrusted input, the root of the critical overflow and secondary wild writes.
- [[Save-State Load Path Overflow]] — mem-01 CRITICAL: attacker-controlled memory.size drives an RLE decode whose cap is the corrupted size, writing far past a ~704 KB allocation.
- [[Vacuous Interrupt Delivery (C2)]] — C2 verified resolved; execute_cycles now runs the PIC queue before the decoder and checks the NMI afterward.
- [[Prior-Audit Remediation Status]] — eight prior findings (H5, H6, H9, M7, M8, M9, M11, C2) re-verified as genuinely, not cosmetically, fixed at commit ef11f20.
