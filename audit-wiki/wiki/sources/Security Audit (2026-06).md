---
type: source
aliases: ["Security Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: Security Audit (2026-06)
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
  - "[[Save-State Load Path Overflow]]"
  - "[[IPC Trust Boundary Gaps]]"
  - "[[Prior-Audit Remediation Status]]"
  - "[[Documentation Drift]]"
---

# Security Audit (2026-06)

## Summary

A 2026-06-09 security and untrusted-input audit of Project Legends (115 commits after the 2026-02-24 prior audit) grading the codebase C overall. Save-state deserialization is well-hardened in both the legends layer and the engine bridge, while the new IPC / shared-memory isolation layer — the GPL trust boundary that runs untrusted guest code — lacks response validation, peer authentication, fuzzing, and verifiable isolation guarantees.

## Key takeaways

- Overall health grade C: save-state deserialization is the strongest surface; the IPC / shared-memory isolation layer (the MIT shell vs GPL engine-host trust boundary) is the weakest.
- SEC-01 (High) claimed shared-memory consumers trust attacker-controlled geometry fields, producing OOB reads in the trusted shell (src/legends_ipc/framebuffer_shm.cpp:74-92, src/legends_proxy/proxy_api.cpp:222-232, src/legends_ipc/audio_ring.cpp:10-16,63-110) — this finding was REFUTED by adversarial verification with high confidence.
- SEC-02 (Medium): the proxy never checks that a response's msg_type or sequence_id matches the request (src/legends_proxy/proxy_connection.cpp:74-88); an unsolicited EventNotification (0x1102) is consumed as the next response and desynchronizes the request/response stream, and a malicious host can forge a wrongly-typed payload read as a valid result.
- SEC-03 (Medium): IPC endpoints have no peer authentication and use predictable, world-reachable names — POSIX socket /tmp/legends_<pid>.sock with no SO_PEERCRED and shm_open without O_EXCL (src/legends_ipc/platform/posix/control_channel_posix.cpp:51-107, shared_memory_posix.cpp:57-67); Windows named pipe with default DACL, no FILE_FLAG_FIRST_PIPE_INSTANCE, no PIPE_REJECT_REMOTE_CLIENTS (control_channel_win.cpp:46-66); the handshake carries no token.
- SEC-04 (Medium): the IPC parsing layer — ~89 deserialize() functions in src/legends_ipc/messages.cpp (905 lines), the MessageCodec framing, and the 43-case dispatch() in src/engine_host/engine_dispatcher.cpp — is entirely unfuzzed despite parsing untrusted bytes at the GPL trust boundary.
- SEC-05 (High): GPL process-isolation guarantees are unverified — CI has no REQ-ISO-016 GPL symbol-isolation scan (ci.yml:121-124 only checks the binary exists), no REQ-ISO-013 crash detection/recovery in the host main loop, and the engine host never opens the framebuffer/audio SHM, so the write path is unwired (src/engine_host/main.cpp:20-108).
- SEC-06 (Low): MountDriveReq serializes the path length as a single byte while copying the full path, silently truncating paths over 255 bytes (src/legends_ipc/messages.cpp:341-359) — risky because the mount path feeds REQ-SEC-023 path confinement.
- IPC mode is opt-in (LEGENDS_USE_IPC=OFF by default), bounding present-day exposure, but it is the stated roadmap direction and these findings block it from being a real security boundary.
- Save-state load (reachable in the default in-process build) is well-hardened: magic/version/CRC32 validation, underflow guards, overflow-safe subtraction-form bounds macros, per-count caps, pre-validation of input events, four-phase atomic load (src/legends/legends_embed_api.cpp:2291-2428, 706-724).
- Engine-side V5 load is similarly validated with bounded RLE decode into fixed-size RAM/VRAM, and that path is fuzzed (engine/src/misc/dosbox_library.cpp:1106-1167, 1409-1487).
- Prior findings: H6 (integer overflow in memory bounds) RESOLVED at dosbox_library.cpp:1723,1747; H9 (unaligned reinterpret_cast) RESOLVED in the load path; H7 (HashMode::Full) only PARTIALLY RESOLVED — it now hashes conventional RAM (state_hash.cpp:300-303) but still omits VGA registers/VRAM and device state.
- Documentation drift: TODO.md:19,257 still calls IPC isolation "STUB ONLY" and roadmap.md:3319-3332 marks REQ-ISO-003…016 Missing, yet the transport mechanism is substantially built — the docs understate the code while overstating the guarantees.
- Sprint recommendations: harden the SHM boundary and proxy response matching, authenticate/lock down IPC endpoints, fuzz the IPC surface via MessageCodec + dispatch(), and make isolation verifiable with a symbol-scan CI gate, crash recovery, and a finished SHM write path.

## Covers

- [[Legends C API Layer]] — legends_load_state validation (header, magic, CRC32, overflow-safe section bounds) and the legends_capture_rgb two-call pattern in proxy_api.cpp.
- [[IPC Runtime (Project Legends)]] — the 108-message/89-struct codec, 43-case dispatcher, and SHM channels; 64 MB payload cap is the main existing guard.
- [[Engine Bridge (DOSBox-X)]] — engine V5 save-state load validation, bounded RLE decode, and the fixed memory-bounds checks in dosbox_library.cpp.
- [[Build & CI System (Project Legends)]] — CI builds and unit-tests IPC mode but lacks the REQ-ISO-016 GPL symbol-isolation scan gate.
- [[Project Legends Test Suite]] — four fuzz targets cover save-state/input/config but none touch the IPC surface; IPC unit tests use only well-formed inputs.
- [[Save-State Load Path Overflow]] — the prior overflow exposure in the load path is closed by subtraction-form macros and a four-phase atomic load.
- [[IPC Trust Boundary Gaps]] — SEC-02/03/05: no response type/sequence validation, no peer authentication, unverified isolation; IPC mode is not yet a trustworthy boundary.
- [[Prior-Audit Remediation Status]] — H6 and H9 resolved, H7 partially resolved (VGA/VRAM/device state still unhashed).
- [[Documentation Drift]] — TODO.md and roadmap.md understate the built IPC mechanism while overstating its guarantees.
