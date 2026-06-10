# Backlog & Prior-Audit Verification Report

**Role:** Backlog miner / prior-audit verifier
**Audit date:** 2026-06-09
**Baseline:** AUDIT.md (2026-02-24, 30 findings: C1-C2, H1-H9, M1-M11, L1-L8)
**Also mined:** AUDIT_REPORT.md (2026-03-20), TODO.md (2026-02-27), tlaAudit.md (2026-02-27), TLA_CONFORMANCE.md (2026-02-24), CIFix.md (2026-06-08), REFACTORING_CHANGELOG.md (2026-01-15), CHANGELOG.md, roadmap.md/ROADMAP.md (v4.1.0)
**HEAD:** `ef11f20` (2026-06-09), 115 commits since 2026-02-24, master ahead of origin/master by 1

---

## 1. Executive Summary

The prior audit backlog has been **substantially burned down**: 22 of 30 AUDIT.md findings are verifiably resolved at HEAD, including both criticals (C1 header duplication, C2 missing PIC_RunQueue/NMI) and 7 of 9 highs. The fixes are real, carry traceable comments (`// C2 fix`, `(M8)`, `(M9)`, `DEPRECATED(M10)`), and most map to specific commits. A second, larger audit wave (AUDIT_REPORT.md, 2026-03-20, 12+10 agents) drove a March remediation sprint that fixed the CRC-32 table, IPC payload cap, SDL races, config field limits, prompt-injection separation, and more.

The **paper trail itself is now the weak point**. Four documentation-of-record defects were found: (1) `ROADMAP.md` and `roadmap.md` are *both* tracked in git with case-colliding names — the source-verified 427-line ROADMAP from March (commit `8e3b0b0`, which fixed "major factual errors") was clobbered back to a 4,061-line document in June (commit `1dd76b4`) whose own changelog stamp still says v4.1.0/2026-02-25; (2) TODO.md is 3.5 months stale and internally contradictory; (3) CHANGELOG.md claims "TLS verification" while no HTTP/TLS transport exists anywhere; (4) AUDIT.md records none of the 22 resolutions, inviting duplicate work.

Verified-open prior findings: **H2, H3, H4 (+M5), H7 (narrowed), M4, M10, L1, L3** — none critical, mostly accepted-design or hygiene debt.

---

## 2. What Actually Changed Since 2026-02-24 (git-log map)

115 commits. Major waves, oldest first:

| Wave | Representative commits | Content |
|---|---|---|
| Phase -1 engine I/O plumbing | `7c5321d`, `bfa0f8e` | Real VRAM/framebuffer sync, font, audio path (kills H8) |
| Phase 0-4 app shell build-out | `ec22c0d`, `e842094`, `8f46bbb`, `e779c86`, `4478a01`, `5195049` | SDL3 executable, menus, save slots, capture, AI panel, mapper, packaging |
| Audit quick wins | `d59eaf2`, `dfbad8b`, `1bdf92b` | `legends_force_destroy`, destroy/text_input fixes (H5, M2, L8), bridge hardening |
| Release A + GPL isolation | `8e78bfe`, `d32bbe4`, `8e46c2d`, `0de44cd`, `3e73565` | Security baseline, mount API, IPC library + engine host + proxy, IPC CI job |
| March remediation sprint (AUDIT_REPORT follow-up) | `099b054` (CRC-32), `bfe3271`/`15c1a10` (IPC payload cap), `a6a0f00` (SDL races), `07a2c6b`/`56dee93` (config limits, prompt injection), `0660eb3` (AI sanitization), `7275c8e` (API-key detection), `3708ea6` (FAT depth), `7f86dd7` (stubs return NOT_SUPPORTED), `1de7e80`/`4b4c43b`/`e14629e` (shader/joystick/TTF wiring), `8434561` (boot test) | Fixes for all 8 "critical bugs" and most of the 7 overstated REQ-SECs from AUDIT_REPORT.md |
| Phase 3 serialization | `faababd` | V5 save format: CPU GPRs, zero-RLE RAM, VRAM, VGA registers (kills H1) |
| C++23/gsl modernization | `4e96754`, `828f4ef`, `df7edc7`, `a19faeb`, `45d9ba9`, `64feede`, `ca44f1a` | `[[nodiscard]]` x53 headers, string_view/from_chars, gsl_Expects/narrow, constexpr wire format, overlay_render dedup — directly executes AUDIT_REPORT §14.4 items 1,3,5,6,8,9,14,20 |
| RuntimeHost adoption + Graphify | `1dd76b4`, `757255e`, `9fa3125`, `6900e7a`, `274ef4d` | RuntimeHost service layer, IPC parity work, graph tooling (June) |
| CI stabilization (CIFix.md) | `46e6bd5`, `8fdd4c6`, `911692f`, `82e65fc`, `f128e6a` | Lane split (primary vs optional), determinism fix, MSVC /wd4834 containment |

---

## 3. Verification of All 30 Prior Findings (AUDIT.md 2026-02-24)

### Critical

| ID | Finding | Status at HEAD | Evidence |
|----|---------|----------------|----------|
| **C1** | 27+ duplicated header pairs `include/legends/` vs `engine/include/aibox/` compiled into separate libs | **RESOLVED** | All 25 overlapping headers in `include/legends/` are now 4-7 line forwarding headers, e.g. `include/legends/machine_context.h:1-7` (`// Forwarding header: legends -> aibox unification`, `#include <aibox/machine_context.h>`). `src/legends/` contains only `legends_embed_api.cpp` + `internal/`; the implementation sources (`llm_*.cpp`, `vision_*.cpp`, etc.) exist only in `engine/src/aibox/`. Residual: `namespace legends { using namespace aibox; }` in public headers (flagged as 25 violations in AUDIT_REPORT §14.2). |
| **C2** | CPU bridge skips `PIC_RunQueue()` / `CPU_Check_NMI()` | **RESOLVED** | `engine/src/misc/cpu_bridge.cpp:113` (`if (PIC_RunQueue()) result.events_processed++;` — comment "Process pending PIC events before CPU execution (C2 fix)") and `:119` (`CPU_Check_NMI(); // Check for NMI after execution (C2 fix)`). |

### High

| ID | Finding | Status | Evidence |
|----|---------|--------|----------|
| **H1** | CPU GPRs, VGA hardware state, RAM not serialized | **RESOLVED** | Commit `faababd` (2026-03-15). `engine/include/dosbox/engine_state.h:393-403` `EngineStateCpuGpr` (8 GPRs, EIP, EFLAGS, 6 segment regs val/phys/limit, 104 B, static_assert); `:700-716` `ENGINE_STATE_SIZE_V5_BASE == 792` + dynamic V5 sub-blocks; `engine/src/misc/dosbox_library.cpp:716-733` adds VGA_REG + zero-RLE VRAM/RAM sub-blocks. Residual gap (out of H1 scope): engine event-scheduler queue still not serialized (SaveStateTest `EventCountPreserved` stays PARTIAL). |
| **H2** | Two unsynchronized `g_current_context` thread-locals (aibox + dosbox layers) | **CONFIRMED OPEN** | `engine/src/aibox/machine_context.cpp:20` (`thread_local MachineContext* g_current_context`) and `engine/src/misc/dosbox_context.cpp:65` (`thread_local dosbox::DOSBoxContext* g_current_context`) both still exist. TODO.md "Engine-Level Technical Debt" tracks "Eliminate thread-local current_context() accessors" as open. Mitigated by `ContextGuard` dual-set during step scope. |
| **H3** | `MachineContext::step()` is a no-op counter stub | **CONFIRMED OPEN (deprecated, contained)** | `engine/src/aibox/machine_context.cpp:229` — `// No real CPU execution — counter increment only (see deprecation note)`. Real execution goes through `cpu_bridge`. The stub path is now documented and only reachable via deprecated `dosbox_step()` (see M10). |
| **H4** | 7 `init_*` methods are stubs | **CONFIRMED OPEN (accepted design)** | `engine/src/aibox/machine_context.cpp:376-378`: `// H4/M5: These init stubs delegate to DOSBox-X engine bridge... intentional no-ops.` All 7 (`init_pic/pit/vga/input/sound/dos/bios`, lines 380-419) return `Ok()` unchanged. Reclassified by the team from defect to design decision; the dead-interface debt remains. |
| **H5** | `legends_destroy()` fallback destroys active instance on any non-null handle | **RESOLVED** | `src/legends/legends_embed_api.cpp:79-82` — `get_instance()` strict-matches `handle == inst`; `:966-969` destroy returns `LEGENDS_ERR_NULL_HANDLE` on mismatch; explicit `legends_force_destroy()` escape hatch at `:998-1003` (commit `d59eaf2`). |
| **H6** | Integer overflow in memory bounds checks (`address + size` wrap) | **RESOLVED** | `engine/src/misc/dosbox_library.cpp:1722-1725` and `:1747-1750` use subtraction form: `if (size > g_context->memory.size \|\| address > g_context->memory.size - size)`. |
| **H7** | `HashMode::Full` contract mismatch (only appended `"FULL_MODE"` string) | **PARTIALLY RESOLVED — OPEN (narrowed)** | `engine/src/misc/state_hash.cpp:300-303` now hashes full conventional memory (`builder.update(ctx->memory.base, ctx->memory.size)`), but the comment says "VGA and device state will be added in Phase B" while the public header `engine/include/dosbox/state_hash.h:40-47` still promises "all of fast mode plus memory, VGA state, device state". Contract still overstates by VGA + devices. |
| **H8** | Frame capture decoupled from engine (synthetic test pattern only) | **RESOLVED** | `src/legends/legends_embed_api.cpp:1626-1700+` `sync_state_from_engine()` now syncs display mode (`dosbox_lib_get_display_info`, comment "(H8)"), 256-color palette, text buffer, font data, and framebuffer (Phase -1 REQ-PLUMB-001/002). Test pattern retained only as headless fallback when engine returns NOT_SUPPORTED/zeros. |
| **H9** | Unaligned `reinterpret_cast` on caller buffers in save/load | **RESOLVED** | Only one `reinterpret_cast` remains in the whole file (`legends_embed_api.cpp:1003`, a handle cast). Save/load uses portable little-endian byte-shift read/write helpers (declared around `:95-100`). |

### Medium

| ID | Finding | Status | Evidence |
|----|---------|--------|----------|
| **M1** | Reentrancy guard only on step functions | **RESOLVED** | `in_step` early-return added to mutating APIs: `legends_reset` (`legends_embed_api.cpp:1010`), `legends_key_event` (:1509), `legends_key_event_ext` (:1527), `legends_text_input` (:1544), `legends_mouse_event` (:1599), save_state (:1854), load_state (:2287). |
| **M2** | `legends_text_input` partial commit on queue-full (stuck shift) | **RESOLVED** | `legends_embed_api.cpp:1555-1558`: `size_t slots_needed = mapping.needs_shift ? 4 : 2; if (available < slots_needed)` → `BUFFER_TOO_SMALL` before queueing any event of the character. |
| **M3** | `MixerState` callback-thread access unsynchronized | **RESOLVED** | `engine/include/dosbox/dosbox_context.h:459-460`: `std::atomic<uint32_t> work_in` / `work_out` for producer/consumer ring positions, with `[CALLBACK]` annotations (commit `ddf04b6` "mixer thread safety"). Volume floats remain plain (read-mostly; acceptable residual). |
| **M4** | 30-40 mutable extern globals untracked in migration registry | **CONFIRMED OPEN (narrowed)** | `engine/globals_registry.yaml` now tracks 70 entries (was 45+) incl. `CPU_Cycles`/`CPU_CycleLeft` (lines 36, 49), but engine headers still expose unregistered mutable externs: `engine/include/cpu.h` 26 externs, `bios.h` 19, `callback.h` 4. Low residual risk; vendored-engine boundary. |
| **M5** | 7 forward-declared classes with no definitions | **CONFIRMED OPEN** | `engine/include/aibox/machine_context.h:34-40` still forward-declares `VgaContext`, `DosKernel`, `PicController`, `PitTimer`, `KeyboardController`, `MouseController`, `SoundSubsystem`; no definition exists anywhere (`grep "class VgaContext"` matches only the forward decl). Cosmetic — tied to the accepted H4 design. |
| **M6** | Log callback not exception-safe at C ABI boundary | **RESOLVED** | `src/legends/internal/instance_state.h:50-56`: `log()` wraps the callback invocation in `try { callback(...) } catch (...) {}`. |
| **M7** | `dosbox_lib_get_context_ptr()` bypasses `LIB_CHECK_THREAD()` | **RESOLVED** | `engine/src/misc/dosbox_library.cpp:655-666`: function now calls `LIB_VALIDATE_HANDLE` + `LIB_CHECK_THREAD()` (line 660). |
| **M8** | Engine handle validation null-only | **RESOLVED** | `dosbox_library.cpp:118-121` `LIB_VALIDATE_HANDLE` requires exact `HANDLE_SENTINEL` match (`DOSBOX_LIB_ERR_INVALID_HANDLE` otherwise), applied across the API (lines 436, 504, 548, 614, ...). |
| **M9** | Config string dangling pointers (no deep copy) | **RESOLVED** | `dosbox_library.cpp:380-394`: `g_config = *config` followed by deep copies into `g_config_path_owned` / `g_working_dir_owned` (`std::string` at :60-61), comment "Deep-copy string fields so caller can free originals (M9)". Same pattern in legends layer (`legends_embed_api.cpp:849-857`). |
| **M10** | Dual runtime path: `dosbox_step()` routes through stub, `dosbox_lib_step_cycles()` real | **CONFIRMED OPEN (mitigated)** | `engine/src/misc/dosbox_context.cpp:973-976`: `// DEPRECATED(M10): Routes through MachineContext::step() which is a counter-incrementing stub. Production code uses dosbox_lib_step_cycles() instead. Only called from test_dosbox_context.cpp. Will be removed in a future pass.` Path still compiles and is exported in `dosbox_context.h:99`. REQ-LC-005 ("no alternative stub path shall exist") remains a GAP until removal. |
| **M11** | `legends_step_cycles()` ignores `dosbox_lib_get_context_ptr()` return | **RESOLVED** | `legends_embed_api.cpp:1087-1089`: `auto ctx_err = dosbox_lib_get_context_ptr(...); if (ctx_err != DOSBOX_LIB_OK \|\| raw_ctx == nullptr)` → error before the `static_cast` at :1097. |

### Low

| ID | Finding | Status | Evidence |
|----|---------|--------|----------|
| **L1** | README documents ~18 of 22 API functions | **CONFIRMED OPEN — WORSE** | API grew to **50** functions (`grep -oE "legends_[a-z0-9_]+\(" include/legends/legends_embed.h \| sort -u` = 50); README.md mentions only ~31 distinct `legends_*` identifiers; **27 of 50 functions are not mentioned at all**. |
| **L2** | 3 error codes never used (`REENTRANT_CALL`, `IO_FAILED`, `NOT_SUPPORTED`) | **RESOLVED** | `REENTRANT_CALL` returned at 7+ sites (e.g. `legends_embed_api.cpp:1010`); `IO_FAILED` at :2777, :2782; `NOT_SUPPORTED` at :2805, :2837, :2872, ... (commit `7f86dd7` made stubs return it). |
| **L3** | `HandleRegistry` implemented but unused | **CONFIRMED OPEN** | Only consumers are tests (`tests/unit/test_handle_registry.cpp`, `test_gsl_contracts.cpp`, `test_thread_safety.cpp`); zero references in `src/legends/legends_embed_api.cpp`. Dead production code. |
| **L4** | `LEGENDS_ERROR` macro collision (error.h vs embed API) | **RESOLVED** | Repo-wide grep finds exactly one definition site: `legends_embed_api.cpp:688-690` (the `#undef` is now defensive); `engine/include/aibox/error.h` no longer defines it. |
| **L5** | `project_legends` target unbuildable (no main.cpp) | **RESOLVED** | `src/main.cpp` exists; Phase 0 REQ-BUILD-001/002 complete (TODO.md, roadmap §4); SDL3 executable built in CI. |
| **L6** | `check_gsl_lite_usage.py` false positives from generated dirs | **RESOLVED** | `scripts/check_gsl_lite_usage.py:207`: `exclude_dirs = ['build', 'build_test', 'cmake-build', 'third_party', 'vendor', 'external', '_deps']`. |
| **L7** | `pyyaml` undeclared (no requirements-dev.txt) | **RESOLVED** | `C:\projectLegends\requirements-dev.txt` exists, content `pyyaml>=6.0`. |
| **L8** | Tests pass `(void*)0xDEAD` to destroy and expect success | **RESOLVED** | No `0xDEAD` destroy-sentinel pattern remains in `tests/unit/` (remaining `0xDEADBEEF` hits are version/exception test constants); commit `dfbad8b` updated the sentinel destroy pattern. |

**Tally: 22 resolved, 8 open** (H2, H3, H4+M5, H7-narrowed, M4, M10, L1, L3 — counting H4/M5 together: 9 IDs open).

---

## 4. New Findings (documentation of record)

### N1 (high): Case-colliding duplicate roadmaps; source-verified ROADMAP clobbered

- `git ls-files | grep -i roadmap` returns **both** `ROADMAP.md` and `roadmap.md`, identical 209,189-byte blobs at HEAD (`git cat-file -s HEAD:ROADMAP.md` == `HEAD:roadmap.md`; `git diff HEAD:ROADMAP.md HEAD:roadmap.md` is empty).
- History: commit `8e3b0b0` (2026-03-15) **deleted** the 4,061-line `roadmap.md` and created a 427-line source-verified `ROADMAP.md`, explicitly "Correct[ing] major factual errors" (API count 50 not 22, save format V3 not V4, REQ-SEC-024 not implemented, GPL IPC partially implemented, 24 REQUIREMENTS GAP items). Commit `18c1cf3` refined it. Then commit `1dd76b4` (2026-06-08) re-expanded `ROADMAP.md` by +3,994/-360 lines back to the 4,061-line v4.1.0-style document — and `roadmap.md` reappears as a second tracked path.
- The current document's own changelog ends at "v4.1.0 (2026-02-25)" (`roadmap.md:3845-3847`) despite June edits — the version stamp is false.
- On case-insensitive filesystems (Windows is the primary dev platform per CIFix.md), two tracked paths differing only in case cause nondeterministic checkouts and silent clobbering — almost certainly how the March corrections were lost.
- **Fix (S):** delete one path (`git rm --cached roadmap.md`), reconcile content against the March source-verified version, bump the internal changelog, add a CI check for case-colliding tracked paths.

### N2 (high): CHANGELOG.md claims TLS verification; no TLS/HTTP transport exists

- `CHANGELOG.md:36-38` (Unreleased/Added): "**Security hardening**: TLS verification, API key protection, config field limits, ...".
- `src/app/ai_http_client.cpp:212`: `// Actual thread creation deferred to application wiring (libcurl optional).` — the only TLS/SSL/https/curl reference in the AI HTTP client; there is no transport layer, so REQ-SEC-005 (TLS verification) cannot be satisfied. AUDIT_REPORT.md §4 flagged exactly this on 2026-03-20 ("HTTP client has no transport layer — no TLS code exists anywhere"); it is still true at HEAD while the user-facing changelog asserts the opposite.
- Other March security fixes are real (API-key detection `7275c8e`, AI response sanitization `0660eb3`, config field limits `07a2c6b`, FAT depth `3708ea6`), which makes the one false claim more likely to be trusted.
- **Fix (S):** reword CHANGELOG (and roadmap REQ-SEC-005 status) to "planned/deferred", or actually wire libcurl with certificate verification before Release A.

### N3 (medium): TODO.md is 3.5 months stale and internally contradictory

- `TODO.md:3` "Last updated 2026-02-27". Since then: GPL isolation layer landed (`8e46c2d`, `0de44cd`), V5 RAM/VGA/GPR serialization (`faababd`), Release A sprints, RuntimeHost adoption, CI restructure — none reflected.
- Header table (`TODO.md:18-21`) says Security Hardening 6/22, **GPL v2 Process Isolation 2/16 "STUB"**, Wasm 0/50, UX 2/11. AUDIT_REPORT.md §1 (three weeks later) measured GPL isolation at **12-13/16**; at HEAD `src/legends_ipc/` (message codec, SHM framebuffer, audio ring, control channel), `src/engine_host/` (dispatcher), `src/legends_proxy/` all exist with CI coverage (`3e73565` Linux IPC job).
- Internal contradiction: `TODO.md:90` marks `REQ-MOUNT-001 — Host directory mounting` complete (Phase 2, with `mount_manager.cpp` + `legends_mount_drive`), while `TODO.md:168` lists the same `REQ-MOUNT-001` under "Not Yet Implemented — Must-Have (Release Blockers)". Same for REQ-MOUNT-002, REQ-MENU-001, REQ-MAPPER-001, REQ-SAVE-003, REQ-CAPTURE-003 (all appear both as `[x]` complete and as missing).
- **Fix (S):** regenerate TODO.md from the verification matrix, or retire it in favor of the single reconciled ROADMAP (see N1).

### N4 (medium): IPC protocol stub + proxy parity gaps contradict "GPL isolation complete" narrative

- `src/legends_ipc/protocol.cpp:1`: `// Stub — not yet implemented` (the high-level protocol state machine; wire format/messages are real).
- `src/legends_proxy/proxy_api.cpp` returns `LEGENDS_ERR_NOT_SUPPORTED` for 6 APIs in IPC mode: video capture start/stop/query (:452-454), `legends_set_ttf_font` (:571), `legends_register_event_callback` (:675), plus :425. CIFix.md (2026-06-08) confirms: "several proxy C ABI functions still return `LEGENDS_ERR_NOT_SUPPORTED`".
- roadmap.md §14 says "GPL v2 Process Isolation — MOSTLY COMPLETE"; CHANGELOG claims a complete "IPC protocol". Embedders choosing IPC mode for license isolation silently lose video capture, TTF, and event callbacks.
- **Fix (M):** finish proxy parity for the 6 gaps (or document the IPC-mode capability matrix in legends_embed.h), implement or delete protocol.cpp.

### N5 (low): AUDIT.md never updated with resolution status

- AUDIT.md still presents all 30 findings as the current state ("Top Findings by Severity") with no resolution annotations, although 22 are fixed — several with code comments referencing the very finding IDs (C2, H4/M5, M8, M9, M10). The EARS table (§6) still shows 24 GAP/4 PARTIAL of 50 REQs; by this verification the GAP count is now roughly 8. Anyone triaging from AUDIT.md alone would re-fix solved problems (and the March AUDIT_REPORT does not cross-reference the Feb IDs).
- **Fix (S):** append a "verified 2026-06-09" resolution column (this report supplies the evidence), or supersede AUDIT.md with the audit-wiki.

### Positive verification notes

- tlaAudit.md P0 backlog has been executed: `spec/tla/Composition.tla:272-293` now uses real `INSTANCE` composition (LifecycleMinimal/Threading/PAL/Determinism/SaveState/Capture); `APIContract.tla:6` asserts "Every gate has a SUBSTANTIVE formula -- no TRUE stubs remain"; 26 `.cfg` files exist (was 11 in CI) and ci.yml runs SchedulerMinimal/SchedulerTest (`.github/workflows/ci.yml:623-633`).
- `cpu_cycles` validation (TLA ConfigValidation quick win) landed: `legends_embed_api.cpp:841-847` rejects out-of-range values (0=auto, else 100..1,000,000).
- CIFix.md work is in place: workflows split into primary vs optional lanes, determinism failure fixed, `/wd4834` contained to test targets, 4,497 local tests passing per its log.

---

## 5. Roadmap Gap Summary → Candidate Sprint Themes

Measured against roadmap.md v4.1.0 sections (statuses cross-checked vs code where feasible):

1. **Security Hardening completion (roadmap §9, ~6-10 of 22 REQ-SECs still open).** March sprint closed SEC-006/008/014/016/018 and SEC-040; still open: SEC-005 (TLS — no transport, N2), SEC-023/024 (canonical path resolution + read-only mounts; `8e3b0b0` commit message: "REQ-SEC-024: not implemented (flag defined, no logic)"), SEC-031 (threat model doc), SEC-035/036 (code signing, checksum publication), SEC-038/039 (shader/SoundFont validation, deferred to Release B). Theme: "Security claims become security facts" — fix or re-label every overstated REQ-SEC, then gate G5.
2. **GPL Process Isolation parity (roadmap §14, "MOSTLY COMPLETE" but parity-gapped).** Close the 6 proxy NOT_SUPPORTED gaps, implement/delete `protocol.cpp`, add reconnection logic, keep the Linux IPC CI lane green, publish an IPC-mode capability matrix. This is the project's GPL-compliance load-bearing wall (RISK-019: High/Critical).
3. **Wasm Sandbox (roadmap §15, 0/50, unchanged since Feb).** Only `LEGENDS_BUILD_WASM` CMake option (CMakeLists.txt:38) and WIT docs exist. Decision sprint needed: commit to a thin REQ-WASM-001..010 spike or formally defer the section to Release C — carrying 50 unstarted requirements in the active roadmap distorts every completion metric.
4. **Engine-layer debt + docs-of-record closure.** Remove deprecated `dosbox_step()`/`MachineContext::step()` counter path (H3/M10), unify or formally bless the dual `g_current_context` (H2), add VGA/device hashing to `HashMode::Full` or fix the header contract (H7), regenerate README API docs (27/50 functions missing, L1), delete dead `HandleRegistry` or adopt it (L3), and execute N1/N3/N5 (single source-of-truth roadmap, fresh TODO, annotated AUDIT). UX/Accessibility (roadmap §13, ~2-3/11 done) items REQ-UX-001/002/005/008/009/010 fold naturally into this Release-B polish lane.

---

## 6. Suggested Disposition Table (for the synthesis agent)

| Prior ID | Verdict | Carry forward as |
|----------|---------|------------------|
| C1, C2, H1, H5, H6, H8, H9, M1, M2, M3, M6, M7, M8, M9, M11, L2, L4, L5, L6, L7, L8 | Resolved | Close in record |
| H2 | Open | medium / L (architectural unification or documented blessing) |
| H3 + M10 | Open, mitigated | low / S (delete deprecated path + test migration) |
| H4 + M5 | Open, accepted design | low / S (delete dead interface or document permanently) |
| H7 | Open, narrowed | medium / M (VGA+device hashing or contract fix) |
| M4 | Open, narrowed | low / M (registry sweep of engine headers) |
| L1 | Open, worse | low / S (doc generation from header) |
| L3 | Open | low / S (delete or adopt) |
| N1-N5 | New | see §4 |
