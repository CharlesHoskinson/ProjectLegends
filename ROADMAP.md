# ProjectLegends Roadmap

## Project Status (verified 2026-03-15)

| Item | Value |
|------|-------|
| Commit | `a0ad97b` |
| API | 50 exported functions in `legends_embed.h` (48 implemented, 2 stubs: `legends_start_video_capture`, `legends_stop_video_capture`) |
| Tests | 215 files (199 active, 16 GTEST_SKIP stubs) |
| Contract gates | 23 (enforced by `test_contract_gates.cpp` + TLA+) |
| TLA+ specs | 33 files, 17 model-checked in CI |
| Platforms | Windows (MSVC, MinGW), macOS, Linux (GCC, Clang) |
| Save format | API: V3 (Unified Input Queue); engine defines V5 struct |
| REQUIREMENTS.md | 50 EARS requirements: 26 OK, 24 GAP |

### Test Breakdown

| Category | Files | Active | Stubs |
|----------|-------|--------|-------|
| Unit tests (top-level) | 118 | 118 | 0 |
| Integration tests | 35 | 19 | 16 |
| Fuzz targets | 4 | 4 | 0 |
| Engine unit tests | 58 | 58 | 0 |
| **Total** | **215** | **199** | **16** |

### Integration Test Stubs (16 GTEST_SKIP)

Full stubs ("Not yet implemented"):
`test_boot_to_prompt`, `test_cross_platform_smoke`, `test_determinism_hash`,
`test_frame_timing`, `test_golden_visual`, `test_pairwise_config`,
`test_replay_determinism`, `test_save_state_compat`, `test_visual_regression`

Conditional skips (runtime/environment checks):
`test_audio_validation` (headless), `test_event_callbacks` (mount unsupported),
`test_full_lifecycle` (concurrent instances), `test_ipc_integration` (engine host not found),
`test_mount_lifecycle` (mount unsupported), `test_soak_endurance` (env var gated),
`test_video_capture_lifecycle` (backend unwired)

---

## Release Sequence

```
v0.1.0-alpha.1   Tag current master
v0.1.0-beta.1    Safety + serialization foundation
v0.1.0-rc.1      Full serialization + security hardening
v1.0.0            All blockers resolved
```

---

## v0.1.0-alpha.1 — Tag Current Master

**Goal:** Establish a baseline tag. Everything currently on `master` ships as-is.

### What's Included

| Area | Status | Evidence |
|------|--------|----------|
| Core C API (50 functions) | 48 implemented, 2 stubs | `legends_embed.h` — full function list |
| CPU execution via cpu_bridge | Complete | `cpu_bridge.cpp` — PIC_RunQueue, decoder, CPU_Check_NMI |
| Determinism | Complete | Identical (config, input, steps) → identical hash |
| Save/Load V3 | Partial | Config + input queue (680 bytes), CRC32, atomic load; CPU/VGA/RAM not serialized |
| App shell (Phase 0-2) | Complete | Display, input, audio, menus, save browser, shaders |
| Phase 3 wiring | Complete | IPX/Glide/PC-98/MIDI routed app→API→engine; MIDI functionally complete; others store globals only |
| Phase 4 (Polish) | Complete | Packaging, logging, crash reporting, update checker (Windows-only) |
| CI pipeline | Complete | 3 platforms, 4 sanitizers, 17 TLA+ checks, fuzz, coverage |
| Contract gates | Complete | 23 gates verified by tests + TLA+ |
| GPL process isolation | Partial | IPC framework built (engine host, proxy, pipe transport); off by default via `LEGENDS_USE_IPC` CMake flag |
| Video capture | Stub | Backend class exists (`video_capture.cpp`), C API returns OK but is a no-op (TODO comments) |
| Joystick | Stub | API declared in header, engine wiring incomplete |

### Requirements Met (alpha)

26 of 50 EARS requirements pass. See [EARS table](#ears-requirements-by-release) for full status.

### Known Limitations

| Limitation | Detail |
|-----------|--------|
| Save/Load incomplete | V3 format serializes config + input queue only; CPU registers, VGA state, and RAM are not saved |
| REQ-SEC-024 (read-only mount) | `LEGENDS_MOUNT_FLAG_READONLY` flag defined but not enforced — no logic checks the flag |
| Video capture | C API stubs return success but perform no capture; backend `VideoCapture` class is unwired |
| Joystick | `legends_joystick_event()` declared but engine-side handler is incomplete |
| ErrorReporter | Stub only — `report()` logs but does not send telemetry |
| Update checker | Windows-only (`update_checker_win.cpp`); no macOS/Linux implementation |
| Config parser | Swallows parse exceptions silently; invalid values fall through to defaults |
| Version mismatch | Root CMakeLists.txt declares 1.0.0; engine declares 0.1.0 |
| GPL IPC stubs | Proxy layer has 30 `NOT_SUPPORTED` stubs; only usable with `LEGENDS_USE_IPC=ON` |

### CI Policy

| Job | Status | Policy |
|-----|--------|--------|
| TSan | `allow_failure` | Known races in mixer thread; does not block CI |
| MSan | `allow_failure` | Uninstrumented libc++ causes false positives |
| osv-scanner | `continue-on-error` + `\|\| true` | Vulnerability scan runs but failures are silently swallowed |

### Action

```bash
git tag -a v0.1.0-alpha.1 -m "Alpha 1: baseline tag — 50-function API, app shell, CI pipeline"
git push origin v0.1.0-alpha.1
```

---

## v0.1.0-beta.1 — Safety + Serialization

**Goal:** Fix all safety issues, add CPU register serialization, address initial security gaps.

### Blockers

| Requirement | Description |
|-------------|-------------|
| REQ-TH-004 | MixerState thread synchronization — add mutex to protect compound operations from audio callback thread racing with main thread |
| REQ-EX-004 | Reentrancy guard expansion — add `in_step` check to all API functions reachable from engine callbacks (capture, hash, config query) |
| REQ-LC-005 | Remove dual runtime path — delete `MachineContext::step()` stub and `dosbox_step()` wrapper; route all callers through `dosbox_lib_step_cycles()` |
| REQ-LC-006 | Remove dead forward declarations — delete 7 unimplemented class forward declarations and their `init_*` stubs |
| REQ-SR-002 | CPU GPR serialization — serialize EAX-EDI, segment registers, EIP, EFLAGS in save state |
| REQ-IN-004 | `text_input` multi-character atomicity — pre-count total slots needed before enqueuing any events |
| REQ-SEC-038 | Shader file size limit — enforce 64 KB max upload in `shader_renderer.cpp` |
| REQ-SEC-039 | Soundfont/ROM file size limit — enforce configurable max size for soundfont and ROM loads |

### Files to Modify

| File | Change |
|------|--------|
| `engine/include/dosbox/dosbox_context.h` | Add `std::mutex mixer_mutex` to MixerState |
| `engine/src/misc/dosbox_context.cpp` | Lock mixer_mutex in mixer access paths; delete `dosbox_step()` |
| `src/legends/legends_embed_api.cpp` | Add `in_step` guard to capture/hash/config API calls; fix `text_input` atomicity |
| `engine/src/aibox/machine_context.cpp` | Delete `step()` stub and 7 `init_*` stub methods |
| `engine/include/aibox/machine_context.h` | Delete 7 forward declarations and member fields |
| `engine/include/dosbox/engine_state.h` | Extend `EngineStateCPU` with GPR/segment/EIP/EFLAGS fields |
| `engine/src/misc/dosbox_library.cpp` | Wire GPR serialization in get/set_cpu_state |
| `src/legends/shader_renderer.cpp` | Add file size check (64 KB max) before shader load |

### Tests Required

| Test | Verifies |
|------|----------|
| `test_mixer_mutex.cpp` | MixerState access from two threads does not race under TSan |
| `test_reentrancy_from_callback.cpp` | API calls from log callback during step return REENTRANT_CALL |
| `test_no_dual_step_path.cpp` | Only `dosbox_lib_step_cycles()` route exists |
| `test_cpu_gpr_roundtrip.cpp` | Save after N cycles → load → verify EAX-EDI/EIP match |
| `test_text_input_atomicity.cpp` | Queue with 3 free slots rejects 4-event char, returns BUFFER_TOO_SMALL |
| `test_shader_size_limit.cpp` | Shader file > 64 KB is rejected |
| `test_soundfont_size_limit.cpp` | Soundfont file exceeding max size is rejected |

### Notes

- CPU GPR serialization is the critical path. Without it, save/load silently corrupts game state on resume.
- Removing `MachineContext::step()` may break `test_dosbox_context.cpp` — audit all callers first.
- MixerState mutex ordering: always acquired before any other lock to prevent deadlocks.
- CI improvements: fix TSan races (mixer mutex) → remove `allow_failure`; promote osv-scanner to required.
- Create `CHANGELOG.md` before beta tag.

---

## v0.1.0-rc.1 — Full Serialization + Security

**Goal:** Full serialization fidelity, security hardening, header dedup phase 1.

### Blockers

| Requirement | Description |
|-------------|-------------|
| REQ-SR-004 | RAM serialization — compress guest RAM (zstd) into save state, restore on load |
| REQ-SR-003 | VGA hardware state serialization — register file, attribute/sequencer/CRT/GFX controllers, DAC palette, VRAM |
| REQ-SR-001 | Save/load round-trip fidelity — with GPR+VGA+RAM, observable state round-trips correctly |
| REQ-SR-005 | Engine PIC event queue serialization — serialize pending PIC timer events for full interrupt timing restore |
| REQ-DT-004 | HashMode::Full — hash VGA register state and device state alongside memory |
| REQ-CP-003 | Frame capture graphics sync — read VGA render output into frame_state for graphics modes |
| REQ-BQ-001 | Header deduplication phase 1 — audit 27+ pairs, categorize, consolidate top 10 |
| REQ-BQ-006 | Register untracked globals — add 30-40 extern globals from engine headers to `globals_registry.yaml` |
| REQ-SEC-001 | IPX networking localhost-only bind — restrict IPX socket binding to loopback interface |
| REQ-SEC-002 | IPX rate limiting — add packet rate limit to prevent network flooding |
| REQ-SEC-024 | Read-only mount implementation — enforce `LEGENDS_MOUNT_FLAG_READONLY` flag (currently defined but no logic) |
| Integration stubs | Implement 16 GTEST_SKIP integration test stubs to exercise actual code paths |

### Files to Modify

| File | Change |
|------|--------|
| `engine/include/dosbox/engine_state.h` | Add `EngineStateVGAFull` struct, `EngineStateRAM` blob struct |
| `engine/src/misc/dosbox_library.cpp` | Implement `dosbox_lib_get_vga_full_state()`, `dosbox_lib_get_memory_snapshot()` |
| `src/legends/legends_embed_api.cpp` | Save/load with RAM + VGA sections |
| `engine/src/misc/state_hash.cpp` | Add VGA register and device state hashing in Full mode |
| `engine/src/hardware/pic.cpp` | Expose PIC event queue for serialization |
| `engine/globals_registry.yaml` | Add 30-40 untracked globals with `deferred` status |
| `include/legends/*.h` + `engine/include/aibox/*.h` | Begin header consolidation (top 10 pairs) |
| `engine/src/hardware/ipx.cpp` | Add localhost-only bind and rate limiting |
| `src/legends/mount_manager.cpp` | Implement read-only enforcement for `LEGENDS_MOUNT_FLAG_READONLY` |
| 16 integration test files | Replace GTEST_SKIP with actual test implementations |

### Tests Required

| Test | Verifies |
|------|----------|
| `test_ram_roundtrip.cpp` | Write known pattern, save, load, verify pattern preserved |
| `test_vga_state_roundtrip.cpp` | Set graphics mode, draw pixels, save, load, verify VRAM |
| `test_pic_event_roundtrip.cpp` | Schedule PIC events, save, load, verify events fire correctly |
| `test_hash_full_mode.cpp` | HashMode::Full produces different hashes for different states |
| `test_graphics_capture.cpp` | After graphics mode step, capture returns non-test-pattern pixels |
| `test_header_no_duplication.cpp` | CI script verifying no identical header pairs remain |
| `test_ipx_localhost_bind.cpp` | IPX socket binds only to loopback |
| `test_ipx_rate_limit.cpp` | Packet rate exceeding limit results in dropped packets |
| `test_mount_readonly.cpp` | Read-only mount rejects write operations |
| `test_mount_path_traversal.cpp` | Paths with `..` are canonicalized or rejected |
| `test_save_state_size_limit.cpp` | >256 MB state file returns error |

### Notes

- VGA serialization is the largest item. DOSBox VGA state is spread across many globals.
- RAM compression: guest RAM is 640KB-16MB. zstd level 1 achieves ~10:1 on uninitialized regions.
- Header dedup is a long tail — start with the 10 highest-risk pairs (divergent content, not just forwarding).
- PIC event serialization requires understanding the DOSBox PIC event queue internals (linked list of deadline-sorted events).
- IPX localhost binding prevents accidental network exposure in the embedded use case.
- TSan CI job must be required (not `allow_failure`) by this point.
- osv-scanner must be required (not `continue-on-error`).
- CHANGELOG.md updated with RC changes.

---

## v1.0.0 — Production Release

**Goal:** All GAP requirements closed. Security hardened. Packaging signed.

### Already Verified as Implemented

| Item | Evidence |
|------|----------|
| REQ-SEC-010 — Save state file size limit (256 MB) | `save_manager.h:32` |
| REQ-SEC-023 — Canonical path resolution | `mount_manager.cpp:39` |
| REQ-SEC-031 — Threat model | `THREAT_MODEL.md` exists |
| REQ-SEC-035 — Code signing infrastructure | Authenticode, notarization, GPG configured |
| REQ-SEC-036 — SHA-256 checksums | Checksum generation in place |
| REQ-SEC-011 — Save state header validation | Header validation in save loader |

### Blockers

| Requirement | Description |
|-------------|-------------|
| REQ-BQ-001 | Header deduplication phase 2 — complete remaining 17+ pairs |
| Phase 3 engine layer | Implement engine-layer initialization for IPX/Glide/PC-98 (app-layer wiring already exists; MIDI is complete) |
| REQ-PRINT-001 | Printer emulation (LPT1 capture to file) |
| REQ-OPS-008 | Operational monitoring |
| Input bounds | Enforce size limits on all external input paths not covered by SEC-038/039 |
| CHANGELOG | Create and maintain `CHANGELOG.md` with complete history from alpha |
| Version alignment | Align root CMakeLists.txt (1.0.0) with engine version (0.1.0) |
| ErrorReporter | Wire `report()` to actual telemetry or remove the abstraction |
| Video capture | Wire C API (`legends_start/stop_video_capture`) to existing `VideoCapture` backend |
| Joystick | Complete engine-side handler for `legends_joystick_event()` |
| L1 | README API documentation — document remaining functions |
| L2 | Audit 3 unused error codes — wire or remove |
| L3 | HandleRegistry — delete (raw pointer comparison is the permanent design) or wire |
| L4 | LEGENDS_ERROR macro collision — rename API macro to `LEGENDS_RETURN_ERROR` or similar |
| L5 | Remove unbuildable `project_legends` CMake target (or fix with real `main.cpp`) |
| H2 | Two `g_current_context` globals — document as accepted risk, add assertion both agree during step |

### Remaining GAP Requirements to Close

| Requirement | Description |
|-------------|-------------|
| REQ-LC-003 | Destroy rejects invalid handle — any non-null currently destroys the real instance |
| REQ-EX-001 | PIC event processing — `PIC_RunQueue()` not called during bridge execution |
| REQ-EX-002 | NMI check not called during execution |
| REQ-EX-006 | Null dereference if context pointer validation fails |
| REQ-SR-007 | Uses `reinterpret_cast` instead of `memcpy` for aligned buffer access |
| REQ-TH-002 | Engine thread check missing in `dosbox_lib_get_context_ptr()` |
| REQ-TH-003 | No exception safety at C ABI boundary |
| REQ-ER-003 | Engine handle validation accepts any non-null pointer |
| REQ-CF-002 | Cycles validation absent |
| REQ-BQ-002 | Memory bounds checks use addition form (overflow risk) |
| REQ-BQ-003 | `check_gsl_lite_usage.py` excludes not properly configured |
| REQ-BQ-004 | No `requirements-dev.txt` for Python dependencies |
| REQ-BQ-005 | Test expects success for invalid handle (DEAD) |

### Tests Required

| Test | Verifies |
|------|----------|
| `test_ipx_networking.cpp` | IPX enable/connect/disconnect/query lifecycle |
| `test_glide_passthrough.cpp` | Glide enable/set_resolution lifecycle |
| `test_pc98_mode.cpp` | PC-98 machine mode switch and verify |
| `test_printer_emulation.cpp` | LPT1 output captured to file |
| `test_security_input_bounds.cpp` | Oversized input payloads rejected |
| `test_context_agreement.cpp` | Assert aibox and dosbox context pointers agree during step |
| `test_video_capture_wired.cpp` | Start/stop capture produces actual output file |

### Notes

- Phase 3 app-layer wiring exists — `application.cpp` routes through C API to `dosbox_lib_*` engine functions. The gap is engine-layer: IPX/Glide/PC-98 engine functions store globals but don't initialize subsystems.
- H2 (two `g_current_context` globals) — merging MachineContext and DOSBoxContext is too invasive. Document and add debug assertion.
- HandleRegistry (L3) — recommend deletion. Raw pointer comparison is simpler and correct.
- All 4 sanitizers (ASan, UBSan, TSan, MSan) must be clean.
- CHANGELOG.md complete and up to date.

---

## Known Limitations (Persistent)

Items to document in release notes for every release until resolved:

| Limitation | Status | Target |
|-----------|--------|--------|
| Update checker is Windows-only | No macOS/Linux implementation | Post-1.0 |
| ErrorReporter is a stub | Logs locally, no telemetry | 1.0 |
| Config parser swallows exceptions | Invalid config values silently use defaults | Post-1.0 |
| Version mismatch (root 1.0.0 vs engine 0.1.0) | Inconsistent version identifiers | 1.0 |
| No ABI stability checking | API/ABI changes not automatically detected | Post-1.0 |
| No CHANGELOG | No change tracking file exists | Beta (create) |
| Video capture C API unwired | Backend exists but API is no-op | 1.0 |
| Joystick engine wiring incomplete | API declared, engine handler missing | 1.0 |

---

## CI Policy

### Sanitizer Failure Policies

| Sanitizer | Current Policy | Target Policy | Target Release |
|-----------|---------------|---------------|----------------|
| ASan | Required | Required | — |
| UBSan | Required | Required | — |
| TSan | `allow_failure` | Required | Beta (after mixer mutex fix) |
| MSan | `allow_failure` | `allow_failure` | Requires instrumented libc++ build |

### Vulnerability Scanning

| Tool | Current Policy | Target Policy | Target Release |
|------|---------------|---------------|----------------|
| osv-scanner | `continue-on-error` + `\|\| true` | Required | Beta |

### Risk Assessment

- **TSan `allow_failure`**: Mixer thread races are real but low-severity (audio glitches, not data corruption). Fix is straightforward (REQ-TH-004 mutex). Risk: masking new races introduced by other changes.
- **MSan `allow_failure`**: False positives from uninstrumented system libc++. Cannot fix without building libc++ with MSan instrumentation. Risk: low — ASan covers most memory safety issues.
- **osv-scanner `|| true`**: Vulnerability scan results are completely invisible. Any known-vulnerable dependency would not block CI or be noticed. Risk: shipping with known CVEs.

---

## Post-1.0

These items are explicitly **not release blockers** for 1.0.

### GPL Process Isolation (IPC)

Status: Partial implementation (framework built, off by default).

The IPC mode (`LEGENDS_USE_IPC=ON`) builds `legends_engine_host` + `legends_proxy` instead of monolithic linking. Engine host, proxy API, and pipe transport are coded. Only required for distributing the engine as a separate GPL process.

**Remaining:**
- Save/load over IPC (proxy forwards to engine host)
- Frame capture over shared memory
- Audio streaming over shared memory ring buffer
- 30 proxy stubs to implement

### Wasm Sandbox

Status: Not started. `LEGENDS_BUILD_WASM` CMake option exists but 50 requirements remain. No user demand. Defer indefinitely.

### UX Enhancements

Partially implemented (2 of 11 requirements complete). Includes: first-run wizard, drag-and-drop, performance overlay, DPI scaling, keyboard menu nav, autosave on crash, hung guest detection, command palette, GUI settings dialog.

---

## EARS Requirements by Release

| Requirement | Alpha | Beta | RC | 1.0 |
|-------------|-------|------|-----|-----|
| REQ-LC-001 | OK | OK | OK | OK |
| REQ-LC-002 | OK | OK | OK | OK |
| REQ-LC-003 | GAP | GAP | GAP | **OK** |
| REQ-LC-004 | OK | OK | OK | OK |
| REQ-LC-005 | GAP | **OK** | OK | OK |
| REQ-LC-006 | GAP | **OK** | OK | OK |
| REQ-EX-001 | GAP | GAP | GAP | **OK** |
| REQ-EX-002 | GAP | GAP | GAP | **OK** |
| REQ-EX-003 | OK | OK | OK | OK |
| REQ-EX-004 | OK | **OK** | OK | OK |
| REQ-EX-005 | OK | OK | OK | OK |
| REQ-EX-006 | GAP | GAP | GAP | **OK** |
| REQ-SR-001 | GAP | GAP | **OK** | OK |
| REQ-SR-002 | GAP | **OK** | OK | OK |
| REQ-SR-003 | GAP | GAP | **OK** | OK |
| REQ-SR-004 | GAP | GAP | **OK** | OK |
| REQ-SR-005 | GAP | GAP | **OK** | OK |
| REQ-SR-006 | OK | OK | OK | OK |
| REQ-SR-007 | GAP | GAP | GAP | **OK** |
| REQ-SR-008 | OK | OK | OK | OK |
| REQ-DT-001 | OK | OK | OK | OK |
| REQ-DT-002 | OK | OK | OK | OK |
| REQ-DT-003 | OK | OK | OK | OK |
| REQ-DT-004 | GAP | GAP | **OK** | OK |
| REQ-IN-001 | OK | OK | OK | OK |
| REQ-IN-002 | OK | OK | OK | OK |
| REQ-IN-003 | OK | OK | OK | OK |
| REQ-IN-004 | GAP | **OK** | OK | OK |
| REQ-IN-005 | OK | OK | OK | OK |
| REQ-CP-001 | OK | OK | OK | OK |
| REQ-CP-002 | OK | OK | OK | OK |
| REQ-CP-003 | GAP | GAP | **OK** | OK |
| REQ-CP-004 | OK | OK | OK | OK |
| REQ-TH-001 | OK | OK | OK | OK |
| REQ-TH-002 | GAP | GAP | GAP | **OK** |
| REQ-TH-003 | GAP | GAP | GAP | **OK** |
| REQ-TH-004 | GAP | **OK** | OK | OK |
| REQ-TH-005 | OK | OK | OK | OK |
| REQ-ER-001 | OK | OK | OK | OK |
| REQ-ER-002 | OK | OK | OK | OK |
| REQ-ER-003 | GAP | GAP | GAP | **OK** |
| REQ-CF-001 | OK | OK | OK | OK |
| REQ-CF-002 | GAP | GAP | GAP | **OK** |
| REQ-CF-003 | OK | OK | OK | OK |
| REQ-BQ-001 | GAP | GAP | GAP | **OK** |
| REQ-BQ-002 | GAP | GAP | GAP | **OK** |
| REQ-BQ-003 | GAP | GAP | GAP | **OK** |
| REQ-BQ-004 | GAP | GAP | GAP | **OK** |
| REQ-BQ-005 | GAP | GAP | GAP | **OK** |
| REQ-BQ-006 | GAP | GAP | **OK** | OK |

| Status | Alpha | Beta | RC | 1.0 |
|--------|-------|------|-----|-----|
| **OK** | 26 | 31 | 38 | **50** |
| **GAP** | 24 | 19 | 12 | 0 |
