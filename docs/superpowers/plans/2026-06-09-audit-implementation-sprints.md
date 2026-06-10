# Post-Audit Implementation Sprint Program

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Plan altitude:** this is a sprint *program* derived from the 2026-06-09 eight-role audit (evidence: `audit-wiki/raw/*.md`, synthesis: `audit-wiki/wiki/`). Each sprint below lists concrete, file-anchored work items and exit criteria. At each sprint kickoff, author the detailed per-task TDD plan (failing test → minimal code → green → commit) for that sprint's items using superpowers:writing-plans; the file anchors and acceptance commands here are the spec for those plans.

**Goal:** Take Project Legends from "B-grade codebase wrapped in D-grade verification" (audit verdict) to a releasable, legally coherent, mechanically verified embeddable emulator in 8 sprints (~12–14 team-weeks).

**Architecture:** Fix order follows the audit's dependency logic: re-arm the safety net and kill the two criticals first (Sprint 0); make the records and oracles truthful so later work is measurable (Sprints 1–2); make the IPC runtime boot, then harden it, then make GPL isolation mechanical (Sprints 3–5); only then take on the engine-time epic with working instruments (Sprint 6); close out debt and prove the release path (Sprint 7).

**Tech Stack:** C++23, CMake ≥3.x + CMakePresets, GoogleTest, libFuzzer + ASan/UBSan/TSan/MSan, TLA+/TLC, GitHub Actions, lcov.

**Finding IDs** reference `audit-wiki/raw/fleet-structured-results.json` (per-role `findings[]`) and prior `AUDIT.md` IDs (C/H/M/L). Refuted-by-verification findings SEC-01 and api-05 are deliberately absent.

---

## Sprint 0 — Stop the bleeding (~1 week)

The four items with unbounded downside and small effort. Nothing else merges before the gates are re-armed.

**Findings:** mem-01 (critical), mem-02 (high), ci-01/test-ci-01 (high), ci-04 (medium), lic-01 (critical).

**Files:**
- Modify: `engine/src/misc/dosbox_library.cpp` (V5 load path, ~lines 1106–1487)
- Modify: `src/legends/legends_embed_api.cpp` (`legends_create` error paths)
- Modify: `.github/workflows/ci.yml` (job gating conditions, ~lines 474, 503–513)
- Modify: `LICENSE`
- Test: `tests/fuzz/` (new RAM-blob fuzz target), `tests/unit/test_legends_embed.cpp`

- [ ] **0.1 Fix mem-01 (save-state heap overflow).** In the engine V5 deserializer, stop trusting the deserialized `memory.size` as decompression capacity: validate every size/offset against the *live* allocation before any RLE decode, and clamp decode capacity independently of deserialized fields. Never overwrite the live allocation descriptor from blob contents. Regression test: craft a CRC-valid blob declaring an oversized `memory.size`, assert load fails with the existing invalid-state error code and the machine state is unchanged.
- [ ] **0.2 Fix mem-02 (create-error-path brick).** Audit every early-return/throw path in `legends_create`: on failure after engine-handle acquisition, release the handle and reset `g_instance_exists`. Test: force a late create failure, assert a subsequent `legends_create` succeeds.
- [ ] **0.3 Re-arm the merge gates (reverse the 6900e7a demotion).** ASan+UBSan jobs and a 30s fuzz smoke run on `push` to master and on `pull_request`; fix the dead PR-fuzz step (job-level `if` at ci.yml:474 excludes the PR events the step at :503–513 targets); add `develop` to `pull_request` branch filters in `ci.yml` and `pal-ci.yml` (ci-04). TSan/MSan may stay allow-failure *with a dated exit note in the workflow* (full fix in Sprint 7).
- [ ] **0.4 Fix lic-01 (root LICENSE).** Replace the bare MIT text with a true multi-component overview: per-directory license table (engine/ GPL, src/ as decided in Sprint 1's lic-02 gate, external/ per component) pointing at COPYING and LICENSES/. Do not resolve -only vs -or-later here; state the current tags factually.
- [ ] **0.5 Fuzz the fixed path.** Add `fuzz_engine_memory_blob` seeded with valid V5 states; mutator recomputes CRC32 after mutation so inputs reach deserialization (the CRC-wall fix pattern, fully generalized in Sprint 2). Run 10 min under ASan locally before merge.

**Exit:** crafted-blob regression test green under ASan; create-failure test green; a deliberately UB-introducing draft PR is blocked by CI; LICENSE accurately describes the tree.

---

## Sprint 1 — Truthful record (~1 week, parallel with Sprint 2)

[[Documentation Drift]] remediation: make the documents of record match HEAD so planning stops running on corrupt data.

**Findings:** doc-01..05 (backlog-miner), DLA doc-01..05, lic-02 decision, spec-02, test-readme-14, backlog-05/L1.

**Files:**
- Modify: `ROADMAP.md`/`roadmap.md` (collision), `TODO.md`, `CHANGELOG.md`, `AUDIT.md`, `README.md`, `ARCHITECTURE.md`, `REQUIREMENTS.md`, `TLA_CONFORMANCE.md`, `openspec/`
- Create: `scripts/check_case_collisions.py`, README API-table generator (from `include/legends/legends_embed.h` Doxygen)

- [ ] **1.1** Resolve the `ROADMAP.md`/`roadmap.md` case collision: keep one file, restore the March source-verified content (commit `8e3b0b0`) as the baseline, fold in legitimate June additions, fix the false v4.1.0/2026-02-25 stamp. Add a CI check failing on case-colliding tracked paths.
- [ ] **1.2** Regenerate `TODO.md` from the backlog-miner's verification matrix (`audit-wiki/raw/backlog-miner-report.md`); annotate `AUDIT.md` with the 22 verified resolutions and 8 open carryovers; remove the CHANGELOG TLS-verification claim (no HTTP/TLS transport exists).
- [ ] **1.3** Demote Wasm everywhere it's claimed as present-tense capability (README bullet, ARCHITECTURE section, CMake comments) to "planned"; the referenced `wasm.md`/`wit/legends-emulator.wit` never existed in git history.
- [ ] **1.4** Re-verify all 50 EARS requirement statuses in `REQUIREMENTS.md` at HEAD with `verified-at: <commit>` stamps (6 of 10 sampled were wrong in both directions). Re-baseline `TLA_CONFORMANCE.md` (4 of 5 non-conformant invariants are fixed but undocumented).
- [ ] **1.5** Generate the README API table for all 50 functions + complete error-code table from the header; replace the static "1500+ passing" badge with CI-generated badges. Fix ARCHITECTURE.md save-state constants (96 B/"LEGS"/v2 → 64 B/"DBXS"/v3 per `legends_embed_api.cpp:92-93`) and the stale "cpu_bridge is a stub" label.
- [ ] **1.6** OpenSpec hygiene: archive the 17 stale active changes (completed Feb work), populate `openspec/specs/` as the canonical baseline, add a CI staleness check.
- [ ] **1.7 DECISION GATE (owner): GPL-2.0-only vs -or-later.** All 107 SPDX tags and upstream DOSBox-X say -or-later; README/CONTRIBUTING say -only. Recommend -or-later. Align all docs to the decision.
- [ ] **1.8 DECISION GATE (owner): Wasm sandbox.** Fund a REQ-WASM-001..010 spike or formally defer roadmap Section 15 so completion metrics stop being distorted (0/50 since Feb).

**Exit:** zero contradictions between TODO/ROADMAP/AUDIT/REQUIREMENTS on sampled re-check; both decision gates recorded in the roadmap.

---

## Sprint 2 — Trustworthy oracles (~2 weeks)

[[Determinism Oracle Weakness]]: the product's central claim gets an instrument that can detect violations. Prerequisite for Sprint 6.

**Findings:** conc-07 (high), test-oracle-02/H7 (high), test-stub-03 (high), test-fuzz-05 (high), conc-08, test-weak-07, test-cov-13, test-dead-12, backlog-03.

**Files:**
- Modify: `engine/src/misc/state_hash.cpp` (~line 300), `engine/include/dosbox/state_hash.h`, `src/legends/legends_embed_api.cpp` (`legends_joystick_event` ~lines 2906–2956)
- Modify: `tests/integration/` (8 GTEST_SKIP stub files), `tests/unit/test_determinism_at_scale.cpp`, `tests/fuzz/fuzz_legends_load_state.cpp`, `engine/tests/CMakeLists.txt`
- Modify: `.github/workflows/ci.yml` (coverage ratchet)

- [ ] **2.1** Extend the Fast-mode hash with GPRs/EIP/EFLAGS/segment registers; feed the V5-serialized VGA registers + VRAM into Full mode (closes H7's contract gap — or amend the header contract where coverage is deliberately deferred, no silent overstatement).
- [ ] **2.2** Switch determinism CI and the save/load roundtrip tests to Full-mode hashing; add a direct write-pattern → save → load → read-back guest-memory test.
- [ ] **2.3** Implement the 8 skip-stub integration tests, replay-determinism and save-state-compat first; register the 6 orphaned engine test files in `engine/tests/CMakeLists.txt`; delete the 3 uncompilable tests calling nonexistent `legends_init()`.
- [ ] **2.4** Replace assertion-free "no crash" tests with exact error-code assertions (the H5 fix made this possible); add live-handle contract tests for the 15 device APIs and `legends_set_ttf_font` (currently zero tests).
- [ ] **2.5** Fix the fuzzer CRC wall generally: custom mutator recomputes CRC32 post-mutation for both load-state fuzzers; persist a corpus as a CI artifact.
- [ ] **2.6** Fix `legends_joystick_event` (conc-08): route through the deterministic input queue, honor the `in_step` guard, return success or don't mutate — never both.
- [ ] **2.7** Coverage ratchet: enforce a floor on `src/legends*`, `src/legends_ipc`, `src/legends_proxy` per-push (start at current measured %, fail on decrease).
- [ ] **2.8 C2 verification spike (1 day).** Settle the [[Vacuous Interrupt Delivery (C2)]] conflict empirically: link-map `aibox_core`, confirm which `PIC_RunQueue` symbol binds, write a failing test (timer IRQ observable during `legends_step_ms`) that becomes Sprint 6's acceptance test.

**Exit:** determinism CI red if registers or RAM diverge (prove with an injected fault); 0 skip-stubs in registered integration tests; fuzzers reach deserialization (coverage report); C2 status settled with a pinned failing test.

---

## Sprint 3 — IPC made real (~2 weeks)

The IPC runtime boots, speaks a correlated protocol, and provably matches in-process semantics. [[IPC Trust Boundary Gaps]] functional half.

**Findings:** api-01 (high), api-02 (high), api-03 (high), api-04/conc-09/sec-02 (high), conc-10, conc-13, test-ipc-04 (high), backlog doc-04.

**Files:**
- Modify: `src/legends_proxy/proxy_api.cpp`, `src/legends_proxy/proxy_connection.*`, `src/engine_host/` (dispatcher + main loop), `src/legends_ipc/protocol.cpp` (stub → implement or delete), shared-memory ring/framebuffer modules, root `CMakeLists.txt` (SDL2+IPC link), `.github/workflows/ci.yml` (linux-ipc job)
- Test: new `tests/integration/test_runtime_parity.cpp`, enable `DISABLED_FullE2E`

- [ ] **3.1** Wire the boot path: proxy `legends_create` spawns/connects to the engine host (EngineSpawner + `ProxyConnection::connect`, which today has no production caller); propagate `config_path` (currently silently dropped).
- [ ] **3.2** Validate the version handshake: protocol + engine versions checked at create, mismatch → typed error (today versions are transmitted but never validated).
- [ ] **3.3** Correlate responses by `sequence_id` + `msg_type`; on timeout, drain/resync instead of permanent desync; queue unsolicited `EventNotification`s instead of misreading them as responses.
- [ ] **3.4** Fix the cross-process audio ring to true SPSC (single writer of `read_index`); validate `capacity_frames` and all geometry from SHM against the mapped size on open (divide-by-zero fix).
- [ ] **3.5** Wire framebuffer/audio SHM producers into the engine-host step loop so IPC `capture_rgb` returns real frames instead of empty-with-OK.
- [ ] **3.6** Close or capability-gate the 6 NOT_SUPPORTED proxy APIs (video capture ×3, TTF font, event callbacks): implement EventNotification-based forwarding, or add a queryable capability API so divergence is contractual, not silent. Fix proxy `destroy(NULL)`/handle-validation inversions (the H5-spirit regression).
- [ ] **3.7** Parity suite: one parameterized C-ABI conformance suite run against both runtimes in CI; enable `FullE2E` in the linux-ipc job; fix the SDL2+IPC link by extracting `Application` from GPL-linked `legends_app`.

**Exit:** linux-ipc CI boots the app end-to-end in IPC mode; parity suite green over all 50 functions (or documented capability gaps); kill -9 of the engine host yields a typed error, not a hang.

---

## Sprint 4 — Trust boundary hardening (~1.5 weeks)

The now-running boundary becomes adversarially defensible.

**Findings:** sec-03, sec-04, api-10, sec-06, mem-04, mem-05.

**Files:**
- Modify: IPC endpoint creation (named pipes/UDS/SHM open paths), `src/engine_host/` dispatcher (GetStateHash zero-init), `src/legends_ipc/messages.cpp` (MountDriveReq length field), `src/legends/legends_embed_api.cpp` + `engine/src/misc/dosbox_library.cpp` (load staging)
- Create: `tests/fuzz/fuzz_ipc_codec.cpp`, `tests/fuzz/fuzz_engine_dispatch.cpp`, proxy-side `Resp::deserialize` fuzzers

- [ ] **4.1** Endpoint auth (sec-03): unguessable per-launch names, owner-only DACLs / `PIPE_REJECT_REMOTE_CLIENTS` / `FILE_FLAG_FIRST_PIPE_INSTANCE` on Windows, `O_EXCL` SHM creation, handshake nonce passed via the spawn channel.
- [ ] **4.2** Fuzz the IPC surface (sec-04): byte-level libFuzzer targets for `MessageCodec` + `dispatch()` and proxy-side response deserializers, wired into the CI fuzz job with corpora.
- [ ] **4.3** Zero-initialize the GetStateHash response (api-10, 32-byte stack leak); fix MountDriveReq 8-bit path-length truncation (sec-06) with full-width length + bounds check.
- [ ] **4.4** Load atomicity (mem-04): perform all wrapper-layer allocations before any engine mutation, or add engine snapshot/rollback, so a failed load leaves the machine unchanged. Field-serialize the padded V3 structs (mem-05) or version them out.
- [ ] **4.5** Evaluate (decision memo, ≤1 page): keyed/authenticated save-state integrity vs documented "CRC is corruption-detection only" stance.

**Exit:** 24h fuzz run on the three new IPC targets without crash; endpoint-squatting test fails to connect; load-failure state-intact test green.

---

## Sprint 5 — GPL isolation enforceable (~1 week)

[[Licensing Inconsistency]] mechanical half: the legal promise becomes a CI failure, not a comment. **Re-audit checkpoint at sprint end.**

**Findings:** ci-02 (high), sec-05 (high), spec-01, api-07, lic-03 (high), lic-04.

**Files:**
- Modify: `cmake/VerifyGPLIsolation.cmake` (wire in), `cmake/ModuleDAG.cmake` + module manifest, `.github/workflows/ci.yml` (linux-ipc + new windows-ipc job), `NOTICE`, `DEPENDENCIES.md`, `include/legends/legends_embed.h` (SPDX), design doc TDD-LIC-001
- Create: `LICENSES/` directory (TODO.md already claims it exists), CI SPDX-policy lint

- [ ] **5.1** Include `VerifyGPLIsolation.cmake` from the IPC build; run `scripts/verify_gpl_isolation.py` (nm symbol firewall) over `liblegends_proxy.a` and `liblegends_ipc.a` in linux-ipc CI — fail on any GPL symbol.
- [ ] **5.2** Extend `legends_verify_all_dags()` to all six manifest modules + `legends_app` so a stray `legends_proxy → legends_core` edge fails configure (today it passes silently).
- [ ] **5.3** Add a windows-ipc CI job building engine_host + proxy (currently zero Windows IPC coverage).
- [ ] **5.4** Header licensing (lic-03): dual-license or re-license `legends_embed.h` per the Sprint 1 GPL decision, document in TDD-LIC-001, fix the "proprietary shell" vs GPL-tagged `src/app` contradiction, add the in-process-mode GPL-obligations paragraph to README.
- [ ] **5.5** Attribute vendored stb/glad/zlib/FluidSynth/MUNT in NOTICE + DEPENDENCIES.md; create `LICENSES/`; add the SPDX-policy CI lint.
- [ ] **5.6** Isolation assurance (sec-05 residue): engine-host crash detection + typed recovery error in the proxy; publish the IPC capability matrix doc.
- [ ] **5.7 Re-audit checkpoint:** re-run the audit fleet's security + licensing roles against HEAD; findings feed Sprint 6/7 scope.

**Exit:** a test PR adding a GPL symbol to the proxy is blocked by CI; Windows IPC job green; license docs internally consistent end-to-end.

---

## Sprint 6 — Make time real (~3–4 weeks, XL — gated on Sprint 2)

[[Vacuous Interrupt Delivery (C2)]]: timer and IRQ-driven guest code actually runs during stepped execution, deterministically. Runnable parallel to Sprints 4–5 if staffed.

**Findings:** conc-01/C2 (critical), conc-02/H2, conc-05 residue, BVA scheduler-serialization gap, conc-12 residue.

**Files:**
- Modify: `engine/src/misc/cpu_bridge.cpp` (~lines 110–130), engine CMake targets (PIC linkage), `engine/src/hardware/pic.cpp` or a new deterministic event-queue module, V5/V6 save format (scheduler queue section), `spec/` TLA+ Scheduler/PIC specs, `TLA_CONFORMANCE.md`
- Test: the Sprint 2.8 pinned failing test (timer IRQ during `legends_step_ms`), determinism CI with Full-mode hash

- [ ] **6.1** Design note first (1–2 days): integrate the real PIC vs implement a deterministic PIC/PIT event queue for library mode. Constraint from the audit: the bridge's cycle accounting only works with the stub — naive relinking corrupts `CPU_Cycles`/`CPU_CycleLeft` math.
- [ ] **6.2** Restructure `execute_cycles` into per-ms slices: `PIC_RunQueue()` → decoder → `TIMER_AddTick()`, with corrected cycle accounting; device time advances during `legends_step_*`.
- [ ] **6.3** Serialize the scheduler/event queue in the save format (closes the `EventCountPreserved` PARTIAL); bump format version with compat test.
- [ ] **6.4** Decide H2 (dual thread-local contexts): unify behind one accessor, or document the dual-guard invariant and add a debug assertion they reference the same instance.
- [ ] **6.5** Make the Scheduler/PIC TLA+ specs testable against the new queue; re-baseline `TLA_CONFORMANCE.md`; flip REQ-EX-001/002 from GAP with verified-at stamps.

**Exit:** the Sprint 2.8 pinned test passes (BIOS tick observable, keyboard IRQ fires during stepped execution); determinism CI (Full-mode hash) green across 2 OSes × 2 compilers; save/load mid-timer-burst roundtrips.

---

## Sprint 7 — Debt burn-down & release dry run (~1.5 weeks)

Close the audit cycle; prove the ship process before v1.0 pressure.

**Findings:** backlog-02/H3/M10, backlog-04/H4/M5, backlog-06/L3, backlog-07/M4, api-06, api-11, conc-11, ci-03 (high), ci-05, ci-06, build-01, build-03, build-05, build-06, test-bench-11, test-soak-10, test-headless-09, build-04/L5 decision.

- [ ] **7.1** Delete dead paths: `dosbox_step()`/`MachineContext::step()` counter stub (migrate `test_dosbox_context.cpp` to `dosbox_lib_step_cycles()`), the 7 init_* no-ops + phantom forward declarations; delete-or-adopt HandleRegistry (decision: delete unless multi-instance is scheduled).
- [ ] **7.2** Collapse the byte-identical InProcess/Ipc RuntimeHost subclasses; de-inline the SDL3 target's 45-file source list (api-11); decide L5 (SDL2 Windows target): fix the mingw32 hardcode or delete the target.
- [ ] **7.3** TSan green (conc-11): fix the named `g_active_instance` and `CrashBreadcrumb::add` races + residual audio nits, suppress intentional wrong-thread tests, remove `allow_failure` so races gate merges.
- [ ] **7.4** Supply chain & build hygiene: SHA-pin FetchContent deps and GitHub Actions; replace the osv-scanner lockfile no-op with an SBOM-based scan including the engine fork; add ccache; consolidate the four overlapping workflows; delete committed `build_log.txt`/`build_output.txt`; un-FORCE `AIBOX_BUILD_TESTS`; scope `_FORTIFY_SOURCE` to optimized builds; extend extern-globals registry sweep + CI guard (M4).
- [ ] **7.5** Wire benchmarks into a nightly CI job with regression tracking; implement the soak label + `LEGENDS_SOAK_SHORT=1` nightly step; restore the deleted SDL startup-event assertion properly (test-headless-09).
- [ ] **7.6 Release dry run (ci-03):** push `v0.9.0-rc.1` from a throwaway branch; execute packaging (NSIS/DMG/TGZ), checksum generation, and the never-run 80% coverage release gate end-to-end; fix version-string fallback and CPack fallout; make release-validation `workflow_dispatch`able; correct RELEASING.md to match reality.

**Exit:** TSan gating; rc pipeline produced installable artifacts on all three platforms; AUDIT.md closed out with this program's resolutions recorded (don't repeat the February mistake).

---

## Program-level tracking

| Sprint | Theme | Effort | Depends on |
|---|---|---|---|
| 0 | Stop the bleeding | 1 wk | — |
| 1 | Truthful record | 1 wk | 0 |
| 2 | Trustworthy oracles | 2 wks | 0 (∥ 1) |
| 3 | IPC made real | 2 wks | 0 |
| 4 | Boundary hardening | 1.5 wks | 3 |
| 5 | GPL enforceable + re-audit | 1 wk | 3, 4 |
| 6 | Make time real | 3–4 wks | 2 (∥ 4–5) |
| 7 | Debt + release dry run | 1.5 wks | all |

Accepted/deferred (tracked, not scheduled): Wasm sandbox (per Sprint 1.8 decision), H4/M5 init-stub deletion is in 7.1, UX/accessibility roadmap section (out of audit scope).
