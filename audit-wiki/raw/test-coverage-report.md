# Tests, Fuzzing & Benchmarks Audit — Project Legends

Role: Tests, fuzzing & benchmarks auditor
Date: 2026-06-09
Baseline: AUDIT.md 2026-02-24 (IDs C1-C2, H1-H9, M1-M11, L1-L8)
Scope: `tests/` (176 files), `engine/tests/` (82 files), `benchmarks/`, `.github/workflows/`, test-facing parts of `src/legends`, `src/engine_host`, `src/legends_proxy`, `engine/src/misc`.

---

## Executive summary

The suite is large and much of it is real: ~2,788 `TEST(...)` macros under `tests/` plus ~1,878 under `engine/tests/`, a genuine boot-to-DOS-prompt integration test, corrupted-save-state security tests, and a determinism scaffold that runs two instances and compares hashes. Prior finding **L8 (sentinel destroy masking H5) is fixed**, and the underlying H5 fallback is gone.

Three structural problems undercut that breadth. First, on 2026-06-08 (one day before this audit) commit `6900e7a "Stabilize CI and RuntimeHost adoption"` demoted **all four sanitizers, fuzzing, TLA+ model checking, static analysis, and the macOS jobs to nightly/manual-only** — the PR/merge gate is now just Linux+Windows headless build-and-test. The prior audit's "What Works Well" CI list no longer describes what gates a merge. Second, the oracle used by every determinism and save/load roundtrip test is the **Fast-mode state hash, which excludes guest RAM, CPU GPRs/EIP, and VRAM** — the tests would pass even if execution or restoration of the bulk of machine state were wrong. Third, the **IPC/process-isolation path (a core GPL-compliance product promise) has no enabled end-to-end test**: the only true cross-process test is `DISABLED_`, the dispatcher has direct tests for 8 of 43 message cases, the proxy is tested only for "not connected" errors, and there is no in-process-vs-proxy parity suite and no IPC fuzz target.

Eight of the 33 registered integration test files — including `test_replay_determinism.cpp` and `test_save_state_compat.cpp`, the headline product promises — are one-line `GTEST_SKIP() << "Not yet implemented"` stubs that register as green. Benchmarks exist but are never built in CI. The soak test can never run because no workflow sets its enabling env var.

**Health grade: C** — wide but under-enforced, with weak oracles at exactly the points the product claims matter most.

---

## Prior-audit verification

### L8 — sentinel invalid-handle destroy pattern: RESOLVED

Prior state: `tests/unit/test_legends_embed.cpp:23` passed `(void*)0xDEAD` to `legends_destroy` and expected success, masking H5.

Current state (verified):

- `tests/unit/test_legends_embed_lifecycle.cpp:206-215` now creates a real instance, calls `legends_destroy(fake)` with `fake = (legends_handle)0xDEADBEEF`, and asserts `EXPECT_NE(err, LEGENDS_OK)`, then verifies the real instance is still alive and destroys it cleanly.
- The underlying H5 is fixed: `src/legends/legends_embed_api.cpp:79-82` —
  ```cpp
  static legends_instance* get_instance(legends_handle handle) noexcept {
      auto* inst = g_active_instance.load(std::memory_order_acquire);
      return (inst && handle == inst) ? inst : nullptr;
  }
  ```
  No `g_active_instance` fallback remains; an invalid non-null handle returns `nullptr` and the API returns `LEGENDS_ERR_NULL_HANDLE`.

Residue: several older tests still use the "no crash is the assertion" style (see finding test-weak-07) — they no longer mask H5 but assert nothing either.

### H7 — `HashMode::Full` contract mismatch: PARTIALLY RESOLVED, gap moved into the tests

`engine/src/misc/state_hash.cpp:300-305` now hashes guest RAM in Full mode (`builder.update(ctx->memory.base, ctx->memory.size)`), no longer just a `"FULL_MODE"` string (that string survives only in the deprecated no-context path, `state_hash_compat.cpp:49`). However **nothing in the production or test path ever uses Full mode**: `engine/src/misc/dosbox_library.cpp:684` hard-codes `HashMode::Fast`, and `legends_get_state_hash` (`legends_embed_api.cpp:2552-2627`) builds on that. See finding test-oracle-02.

### Prior test-gaps table (AUDIT.md §3): mostly still open

| Prior gap | Status at HEAD |
|---|---|
| No test loads/runs a real COM/EXE | Still open. `tests/fixtures/counter.com`, `graphics.com`, `input.com` exist but are referenced **only** by `tests/fixtures/README.md`; no test mounts or executes them. Boot-to-prompt (`test_boot_to_prompt.cpp`, real since commit `8434561`) is the only guest-code-observing test. |
| Long-running determinism (<200K cycles) | Still open. Largest determinism run is 100K cycles (`test_determinism_at_scale.cpp:81,92`). The soak test that would cover this never runs (finding test-soak-10). |
| Graphics-mode determinism | Still open (golden visual + visual regression are stubs, finding test-stub-03). |
| Multi-process determinism | Still open (IPC E2E disabled, finding test-ipc-04). |

---

## Findings

### test-ci-01 — Merge gate stripped: sanitizers, fuzzing, TLA+, static analysis all demoted to nightly/manual (HIGH, new)

Evidence:

- `git show 6900e7a` (2026-06-08, "Stabilize CI and RuntimeHost adoption") changed `.github/workflows/ci.yml`:
  - sanitizers: `if: github.ref == main || master || schedule` → `if: github.event_name == 'schedule' || 'workflow_dispatch'` (ci.yml:333)
  - fuzz: previously ran on `pull_request` **and** main pushes → now schedule/dispatch only (ci.yml:474)
  - tlaplus: unconditional → schedule/dispatch only (ci.yml:554)
  - static-analysis: unconditional → schedule/dispatch only (ci.yml:431)
  - macOS, macOS-SDL3, Linux-SDL3, Windows-SDL3: now schedule/dispatch/tag only (ci.yml:136,229,263,301)
- The fuzz job still contains a step `"PR: Quick fuzz (30s per target)"` gated `if: github.event_name == 'pull_request'` (ci.yml:503-504) — **dead code**, since the job-level condition excludes PR events entirely.
- TSan and MSan were already `allow_failure: true` (ci.yml:351-365), with comments acknowledging known data races in `g_active_instance` and `CrashBreadcrumb::add()` "until REQ-TH-004 ... fixes land".
- What still gates a PR/merge: `linux` (gcc/clang headless), `linux-ipc`, `windows`, `abi-check`, `coverage` (report-only), path-filtered `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`.

Impact: a memory-safety regression, UB, a fuzz crash, or a TLA+ invariant violation can now merge to main and sit for up to 24h before any job could catch it — in a codebase whose prior audit relied on exactly these jobs as strengths, and whose roadmap is mid-"Security Hardening" (6/22 REQs). The header comment (ci.yml:8-11, "merge-to-main: + sanitizers") and AUDIT.md §3's CI table are now both inaccurate.

This is the "is flakiness being suppressed rather than fixed?" question answered at the workflow level: rather than stabilizing the sanitizer/fuzz jobs, they were removed from the gate and renamed "Optional ...".

Recommendation (effort M): restore ASan+UBSan and a 30s fuzz smoke to the merge-to-main path (they were passing; TSan/MSan can stay nightly with their allow-failure rationale); delete or re-enable the dead PR-fuzz step; update ci.yml header comment; add a CI-dashboard check so nightly-only failures page someone.

### test-oracle-02 — Determinism and save/load roundtrip tests assert on a hash that ignores RAM, CPU registers, and VRAM (HIGH, new; refs prior H1/H7)

Evidence chain (all read at HEAD):

- All hash-based tests call `legends_get_state_hash` (`tests/unit/test_determinism_at_scale.cpp:43`, `tests/integration/test_workflow_determinism.cpp:39`, `tests/unit/test_legends_embed.cpp:744-758` RepeatedSaveLoadCycle, `tests/integration/test_workflow_saveload.cpp`).
- `legends_get_state_hash` (`src/legends/legends_embed_api.cpp:2552-2627`) hashes: the engine hash + legends input queue + time counters + 6 PIC bytes + legends event queue.
- The engine hash comes from `dosbox_lib_get_state_hash` → `dosbox::get_state_hash(ctx, HashMode::Fast)` (`engine/src/misc/dosbox_library.cpp:684`).
- In Fast mode (`engine/src/misc/state_hash.cpp:224-305`): `CpuState::hash_into` covers cycle counters/flags only — no GPRs, EIP, or segment registers (`engine/src/misc/dosbox_context.cpp:103-118`); `MemoryState::hash_into` covers page config, not contents; guest RAM is hashed **only** in `HashMode::Full` (state_hash.cpp:301-303), which nothing calls; VRAM and device state are still absent even from Full ("will be added in Phase B", state_hash.cpp:304).
- In the headless build (the only configuration CI tests), `DmaState::hash_into` reduces to two presence bytes (`dosbox_context.cpp:740-745`).

Impact: `TwoRunsProduceSameHash`, `MidpointSaveLoadMatchesStraightRun`, `RepeatedSaveLoadCycle`, `IdenticalTracesProduceIdenticalHashes`, and `legends_verify_determinism` (also hash-based) are all **asserted-by-sentinel** with respect to the machine state that matters: two runs that diverge in guest RAM, register state, or video memory would still "prove" determinism; a save/load that corrupted RAM would still roundtrip "successfully". With Phase 3 RAM+VGA serialization recently landed (commit `faababd`), the serializer now carries state that no test oracle can observe. README's claim that "Observable state after load equals observable state before save ... is verified by ... integration tests" (README.md:138) overstates what is verified.

Recommendation (effort M): plumb Full-mode hashing through the test path (either a `legends_get_state_hash_ex(mode)` or a test-only hook on `dosbox_lib_get_state_hash`), extend Full mode to VRAM/GPRs as Phase B lands, and switch the determinism-at-scale and roundtrip tests to it. Add one test that writes a known pattern into guest memory via the memory API, saves, perturbs, loads, and reads the pattern back — a direct oracle that bypasses hashing entirely.

### test-stub-03 — 8 of 33 registered integration test files are "Not yet implemented" skip stubs, including the product's headline promises (HIGH, new)

Evidence: each file is exactly two lines, e.g. `tests/integration/test_replay_determinism.cpp`:

```cpp
#include <gtest/gtest.h>
TEST(ReplayDeterminismStub, NotYetImplemented) { GTEST_SKIP() << "Not yet implemented"; }
```

Stub files, all registered in `CMakeLists.txt:941-979` and reporting as green/skipped in every CI run: `test_replay_determinism.cpp`, `test_save_state_compat.cpp` (V3/V4 cross-version compatibility), `test_visual_regression.cpp`, `test_golden_visual.cpp`, `test_determinism_hash.cpp`, `test_cross_platform_smoke.cpp`, `test_frame_timing.cpp`, `test_pairwise_config.cpp`.

Impact: TODO.md and the README describe deterministic replay and save-state compatibility as core capabilities; the corresponding tests exist in name only, and their presence inflates file-count-based coverage claims (the "33 integration tests" figure includes them). Note also `.github/workflows/ci.yml:79-90` uploads visual-diff artifacts "on failure" for a visual regression suite that cannot fail because it is a stub.

Recommendation (effort L for the first two, XL for full visual suite): implement replay determinism (record an input trace, replay from a save, compare Full-mode hashes per test-oracle-02) and save-state compat (golden V3/V4 blobs checked into fixtures) first; convert the remaining stubs into tracked issues and delete the stub files so skips don't masquerade as suite breadth.

### test-ipc-04 — IPC/process-isolation path has no enabled end-to-end or parity coverage; dispatcher 8/43 cases tested (HIGH, new)

Evidence:

- The only true cross-process test is `TEST_F(IpcIntegrationTest, DISABLED_FullE2E)` (`tests/integration/test_ipc_integration.cpp:42`), which additionally `GTEST_SKIP`s if the engine host binary or pipe server is unavailable (lines 66, 79). Disabled tests never run under ctest.
- `src/engine_host/engine_dispatcher.cpp` has 43 `case MsgType::` handlers (lines 39-525). `tests/unit/test_engine_dispatcher.cpp` (174 lines) covers 8: Create, Shutdown, unknown-type, StepMs, Heartbeat, GetConfig, VerifyDeterminism, GetLastError — all happy-path, in-process, no truncated/malformed payload cases.
- `tests/unit/test_proxy_api.cpp` (55 lines) tests only that proxy functions return `LEGENDS_ERR_NOT_INITIALIZED` when not connected, plus three `NOT_SUPPORTED` stubs.
- In the `linux-ipc` CI job (ci.yml:95-127, `LEGENDS_USE_IPC=ON`), `legends_unit_tests` still links `legends_app`→`legends_core` (CMakeLists.txt:779-781); only the `project_legends` executable links `legends_proxy` (CMakeLists.txt:1173-1180). So the IPC CI job re-runs the same in-process tests; the proxy→pipe→engine_host→dispatcher→legends_core chain is never exercised under assertion.
- Commit `274ef4d "Add RuntimeHost proxy parity"` adds openspec documents, capability-truth docs, `messages.h` structs, and dispatcher cases — no parity tests. Greping `tests/` for "parity" matches only an unrelated comment in `test_cpu_context.cpp`.
- `src/app/runtime_host.cpp` (655 lines, 32 methods) has no direct unit test; the only test-side use is a `FakeRuntimeHost` mock (`tests/unit/test_ai_screen_context.cpp:139`).

Impact: GPL v2 process isolation is a core roadmap line item (2/16 REQs done) and the IPC layer is the project's main trust boundary (108 message types, 64MB payload cap). Its serialization, dispatch, SHM/ring transport, heartbeat, and crash-handling behavior are validated only piecewise by unit tests of individual classes; nothing verifies the proxy and the in-process runtime produce the same observable results for the same call sequence.

Recommendation (effort L): (1) un-disable FullE2E with robust engine-host path discovery (CMake can pass the binary path as a compile definition) and run it in the linux-ipc job; (2) add a parameterized parity suite that drives an identical scenario through `InProcessEngineRuntime` and `IpcEngineRuntime` and diffs step results, text captures, and state hashes; (3) add malformed/truncated-payload dispatch tests for every Req type (a table-driven test over the 43 cases is ~1 day).

### test-fuzz-05 — Fuzzing is shallow: CRC wall blocks the load-state fuzzers, no IPC fuzz target, nightly-only 30-60s budget, no persisted corpus (HIGH, new)

Evidence:

- Both save-state fuzzers (`tests/fuzz/fuzz_legends_load_state.cpp`, `fuzz_engine_load_state.cpp`) feed `legends_load_state`/engine load directly. The legends load path verifies CRC32 **before** any section parsing: `src/legends/legends_embed_api.cpp:2072-2073` (`computed_crc != header->checksum` → reject; same at 2335 for the V2 path). The custom mutator (`fuzz_legends_load_state.cpp:56-90`) patches magic and version bytes but **not the checksum**, so virtually every mutated input dies at the CRC check; the deep deserialization code (section bounds, offset arithmetic, the very `reinterpret_cast` paths flagged as H9) is effectively unfuzzed. Seed corpus entries from `generate_corpus.cpp` are valid (pass CRC) but any mutation invalidates them.
- No fuzz target exists for the IPC message codec, header parser, or dispatcher (`grep -i ipc tests/fuzz/` → no matches) — the layer that actually consumes attacker-influenceable bytes across a process boundary.
- `fuzz_input_injection.cpp` (47 lines) drives only `key_event`/`mouse_event`/`step_cycles`; `text_input` (the API with the known partial-commit bug M2) and `key_event_ext`, `joystick_event` are not fuzzed.
- Budget and cadence: 30-60s per target (ci.yml:503-545), nightly/dispatch only since `6900e7a` (see test-ci-01); corpus is regenerated from scratch each run (`ci.yml:499-500`) — no corpus persistence between runs, no dictionary, no coverage-guided accumulation, no OSS-Fuzz/ClusterFuzz integration.

Impact: the fuzzing program exists largely as a checkbox; its current configuration cannot find bugs past the first 64 header bytes of a save state, and never looks at the IPC surface at all.

Recommendation (effort M): in fuzz builds, recompute the CRC after mutation in `LLVMFuzzerCustomMutator` (or compile the parser with a `LEGENDS_FUZZING` define that treats CRC mismatch as warning), persist `build/tests/fuzz/corpus` via `actions/cache`, add `fuzz_ipc_codec` (decode arbitrary bytes → encode → decode roundtrip) and `fuzz_engine_dispatch` (arbitrary MsgType + payload), and fuzz `legends_text_input`.

### test-weak-07 — Assertion-free "no crash" tests persist after the H5 fix made exact assertions possible (MEDIUM, new; residue of L8)

Evidence:

- `tests/unit/test_negative.cpp:74-85` `InvalidFakeHandle`: calls `legends_step_cycles(fake, ...)`, comment says "might be NULL_HANDLE, INVALID_STATE, or even OK", result discarded with `(void)err`.
- `tests/unit/test_negative.cpp:105-118` `DoubleDestroyIsSafe`: "err2 can be OK or an error, the key is no crash", `(void)err2`.
- `tests/unit/test_negative.cpp:124-139` `OperationsOnDestroyedHandleDontCrash`: every return value ignored.
- `tests/unit/test_legends_embed.cpp:709-726` `InvalidHandlesRejected`: despite the name, asserts nothing — three API calls per handle, all results dropped ("or accept if handle validation is minimal").

Impact: since `get_instance` is now strict (legends_embed_api.cpp:79-82), all of these have deterministic correct answers (`LEGENDS_ERR_NULL_HANDLE`). Leaving them assertion-free means a regression of H5 (reintroduction of a fallback) would not be caught by the very tests named for it — the same masking pattern L8 described, one layer up.

Recommendation (effort S): assert exact error codes in all four tests; grep the suite for `(void)err` and triage the rest.

### test-api-08 — API coverage map: 1 API with zero tests, 14 device APIs with null-handle-only tests, capability-gated APIs never asserted in CI (MEDIUM, new)

Per-API grep of `tests/` (50 public `legends_*` functions in `include/legends/legends_embed.h`):

- **Zero test references:** `legends_set_ttf_font` (declared at legends_embed.h:861; appears in src/, docs, and proxy, never in tests/).
- **Null-handle-rejection only** (sole substantive references in `tests/unit/test_phase3_bridge.cpp:16-124`, all `EXPECT_EQ(..., LEGENDS_ERR_NULL_HANDLE)` against `nullptr`; no test ever calls them with a live handle): `legends_set_machine_pc98`, `legends_is_pc98_mode`, `legends_glide_enable`, `legends_glide_set_resolution`, `legends_printer_set_output`, `legends_printer_is_active`, `legends_printer_flush`, `legends_ipx_enable`, `legends_ipx_connect`, `legends_ipx_disconnect`, `legends_ipx_is_connected`, `legends_midi_set_device`, `legends_midi_set_soundfont`, `legends_midi_set_romdir`, `legends_capture_midi_audio` (15 functions). The matching config-struct unit tests (`test_glide_config.cpp` etc.) test app-shell config structs, not the C API.
- **Tested only via paths that skip in CI's headless-only builds:** `legends_start_video_capture` / `legends_stop_video_capture` / `legends_is_video_capturing` (`test_video_capture_lifecycle.cpp:58,62` skip "backend not wired in headless build"); `legends_mount_drive` / `legends_unmount_drive` happy paths (`test_mount_lifecycle.cpp:59-80` skip "not available in headless mode"); `legends_register_event_callback` drive events (`test_event_callbacks.cpp:75-120` same). Every CI job configures `-DLEGENDS_HEADLESS=ON`.
- Well-covered core: create/destroy/step/capture_text/capture_rgb/key/mouse/save/load/hash/reset (15-48 referencing files each).

Impact: roughly a third of the public ABI has no behavioral verification anywhere, and another slice is verified only on developer machines with SDL hardware, never in CI.

Recommendation (effort M): add a live-handle contract test per device API (in headless they should return a defined code — `LEGENDS_ERR_NOT_SUPPORTED` per the error model — which is itself worth pinning); add a TTF font test with a fixture font file; make one CI job run the SDL2 dummy-driver configuration so the capability-gated paths execute (see test-headless-09).

### test-headless-09 — CI is headless-only; SDL-backend tests are path-filtered/nightly, and recent "stabilization" removed an assertion instead of tightening it (MEDIUM, new)

Evidence:

- All ci.yml build jobs use `-DLEGENDS_HEADLESS=ON`; the only SDL test executions live in `pal-ci.yml`, which triggers on path filters (`src/pal/**`, `include/**`, `tests/unit/test_pal_*.cpp`, `cmake/**`, CMakeLists, the workflow itself — pal-ci.yml:3-21) plus a nightly cron. A change to `src/legends/` or `src/app/` that breaks SDL behavior will not run any SDL test pre-merge.
- Commit `8fdd4c6 "Stabilize optional SDL backend CI"` is the defensible kind of stabilization: sets `SDL_VIDEODRIVER/AUDIODRIVER=dummy` (pal-ci.yml:74-76,114-116) and converts hard failures into `GTEST_SKIP` when no audio device exists (`test_pal_sdl2_backend.cpp:116-119`).
- Commit `911692f "Relax SDL backend startup event tests"` is the problematic kind: `tests/unit/test_pal_sdl2_backend.cpp:141-144` and `test_pal_sdl3_backend.cpp:144-147` replaced `EXPECT_EQ(count, 0u)` after init with `(void)input->poll(events, 10);` — the assertion was deleted, not refined. The stated reason ("startup-capable SDL backends may emit window/device events during init") justifies filtering to *only* window/device event types, not asserting nothing. As written, the test verifies only that `poll` doesn't crash.

Impact: combined with test-api-08, the SDL2/SDL3 input/audio/window paths — the code real embedders will run — have their only CI execution on a nightly schedule with at least one assertion recently removed under a "relax" commit. This is the suppress-rather-than-fix pattern the audit was asked to check, in miniature.

Recommendation (effort S-M): restore the startup-event test as a type-whitelist assertion (`EXPECT_TRUE(evt.type == Window || evt.type == Device)` for each returned event); add `src/legends/**`, `src/app/**` to pal-ci path filters or run the SDL2-dummy job in ci.yml proper.

### test-soak-10 — Soak/endurance suite can never run: enabling env var set by no workflow, labeling cmake module missing (MEDIUM, new)

Evidence:

- `tests/integration/test_soak_endurance.cpp:78-82`: skips unless `LEGENDS_SOAK_ENABLED` or `LEGENDS_SOAK_SHORT` is set. `grep -rn LEGENDS_SOAK .github/workflows/` → no matches; the only "soak" references in workflows are comments ("nightly (cron): soak + fuzz", ci.yml:11,25) and a `--label-exclude soak` in release validation (ci.yml:872).
- `CMakeLists.txt:1016-1024` says the soak label "is applied by test name prefix matching in cmake/SoakTestLabels.cmake (if present)" — `ls cmake/ | grep -i soak` → file does not exist, so the `test-soak` target (CMakeLists.txt:1033-1036) and the label-exclusions act on a label nothing applies.
- Consequence: `SoakEnduranceTest.*` (memory-leak, audio-health, hash-consistency-over-time monitoring, 260 lines) reports SKIPPED in every environment that has ever run it, and the nightly schedule the ci.yml header advertises does not include any soak step.

Recommendation (effort S): add a nightly job step `LEGENDS_SOAK_SHORT=1 ctest -R SoakEndurance`; either write `cmake/SoakTestLabels.cmake` or delete the dead comments and label plumbing.

### test-bench-11 — Benchmarks exist but are never built or run anywhere; no performance regression tracking (MEDIUM, new)

Evidence: `benchmarks/` contains `bench_emulation.cpp` (229 lines), `bench_pal.cpp` (226), `bench_ipc_overhead.cpp` (109), wired behind `option(LEGENDS_BUILD_BENCHMARKS ... OFF)` (CMakeLists.txt:1078) with google/benchmark fetched on demand. `grep -rn bench .github/workflows/` → zero matches. No baseline JSON, no comparison script, no perf budget in any workflow.

Impact: for an emulator whose IPC mode adds a per-call hop (and whose `bench_ipc_overhead` exists precisely to measure it), performance can regress arbitrarily without detection; the benchmarks also bit-rot silently since nothing compiles them (they are excluded from every CI configure).

Recommendation (effort M): add a nightly benchmark job that builds with `-DLEGENDS_BUILD_BENCHMARKS=ON` (catching bit-rot at minimum), emits `--benchmark_format=json`, and compares against a checked-in baseline with a generous (e.g. 20%) regression threshold.

### test-dead-12 — Dead and orphaned test files: 3 uncompilable integration tests, 6 unregistered engine tests, 3 unused binary fixtures (LOW, new)

Evidence:

- `tests/integration/test_dual_ffi.cpp`, `test_context_synchronization.cpp`, `test_error_propagation.cpp` are not in `CMakeLists.txt`'s integration source list (lines 941-979) and **cannot compile**: the latter two call `legends_init(handle)`, which does not exist anywhere in `include/` (grep confirms). They reference finding IDs ("H5: Three unsynchronized context pointers", "M14") from an audit generation that predates the current numbering.
- `engine/tests/unit/` has 6 files absent from `engine/tests/CMakeLists.txt:23-92`: `test_dosboxx_abi.c`, `test_dosboxx_embed.cpp`, `test_handle_registry.cpp`, `test_mixer_thread_safety.cpp`, `test_multi_instance_smoke.cpp`, `test_serialization_completeness.cpp`. The last one is ironic: it documents the H1 keyboard-buffer truncation gap as executable assertions, but is never built.
- `tests/fixtures/{counter,graphics,input}.com` are referenced only by `tests/fixtures/README.md` — created (per README) to test real DOS program execution, never wired into a test.

Impact: dead files inflate the "170 test files" figure (the honest number of *built* legends-side test source files is ~158), confuse contributors, and in the engine case silently drop tests that were written to pin known bugs.

Recommendation (effort S): delete the three uncompilable stubs or rewrite them against the current API; register the salvageable engine tests (at minimum `test_serialization_completeness.cpp`); write the COM-fixture execution test (mount dir, run `counter.com`, assert text output) which would simultaneously close the oldest gap in the prior audit's table.

### test-cov-13 — Coverage measurement is report-only; the single enforced threshold covers only `src/app/`; lcov error suppression widened (MEDIUM, new)

Evidence:

- Main coverage job: `lcov --remove '/usr/*' '*/build/_deps/*' '*/tests/*'` (ci.yml:711-712 — exclusions themselves are honest; engine and src stay in the report), then literally writes `"Coverage policy: report-only; no minimum threshold is enforced by CI yet."` (ci.yml:716, added in `6900e7a`).
- The only enforced threshold lives in `release-validation` (tag pushes only) and extracts **only** `*/src/app/*` before checking >= 80% (ci.yml:879-888) — `src/legends/` (the C API), `src/legends_ipc/`, `src/legends_proxy/`, `src/engine_host/`, and `src/pal/` are outside every enforced gate.
- `46e6bd5` widened lcov error suppression from `--ignore-errors mismatch` to `mismatch,gcov,negative` and `unused` to `unused,empty` (ci.yml:709-714) — pragmatic for gcc-13/lcov version skew, but "negative" counts specifically can indicate profile corruption and are now invisible.

Impact: coverage numbers exist but constrain nothing on the layers this project actually authors as its product surface (the embed API and IPC); the 80% app-shell gate runs only at release-tag time.

Recommendation (effort S-M): once a baseline is taken, enforce a ratchet (no-decrease) on `src/legends`+`src/legends_ipc`+`src/legends_proxy` line coverage in the per-push coverage job; document why each `--ignore-errors` flag is needed.

### test-readme-14 — README "tests: 1500+ passing" badge is a static, unverifiable shields.io badge; counts include skips and stubs (LOW, new)

Evidence: `README.md:8` — `[![Tests](https://img.shields.io/badge/tests-1500%2B%20passing-brightgreen)]()` — a hardcoded static badge linking to nothing, not generated from CI. Actual `TEST(...)` macro counts at HEAD: ~2,788 under `tests/` and ~1,878 under `engine/tests/` (registered subset), so the number is stale-low rather than inflated; but "passing" silently includes 65+ `GTEST_SKIP` sites, 8 stub files (test-stub-03), the never-run soak suite (test-soak-10), and a `DISABLED_` E2E (test-ipc-04). The adjacent "build passing" and "coverage" badges are equally static.

Recommendation (effort S): replace with CI-generated badges (GitHub Actions workflow badge + Codecov badge — a Codecov upload already exists at ci.yml:726-731), or state the number with a date and the skip count.

---

## What is genuinely good (credit where due)

- **Boot-to-prompt is real** (`test_boot_to_prompt.cpp`, commit `8434561` replaced the old GTEST_SKIP stub): boots the engine, scrapes the text screen for a DOS prompt, checks framebuffer non-black — the single strongest end-to-end assertion in the suite.
- **Save-state security tests** (`test_legends_embed_security.cpp`): corrupted offsets, geometry, truncation — with exact error-code assertions (lines 82, 100, 122), not just no-crash.
- **L8/H5 properly closed** with a test that proves the negative case *and* the survivor instance.
- **Test hygiene infrastructure**: shared fixtures extracted (commits `4accbfc`, `0ce6424`, `c715979`, `c3dcdbb`), per-test 30s/60s timeouts, MSVC/GCC warning containment confined to test targets (CMakeLists.txt:807-813).
- **Honest skip messaging**: headless skips state their reason precisely; the v2 load-safety and atomicity tests assert the four-phase load behavior described in the TLA+ spec.

## Suite shape (for the synthesis page)

| Bucket | Files | Built? | Notes |
|---|---|---|---|
| tests/unit | 125 (.cpp/.c) | all 125 registered | core API, IPC classes, app shell, PAL |
| tests/integration | 33 | 30 registered + 3 uncompilable orphans | 8 of 30 are skip stubs |
| tests/toolchain | 2 | yes | C++23 gate |
| tests/fuzz | 4 targets + corpus gen | fuzz builds only | nightly-only since 6900e7a |
| tests/scripts | 1 (GPL-isolation script test) | run via python, not wired to a CI step found in workflows | |
| engine/tests | 53 registered of 59 unit + determinism suite + 4 unbuilt upstream DOSBox-X test files | aibox_unit_tests + aibox_determinism_tests | |
| benchmarks | 3 | never (option OFF, no CI) | |

## Sprint-theme recommendations

1. **Restore the merge gate** (test-ci-01, test-cov-13, test-soak-10): ASan/UBSan + 30s fuzz smoke back on merge-to-main; nightly soak step with `LEGENDS_SOAK_SHORT=1`; coverage ratchet on `src/legends*`; fix the dead PR-fuzz step and stale ci.yml header.
2. **Strengthen the oracles** (test-oracle-02, test-stub-03): Full-mode hash (RAM, and extend to GPR/VRAM with Phase B) exposed to tests; rewrite determinism-at-scale and roundtrip tests on it; implement replay-determinism and save-state-compat integration tests; add a direct write-pattern/save/load/read-pattern memory test.
3. **Test the trust boundary** (test-ipc-04, test-fuzz-05): enable the IPC E2E in the linux-ipc job; in-process vs proxy parity suite; table-driven malformed-payload tests over all 43 dispatch cases; `fuzz_ipc_codec` + `fuzz_engine_dispatch` targets; CRC fix-up in the load-state fuzz mutator; persist fuzz corpus across runs.
4. **Burn down the dishonest residue** (test-weak-07, test-api-08, test-dead-12, test-readme-14): exact error-code assertions in the no-crash tests; live-handle contract tests for the 15 device APIs + `legends_set_ttf_font`; delete or fix orphaned test files; wire the COM fixtures into an execution test; CI-generated badges.
