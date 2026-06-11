---
type: entity
entity_kind: system
aliases: ["sanitizer lanes", "fuzz lane", "coverage lane", "determinism lane"]
tags: [entity, type/entity, topic/ci, topic/testing, topic/audit]
created: 2026-06-10
updated: 2026-06-10
status: draft
related:
  - "[[Determinism Oracle Weakness]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
sources:
  - "[[CI Run History (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
---

# Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)

## Overview

Per-lane inventory (2026-06-10) of how each dynamic-verification lane is implemented (CMake preset and/or CI job), what its enforcement status actually is, and how it has performed empirically. Citations are repo file paths unless marked as wiki sources. Trigger-tier context: [[Build & CI System (Project Legends)]] and [[CI Gate Coverage Map]]; what the test executables themselves contain: [[Project Legends Test Suite]]; empirical pass/fail: [[CI Run History (2026-06)]].

All four sanitizer lanes share one CI job (`sanitizers`, `.github/workflows/ci.yml:328-401`) that runs on pull requests, pushes to `master` only (not `main`/`develop`), nightly schedule, and manual dispatch (`.github/workflows/ci.yml:333-337`). Per-matrix-entry `allow_failure` flags feed `continue-on-error` (`.github/workflows/ci.yml:332`).

## ASan/UBSan

- **Preset:** `asan` — clang-18, libc++, `-fsanitize=address,undefined`, tests ON (`CMakePresets.json:56-74`); matching test preset (`CMakePresets.json:183-193`). The CI job runs ASan and UBSan as two *separate* matrix entries rather than combined as in the preset (`.github/workflows/ci.yml:343-350`).
- **Workflow:** `sanitizers` matrix entries `address` (`.github/workflows/ci.yml:343-346`) and `undefined` (`.github/workflows/ci.yml:347-350`), each building with `LEGENDS_BUILD_TESTS=ON` and running the full ctest suite under `halt_on_error=1` (`.github/workflows/ci.yml:383-401`).
- **Enforcement:** enforced when it runs — neither entry carries `allow_failure`, so a red ASan or UBSan run fails the workflow. Scope caveat: skipped on pushes to `main`/`develop` (`.github/workflows/ci.yml:333-337`).
- **Empirical:** the `address` and `undefined` Sanitizer jobs each failed 6 of 6 sampled executions in the 30-run job sample of [[CI Run History (2026-06)]]; their `Optional` variants failed 1 of 1. An enforced lane that always fails means the enforcement is real but the signal is permanently red.

## TSan

- **Preset:** `tsan` (`CMakePresets.json:75-92`); test preset at `CMakePresets.json:194-203`.
- **Workflow:** `sanitizers` matrix entry `thread` (`.github/workflows/ci.yml:357-361`).
- **Enforcement:** allow-failure — `allow_failure: true` (`.github/workflows/ci.yml:361`). The in-file rationale names known races in engine global state (`g_active_instance`, `CrashBreadcrumb::add()`) and records an exit plan: "Sprint 7 tracks removing allow_failure after the remaining engine global-state races are fixed" (`.github/workflows/ci.yml:351-356`). [[Concurrency & Determinism Audit (2026-06)]] flags this as conc-11: the gate was never re-tightened after the REQ-TH-004 mixer fixes landed, so new races land silently.
- **Empirical:** `thread` Sanitizer failed 6 of 6 sampled executions ([[CI Run History (2026-06)]]) — consistent with the named known races; advisory status means none of those failures blocked anything.

## MSan

- **Preset:** none — `CMakePresets.json` contains no MSan configure or test preset. The only repo-side MSan hooks are the CI matrix entry and the `ENABLE_MSAN` option consumed by the fuzz tree (`tests/fuzz/CMakeLists.txt:104-108`).
- **Workflow:** `sanitizers` matrix entry `memory` (`.github/workflows/ci.yml:368-373`).
- **Enforcement:** allow-failure — `allow_failure: true` (`.github/workflows/ci.yml:373`). The in-file comment states the lane cannot currently pass at all: CI links stock (non-MSan-instrumented) libc++, so "test executables crash on startup"; exit plan is to build an instrumented runtime "or retiring the MSan gate" (`.github/workflows/ci.yml:362-367`).
- **Empirical:** `memory` Sanitizer failed 6 of 6 sampled executions ([[CI Run History (2026-06)]]) — expected, per the comment, since the binaries crash on startup. The lane currently verifies nothing.

## Fuzz

- **Preset:** `fuzz` — clang-18, `ENABLE_FUZZING=ON`, `ENABLE_ASAN=ON`, Release (`CMakePresets.json:119-132`); build preset only, no test preset (`CMakePresets.json:168-218` has no fuzz entry) — the harnesses are not CTest-registered (no `add_test`/`gtest_discover_tests` in `tests/fuzz/CMakeLists.txt`).
- **Workflow:** `fuzz` job (`.github/workflows/ci.yml:478-578`); same trigger condition as `sanitizers` — PRs, pushes to `master`, nightly, dispatch (`.github/workflows/ci.yml:482-486`).
- **Targets (five):** `fuzz_legends_load_state`, `fuzz_engine_load_state`, `fuzz_engine_memory_blob`, `fuzz_input_injection`, `fuzz_config_parser` (`tests/fuzz/CMakeLists.txt:114, 140, 169, 198, 224`; sources under `tests/fuzz/`). Clang/libFuzzer-only (`tests/fuzz/CMakeLists.txt:63-67`).
- **Durations:** PR and push-to-master runs execute all five targets at 30 s each ("Smoke: Quick fuzz (30s per target)", `.github/workflows/ci.yml:514-537`); non-PR runs (push to master, nightly, dispatch) run each target for 60 s (`.github/workflows/ci.yml:539-578`). The local `fuzz-quick` custom target runs two targets at 60 s (`tests/fuzz/CMakeLists.txt:260-271`).
- **Corpus handling:** `generate_corpus.cpp` builds the compiler-agnostic `generate_fuzz_corpus` tool (`tests/fuzz/CMakeLists.txt:24-26`); CI regenerates the seed corpus from scratch into `build/tests/fuzz/corpus` on every run (`.github/workflows/ci.yml:511-512`). CMake would copy a checked-in `tests/fuzz/corpus/` directory if one existed (`tests/fuzz/CMakeLists.txt:46-49`), but no such directory is in the tree, and `ci.yml` has no cache or artifact step for the corpus — coverage discovered by past fuzz runs is not persisted.
- **Enforcement:** enforced when it runs — no `continue-on-error` on the job; a crash fails the workflow. Same `main`/`develop` push gap as the sanitizers.
- **Empirical:** `Fuzz Testing` failed 6 of 6 sampled executions; `Optional Fuzz Testing` failed 1 of 5 ([[CI Run History (2026-06)]]).

## Coverage

- **Preset:** `coverage` — gcc-13 with gcov instrumentation, tests ON (`CMakePresets.json:104-118`); test preset at `CMakePresets.json:211-217`. A `coverage-check` custom target in CMake is self-described as "report-only src/app/ coverage" (`CMakeLists.txt:1050-1066`).
- **Workflow (report-only path):** `coverage` job (`.github/workflows/ci.yml:707-764`) — no `if:` condition, so it runs on every trigger tier. It builds instrumented, runs ctest, generates lcov output, and then *writes its policy into an artifact instead of asserting anything*: `echo "Coverage policy: report-only; no minimum threshold is enforced by CI yet." > coverage-policy.txt` (`.github/workflows/ci.yml:749`). Upload to Codecov happens only if a token secret is present (`.github/workflows/ci.yml:759-764`).
- **Workflow (enforced path):** the only numeric threshold lives in `release-validation`, which runs solely on `v*` tag pushes (`.github/workflows/ci.yml:877-879`): it extracts `src/app/`-scoped coverage and fails below 80% (`.github/workflows/ci.yml:907-921`). Per [[Build & CI System (Project Legends)]], the repository has no git tags, so this gate has never executed.
- **Enforcement:** report-only on every tier that actually runs (the ctest step inside the job is enforced, but no coverage number is); 80%-threshold tag-only, never yet triggered.
- **Empirical:** `Code Coverage` appears in the 30-run job sample with n=11 (median 502 s) and is absent from the nonzero-failure list — it passed its sampled executions ([[CI Run History (2026-06)]]).

## Determinism

- **Where the tests live:** the dedicated suite is `engine/tests/determinism/` — `test_determinism.cpp` plus `determinism_harness.h`, built as `aibox_determinism_tests` with CTest label `determinism` and TIMEOUT 120 (`engine/tests/determinism/CMakeLists.txt:12-14, 33-38`). Additional determinism tests ride in the general suites: `tests/integration/test_workflow_determinism.cpp`, `test_determinism_hash.cpp`, `test_replay_determinism.cpp` (`CMakeLists.txt:946, 968-969`) and `tests/unit/test_determinism_at_scale.cpp` (`CMakeLists.txt:708`).
- **What they hash:** the harness compares 32-byte state hashes obtained from `dosbox_lib_get_state_hash` (`engine/tests/determinism/determinism_harness.h:37-38, 93-96`) across two-instance runs, replay runs, and midpoint save/load round-trips (`engine/tests/determinism/determinism_harness.h:418-470`; replay hash-per-step comparison at `engine/tests/determinism/test_determinism.cpp:192-212`). Test programs are the hand-assembled COM fixtures in `tests/fixtures/` (`tests/fixtures/README.md`).
- **Documented oracle gaps:** the hash the architecture compares is weak. `AUDIT.md:110` (finding H7) records the `HashMode::Full` contract mismatch — the header documents memory/VGA/device hashing while the implementation appended only a `"FULL_MODE"` marker (`state_hash.h:41-43`, `state_hash.cpp:296-301`); the current re-verified status is "`HashMode::Full` now hashes memory, but VGA/device hashing remains outside the documented contract" with H7 still OPEN (`AUDIT.md:66`), and REQ-DT-004 remains a GAP (`AUDIT.md:482`). [[Concurrency & Determinism Audit (2026-06)]] (conc-07) goes further: the production entry point uses `HashMode::Fast`, whose CPU hash covers only cycle counters/flags and is blind to GPRs, EIP, EFLAGS, segment registers, and RAM contents, while Full mode has no callers — so the determinism tests "will report 'deterministic' through register or memory divergence." See [[Determinism Oracle Weakness]].
- **CMake preset / CI lane:** none dedicated. No preset, workflow job, or `ci.yml` step selects `-L determinism`; the determinism tests execute only as part of the undifferentiated `ctest` invocations inside the `linux`, `linux-ipc`, `windows`, `macos`, `coverage`, and `sanitizers` jobs (`.github/workflows/ci.yml:77, 127, 207, 279, 398-401, 737-738`). Locally, `test-determinism` runs the labeled suite (`engine/tests/determinism/CMakeLists.txt:41-45`).
- **Enforcement:** enforced only as ordinary ctest content inside the build jobs — there is no determinism-specific gate, and the oracle weakness means a pass certifies less than the lane's name implies.
- **Empirical:** no per-lane signal exists in [[CI Run History (2026-06)]] because determinism has no job of its own; its results are folded into the build-job conclusions.

## Related

- [[Project Legends Test Suite]] — the executables and labels these lanes run
- [[Build & CI System (Project Legends)]] — the workflow machinery hosting every lane
- [[CI Gate Coverage Map]] — trigger tiers and mandatory-gate status across all jobs
- [[CI Run History (2026-06)]] — empirical pass/fail per lane
- [[Determinism Oracle Weakness]] — why the determinism lane's green is not trustworthy
- [[Quality Gate Demotion (2026-06-08)]] — the event that reshaped which lanes gate at all

## R1 implementation state (2026-06-10, branch ci/r1-stabilize-lanes, PR #41)

The lane facts above describe master before the R1 change. As of PR #41:

- **ASan/UBSan**: green and enforced. The 191-failure alloc-dealloc-mismatch class was an uninstrumented-system-libc++/libc++abi false positive (`alloc_dealloc_mismatch=0`, ci.yml address leg); two real defects fixed: DOSBoxContext move ctor/assignment dropped memory/dma/dos/dos_filesystem ownership (engine/src/misc/dosbox_context.cpp), and the dosbox_error_code/dosbox_log_level FFI enums had UB value ranges (FORCE_INT sentinels).
- **TSan**: green and **enforced** — `allow_failure` removed after run 27304193585 passed 4511/4511 under the issue-linked `tsan-suppressions.txt` (#38, #39; both entries currently inert). Intentional wrong-thread tests skip under TSan in code. Matrix runs `fail-fast: false` so legs report independently.
- **MSan**: retired (matrix is address/undefined/thread); re-entry condition (instrumented libc++, nightly-only) tracked in #40.
- **Fuzz**: green — first actual execution of all five targets since the lane was made mandatory by `ee8a9e2`. Five successive latent build defects fixed (libc++ packages/flag, gsl-lite link, libFuzzer-runtime/libstdc++ interop, pal/platform_dirs link closures, missing config corpus). Zero crashes in the 30s smokes.
- **Dependency scan**: unmuted and renamed (no "Optional"); honest invocation found vendored fluidsynth CVEs (CVE-2021-21417, CVE-2025-56225) → #43, baselined in `osv-scanner.toml`; SBOM input tracked in #42; baseline dispatch 27316418663 green.
- **Demotion rule**: recorded in CONTRIBUTING.md — no allow-failure/mute/retirement/assertion-relaxation without a tracked exit criterion.

Coverage and determinism lanes are unchanged by R1 (see R9/R12 in `CI-THESIS.md`).
