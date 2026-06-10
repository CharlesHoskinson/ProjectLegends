---
type: entity
entity_kind: system
aliases: ["tests/", "fuzz targets", "benchmarks"]
tags: [entity, type/entity, topic/audit, topic/testing]
created: 2026-06-09
updated: 2026-06-10
status: draft
related:
  - "[[Determinism Oracle Weakness]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
sources:
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
---

# Project Legends Test Suite

## Overview

170 test files (~32k lines) in tests/ plus 82 in engine/tests, ~4,600 TEST macros, four fuzz targets, three benchmark files. The audit's verdict: broad but under-enforced, with oracles weakest exactly where the product's claims are strongest (determinism, save/load fidelity, IPC parity).

## Facts

- Overall verdict: wide but under-enforced, with weak oracles.^[from [[Test Coverage Audit (2026-06)]] — "wide but under-enforced, with weak oracles"]
- A quarter of registered integration tests are skip stubs that report green: 8 of 33 files.^[from [[Test Coverage Audit (2026-06)]] — "8 of 33 registered integration test files"]
- A real boot-to-prompt test is the suite's strongest end-to-end check.^[from [[Test Coverage Audit (2026-06)]] — "the single strongest end-to-end assertion in the suite"]
- IPC unit tests round-trip only well-formed messages — benign, not adversarial.^[from [[Security Audit (2026-06)]] — "those are well-formed inputs, not adversarial"]
- The determinism test architecture is sound; the hash it compares is not.^[from [[Concurrency & Determinism Audit (2026-06)]] — "The test architecture is good"]
- The engine event-scheduler queue is still outside V5 serialization, keeping a save-state test PARTIAL.^[from [[Backlog Verification Audit (2026-06)]] — "engine event-scheduler queue still not serialized"]
- Stated test strictness is contradicted by -Wno-error on the test targets.^[from [[Build & CI Audit (2026-06)]] — "tests should be strict too"]
- The promised soak suite cannot run: no workflow enables it and the cmake label does not exist.^[from [[Build & CI Audit (2026-06)]] — "finds no SOAK reference"]
- Coverage is report-only on pushes; no minimum threshold is enforced.^[from [[Test Coverage Audit (2026-06)]] — "no minimum threshold is enforced by CI yet"]
- The architecture audit recommends one parameterized conformance suite run against both runtimes.^[from [[API & Architecture Audit (2026-06)]] — "Write a single parameterized conformance test suite"]

## Test infrastructure inventory (2026-06-10)

Current-state inventory read directly from the repository working tree (2026-06-10). Citations below are repo file paths, not audit-report quotes. Lane-by-lane enforcement detail lives in [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]; which CI jobs run these executables and on which trigger tier is mapped in [[CI Gate Coverage Map]] and [[Build & CI System (Project Legends)]].

### Test executables and how each is registered

Seven CTest-visible executables across two CMake trees. The root tree is gated by `LEGENDS_BUILD_TESTS` (`CMakeLists.txt:34`, block opens at `CMakeLists.txt:611`); the engine tree by `AIBOX_BUILD_TESTS`, default ON (`engine/CMakeLists.txt:18`, `engine/CMakeLists.txt:323`, `enable_testing()` at `engine/CMakeLists.txt:342`, `add_subdirectory(tests)` at `engine/CMakeLists.txt:346`).

| Executable | Defined at | Registered via | Labels / timeout |
|---|---|---|---|
| `legends_unit_tests` | `CMakeLists.txt:629` | `gtest_discover_tests`, `CMakeLists.txt:819-824` | `unit`; TIMEOUT 30 |
| `legends_ipc_integration_tests` | `CMakeLists.txt:831` (only under `LEGENDS_USE_IPC`, `CMakeLists.txt:830`) | `gtest_discover_tests`, `CMakeLists.txt:853-856` | `integration;ipc` |
| `legends_abi_test` (pure C11) | `CMakeLists.txt:863-871` | plain `add_test`, `CMakeLists.txt:881-884` | `abi;unit` via `set_tests_properties`, `CMakeLists.txt:886-888` |
| `legends_toolchain_tests` | `CMakeLists.txt:912-915` | `gtest_discover_tests`, `CMakeLists.txt:929-932` | `toolchain` |
| `legends_integration_tests` | `CMakeLists.txt:944-984` (30 sources) | `gtest_discover_tests`, `CMakeLists.txt:1014-1019` | `integration`; TIMEOUT 60 |
| `aibox_unit_tests` | `engine/tests/CMakeLists.txt:23-92` | `gtest_discover_tests`, `engine/tests/CMakeLists.txt:111-115` | `unit` |
| `aibox_determinism_tests` | `engine/tests/determinism/CMakeLists.txt:12-14` | `gtest_discover_tests`, `engine/tests/determinism/CMakeLists.txt:33-38` | `determinism`; TIMEOUT 120 |

- `legends_abi_test` is the only test registered at configure time; everything else is discovered at CTest time, which is why configure-time `set_tests_properties` cannot relabel discovered tests (comment at `CMakeLists.txt:1023-1028`).
- Engine integration tests are a commented-out placeholder (`engine/tests/CMakeLists.txt:121-136`).
- The five libFuzzer harnesses plus `generate_fuzz_corpus` build only under `ENABLE_FUZZING` (`CMakeLists.txt:1074-1075`, option at `CMakeLists.txt:41`) and are never CTest-registered — `tests/fuzz/CMakeLists.txt` contains no `add_test` or `gtest_discover_tests`; the harnesses are Clang-only (`tests/fuzz/CMakeLists.txt:63-67`).
- Both `legends_unit_tests` and `legends_integration_tests` compile with `-Wno-error` on GCC/Clang (`CMakeLists.txt:815-817`, `CMakeLists.txt:1010-1012`), consistent with the Build & CI Audit fact above.
- Three integration sources are compiled into no target at all: `tests/integration/test_context_synchronization.cpp`, `tests/integration/test_dual_ffi.cpp`, and `tests/integration/test_error_propagation.cpp` appear in no CMakeLists (the `legends_integration_tests` source list at `CMakeLists.txt:944-984` omits them; `test_ipc_integration.cpp` has its own target). By contrast, all 124 unit `.cpp` files on disk are in the `legends_unit_tests` source list.

### Directory layout under tests/

- `tests/unit/` — 124 gtest `.cpp` files plus the pure-C `test_legends_abi.c`; flat `test_<area>.cpp` naming (e.g. `test_ipc_*` for the six IPC codec/transport files, `test_pal_*` for PAL backends). The former `test_legends_embed.cpp` monolith now coexists with five split files: `test_legends_embed_{lifecycle,capture,input,savestate,security}.cpp`. Shared fixture headers live in `tests/unit/test_utils/`.
- `tests/integration/` — 34 `.cpp` files; end-to-end scenario files prefixed `test_workflow_*`, the rest `test_<feature>.cpp` (e.g. `test_boot_to_prompt.cpp`, `test_soak_endurance.cpp`). Shared fixture in `tests/integration/test_utils/integration_fixture.h`.
- `tests/fuzz/` — five harnesses (`fuzz_legends_load_state.cpp`, `fuzz_engine_load_state.cpp`, `fuzz_engine_memory_blob.cpp`, `fuzz_input_injection.cpp`, `fuzz_config_parser.cpp`) plus `generate_corpus.cpp` and its own `CMakeLists.txt`.
- `tests/fixtures/` — three hand-assembled real-mode COM programs (`counter.com`, `graphics.com`, `input.com`) with byte-level documentation in `tests/fixtures/README.md`; used by determinism and CPU-execution tests.
- `tests/scripts/` — `test_verify_gpl_isolation.py`, a Python test for `scripts/verify_gpl_isolation.py`; referenced by no CMakeLists, workflow, or cmake module (its subject script is wired via `cmake/VerifyGPLIsolation.cmake:21`, but the test itself has no runner).
- `tests/toolchain/` — `test_cpp_standard.cpp` and `test_shell_h_headless.cpp`, the C++23/headless gate tests.

> [!conflict] The Overview above says "four fuzz targets" (from [[Test Coverage Audit (2026-06)]]). As of 2026-06-10 five harnesses exist on disk and five CMake targets are defined — `fuzz_config_parser` at `tests/fuzz/CMakeLists.txt:224-248` implements Task 7 of `docs/superpowers/plans/2026-03-20-plan-2-test-infrastructure.md`, which had flagged "source exists but no CMake target" (`docs/superpowers/plans/2026-03-20-plan-2-test-infrastructure.md:239`). The four-target count predates this target.

### CTest labels in use

| Label | Applied to | Selected/excluded where |
|---|---|---|
| `unit` | `legends_unit_tests` (`CMakeLists.txt:822`), `aibox_unit_tests` (`engine/tests/CMakeLists.txt:114`), `legends_abi_test` (`CMakeLists.txt:887`) | `ctest -L unit` in `legends-test-unit` (`CMakeLists.txt:894-898`) and engine `test-unit` (`engine/tests/CMakeLists.txt:149-153`) |
| `integration` | `legends_integration_tests` (`CMakeLists.txt:1017`), `legends_ipc_integration_tests` (`CMakeLists.txt:855`) | `ctest -L integration --label-exclude soak` in `test-integration` (`CMakeLists.txt:1030-1034`) |
| `ipc` | `legends_ipc_integration_tests` (`CMakeLists.txt:855`) | no custom target selects it |
| `abi` | `legends_abi_test` (`CMakeLists.txt:887`) | `ctest -L abi` in `test-abi` (`CMakeLists.txt:902-906`) |
| `toolchain` | `legends_toolchain_tests` (`CMakeLists.txt:931`) | `ctest -L toolchain` in `test-toolchain` (`CMakeLists.txt:934-938`) |
| `determinism` | `aibox_determinism_tests` (`engine/tests/determinism/CMakeLists.txt:36`) | `ctest -L determinism` in `test-determinism` (`engine/tests/determinism/CMakeLists.txt:41-45`) |
| `soak` | **nothing** — see below | excluded by `test-integration` (`CMakeLists.txt:1031`), `legends-test-all` (`CMakeLists.txt:1045`), and the release-validation ctest invocation (`.github/workflows/ci.yml:905`); selected only by `test-soak` (`CMakeLists.txt:1037-1041`, 13 h timeout) |

The `soak` label is referenced but never applied. The comment at `CMakeLists.txt:1021-1028` defers label application to `cmake/SoakTestLabels.cmake` "(if present)" — no such file exists under `cmake/`. Consequently the soak endurance tests in `tests/integration/test_soak_endurance.cpp` (compiled in at `CMakeLists.txt:965`) carry the ordinary `integration` label with TIMEOUT 60, `ctest -L soak` selects zero tests, and every `--label-exclude soak` excludes nothing. This matches the existing fact above ("the cmake label does not exist") — still true at 2026-06-10.

### Fixture status vs the 2026-03-20 plan

`docs/superpowers/plans/2026-03-20-plan-2-test-infrastructure.md` planned shared fixtures (Tasks 1-4), the embed-test split (Task 5), a `legends_app` library (Task 6), the `fuzz_config_parser` target (Task 7), and a unit-test TIMEOUT (Task 8). All eight deliverables exist in the tree:

- `tests/unit/test_utils/temp_file_fixture.h` (Task 1, plan lines 13-23) — exists.
- `tests/unit/test_utils/pal_headless_fixture.h` (Task 2, plan lines 100-106) — exists.
- `tests/unit/test_utils/ipc_test_helpers.h` (Task 3, plan lines 141-151) — exists.
- `tests/integration/test_utils/integration_fixture.h` (Task 4, plan lines 161-173) — exists.
- Embed split files (Task 5, plan lines 185-196) — all five exist in `tests/unit/`, and are compiled alongside the residual `test_legends_embed.cpp`.
- `legends_app` library (Task 6, plan lines 210-227) — `legends_unit_tests` links `legends_app` (`CMakeLists.txt:782-784`).
- `fuzz_config_parser` target (Task 7, plan lines 237-248) — `tests/fuzz/CMakeLists.txt:224-248`.
- TIMEOUT 30 on unit discovery (Task 8, plan lines 252-259) — `CMakeLists.txt:823`.

The `tests/unit/test_utils/` headers are wired into the unit target via `target_include_directories(... tests/unit ...)` (`CMakeLists.txt:800`); the engine tree has its own separate INTERFACE fixtures library `aibox_test_fixtures` (`engine/tests/CMakeLists.txt:9-17`).

### Which CMake presets enable which suites

From `CMakePresets.json` (configure presets at lines 8-133, test presets at lines 168-218):

| Preset | Suites enabled | Test preset? |
|---|---|---|
| `dev` / `dev-mingw` (`CMakePresets.json:28-46`) | `LEGENDS_BUILD_TESTS=ON` → all seven CTest executables (unit, integration, toolchain, abi, engine unit, engine determinism; IPC suite absent — no `LEGENDS_USE_IPC`) | yes (`CMakePresets.json:169-182`) |
| `release` (`CMakePresets.json:48-55`) | none — no test cache variable | no |
| `asan` (`CMakePresets.json:56-74`) | same suites as dev, under ASan+UBSan (clang-18, libc++) | yes (`CMakePresets.json:183-193`) |
| `tsan` (`CMakePresets.json:75-92`) | same suites as dev, under TSan | yes (`CMakePresets.json:194-203`) |
| `ipc` (`CMakePresets.json:93-103`) | dev suites **plus** `legends_ipc_integration_tests` via `LEGENDS_USE_IPC=ON` (`CMakeLists.txt:830`) | yes (`CMakePresets.json:204-210`) |
| `coverage` (`CMakePresets.json:104-118`) | same suites as dev, gcc-13 with gcov instrumentation | yes (`CMakePresets.json:211-217`) |
| `fuzz` (`CMakePresets.json:119-132`) | dev suites plus the five fuzz harnesses (`ENABLE_FUZZING=ON`, `ENABLE_ASAN=ON`) | **no** — fuzz harnesses are not CTest tests; they run via the `fuzz-all`/`fuzz-quick` custom targets (`tests/fuzz/CMakeLists.txt:254-271`) |

No preset exists for MSan; MemorySanitizer appears only as a CI matrix entry (see [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]). No preset or custom target enables a working soak run, since the `soak` label matches nothing.

## Related

- [[Determinism Oracle Weakness]] — the suite's central blind spot
- [[Quality Gate Demotion (2026-06-08)]] — why even existing tests stopped gating
- [[IPC Trust Boundary Gaps]] — the untested boundary
- [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]] — enforcement status of each verification lane that runs this suite
