---
type: entity
entity_kind: system
aliases: ["ci.yml", "CMake build system"]
tags: [entity, type/entity, topic/audit, topic/ci]
created: 2026-06-09
updated: 2026-06-10
status: draft
related:
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Licensing Inconsistency]]"
sources:
  - "[[Build & CI Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
---

# Build & CI System (Project Legends)

## Overview

Root CMakeLists (63KB) + engine CMake + cmake/ modules + four GitHub workflows + githooks + Python check scripts. Impressive machinery on paper — much of it not actually wired to anything that gates a merge, builds the app, or has ever executed (the release pipeline has literally never run).

## Facts

- The machinery has unusual breadth: a 4-sanitizer matrix, libFuzzer jobs, 17 TLA+ model-checking steps.^[from [[Build & CI Audit (2026-06)]] — "a 4-sanitizer matrix, libFuzzer jobs, 17 TLA+ model-checking steps"]
- The repository has no git tags, so the tag-gated release pipeline and coverage release gate have never executed.^[from [[Build & CI Audit (2026-06)]] — "the repository has no git tags"]
- No workflow uses compiler caching; the 1M-line engine rebuilds cold up to ~12 times per push.^[from [[Build & CI Audit (2026-06)]] — "No workflow uses ccache/sccache"]
- PRs targeting develop bypass the primary pipeline; breakage is discovered only after merge.^[from [[Build & CI Audit (2026-06)]] — "Breakage is discovered only after merge"]
- All FetchContent pins are mutable git tags with no integrity hash.^[from [[Build & CI Audit (2026-06)]] — "All FetchContent pins are mutable git"]
- The IPC CI job never builds the application, masking the boot and link failures.^[from [[API & Architecture Audit (2026-06)]] — "CI never sees any of this"]
- Pre-merge CI is headless-only; SDL backends get no pre-merge execution.^[from [[Test Coverage Audit (2026-06)]] — "CI is headless-only; SDL-backend tests are path-filtered/nightly"]
- Benchmarks exist but are never built in CI; performance can regress silently.^[from [[Test Coverage Audit (2026-06)]] — "Benchmarks exist but are never built in CI"]
- The GPL symbol-isolation scan — the core compliance guarantee — is unenforced.^[from [[Security Audit (2026-06)]] — "This is the core GPL-compliance guarantee and it is unenforced"]
- The isolation verifier is documented as a CI gate but is never executed.^[from [[Docs & Licensing Audit (2026-06)]] — "documented as a CI gate but is never executed"]
- The 2026-06-08 stabilization work itself is verified as landed.^[from [[Backlog Verification Audit (2026-06)]] — "CIFix.md work is in place"]

## Build system inventory (2026-06-10)

Direct inventory from the repo files (branch ci-audit working tree); citations are repo paths relative to `C:\projectLegends\`.

### Configure presets (CMakePresets.json)

`CMakePresets.json` (schema version 6, requires CMake >= 3.25, `CMakePresets.json:2-6`) defines **9 configure presets** — 2 hidden bases plus 7 concrete — alongside 8 build presets (`CMakePresets.json:134-167`) and 6 test presets (`CMakePresets.json:168-218`).

| Preset | Generator | Compiler | Build type | Key cache vars | Tests |
|---|---|---|---|---|---|
| `default` (hidden) | MinGW Makefiles | unset | unset | `LEGENDS_HEADLESS=ON` (`CMakePresets.json:10-17`) | OFF (default) |
| `default-ninja` (hidden) | Ninja | unset | unset | `LEGENDS_HEADLESS=ON` (`CMakePresets.json:19-26`) | OFF (default) |
| `dev` | Ninja (inherits default-ninja) | unset | Debug | — (`CMakePresets.json:28-36`) | ON |
| `dev-mingw` | MinGW Makefiles (inherits default) | unset | Debug | — (`CMakePresets.json:38-46`) | ON |
| `release` | Ninja | unset | Release | — (`CMakePresets.json:48-55`) | OFF (not set) |
| `asan` | Ninja | clang-18 / clang++-18 | Debug | `-stdlib=libc++ -fsanitize=address,undefined -fno-omit-frame-pointer` via `CMAKE_CXX_FLAGS`; `ASAN_OPTIONS`/`UBSAN_OPTIONS` env (`CMakePresets.json:57-74`) | ON |
| `tsan` | Ninja | clang-18 / clang++-18 | Debug | `-fsanitize=thread`; `TSAN_OPTIONS` env (`CMakePresets.json:76-92`) | ON |
| `ipc` | Ninja | unset | Debug | `LEGENDS_USE_IPC=ON` (`CMakePresets.json:94-103`) | ON |
| `coverage` | Ninja | gcc-13 / g++-13 | Debug | `--coverage -fprofile-arcs -ftest-coverage` (`CMakePresets.json:105-118`) | ON |
| `fuzz` | Ninja | clang-18 / clang++-18 | Release | `ENABLE_FUZZING=ON`, `ENABLE_ASAN=ON` (`CMakePresets.json:120-132`) | ON |

Sanitizers in presets are passed as raw `CMAKE_CXX_FLAGS`/`CMAKE_EXE_LINKER_FLAGS` strings (asan/tsan/coverage), not via the `ENABLE_*` options — only `fuzz` uses the option-based path.

**No GitHub workflow invokes any preset.** `grep -- --preset` over `.github/workflows/` returns nothing; all four workflows (`ci.yml`, `module-dag.yml`, `pal-ci.yml`, `sprint2-checks.yml`) configure with explicit `cmake -B build` flag lists. CI jobs *replicate* preset configurations by hand: the linux-ipc job mirrors `ipc` plus a gcc-13 pin (`.github/workflows/ci.yml:110-116`), the sanitizers matrix mirrors `asan`/`tsan` flags and adds standalone `undefined` and `memory` configs that have no preset (`.github/workflows/ci.yml:340-374`), the fuzz job mirrors `fuzz` (`.github/workflows/ci.yml:499-505`), and the coverage job mirrors `coverage` (`.github/workflows/ci.yml:724-730`). `dev`, `dev-mingw`, and `release` have no CI counterpart with the same flag set (CI's linux job is Release **with** tests, `.github/workflows/ci.yml:65-71`; the `release` preset has no tests). All presets are therefore local-developer-use only as invoked artifacts.

### Build options (root CMakeLists.txt)

| Option | Default | Gates |
|---|---|---|
| `LEGENDS_BUILD_TESTS` | OFF | `enable_testing()` + GoogleTest fetch + all test targets (`CMakeLists.txt:34`, `:611-623`) |
| `LEGENDS_HEADLESS` | OFF | `LEGENDS_HEADLESS=1` compile definition on legends_core (`CMakeLists.txt:35`, `:212`) |
| `LEGENDS_LIBRARY_MODE` | OFF | `LEGENDS_LIBRARY_MODE=1` compile definition (`CMakeLists.txt:36`, `:213`) |
| `LEGENDS_USE_IPC` | OFF | builds `legends_engine_host` + `legends_proxy`; switches app link from legends_core to legends_proxy (`CMakeLists.txt:37`, `:373-435`, `:1177-1184`) |
| `LEGENDS_BUILD_WASM` | OFF | Wasm/WASI scaffold; CMakeLists' own comment calls it "a planned scaffold: the referenced wasm.md and wit/legends-emulator.wit artifacts are not present at HEAD" (`CMakeLists.txt:38`, `:451-453`) |
| `ENABLE_FUZZING` | OFF | `add_subdirectory(tests/fuzz)` (`CMakeLists.txt:41`, `:1074-1076`) |
| `ENABLE_ASAN` / `ENABLE_UBSAN` / `ENABLE_MSAN` | OFF | consumed only inside `tests/fuzz/CMakeLists.txt:85-106` — they sanitize fuzz targets only, not the main build (`CMakeLists.txt:42-44`) |
| `PAL_BACKEND_HEADLESS` | **ON** | headless PAL sources + `PAL_HAS_HEADLESS=1` (`CMakeLists.txt:47`, `:297`) |
| `PAL_BACKEND_SDL2` | OFF | SDL2 PAL backend; also the **only** condition under which the `project_legends` main executable is built (`CMakeLists.txt:48`, `:1155-1156`) |
| `PAL_BACKEND_SDL3` | OFF | SDL3 PAL backend + SDL3 dependency resolution (`CMakeLists.txt:49`, `cmake/dependencies.cmake:55-74`) |
| `PAL_DEFAULT_BACKEND` | `"Headless"` (cache string) | baked into `legends_pal` as a compile definition (`CMakeLists.txt:50`, `:300`) |
| `LEGENDS_ENABLE_AI` | OFF | optional libcurl lookup (find-only, stub fallback) (`CMakeLists.txt:53`, `cmake/dependencies.cmake:83-90`) |
| `LEGENDS_ENABLE_FLUIDSYNTH` | OFF | optional FluidSynth lookup (find-only) (`CMakeLists.txt:54`, `cmake/dependencies.cmake:99-106`) |
| `LEGENDS_ENABLE_MT32` | OFF | mt32emu try-find-then-fetch (`CMakeLists.txt:55`, `cmake/dependencies.cmake:115-129`) |
| `LEGENDS_BUILD_BENCHMARKS` | OFF | declared mid-file, not in the options block; gates Google Benchmark fetch + 3 benchmark targets (`CMakeLists.txt:1082-1147`) |

The engine subdirectory's own options are force-set by the root: `AIBOX_BUILD_TESTS=ON`, `AIBOX_HEADLESS=ON`, `AIBOX_LIBRARY_MODE=ON` (all `CACHE BOOL ... FORCE`, `CMakeLists.txt:165-167`).

### Two-tier warning policy

Implemented in `CMakeLists.txt:66-138`. Warning/hardening flags live on an INTERFACE library `legends_compile_options` (`-Wall -Wextra -Wpedantic`, `-fstack-protector-strong -D_FORTIFY_SOURCE=2`, PIE on non-Windows; MSVC `/W4 /permissive- /utf-8`, `/GUARD:CF`) precisely so they do not leak into FetchContent dependencies (`CMakeLists.txt:73-105`).

- **Tier A** — `legends_set_strict_cxx_standard()` (`CMakeLists.txt:108-123`): links the interface library, sets C++23, then adds `-Werror` (GCC/Clang) or `/std:c++23preview /WX` (MSVC). Applied to 14 targets: `legends_core` (:189), `legends_pal` (:287), `legends_ipc` (:346), `legends_engine_host` (:381), `legends_proxy` (:413), `legends_app` (:561), `legends_unit_tests` (:780), `legends_ipc_integration_tests` (:835), `legends_toolchain_tests` (:918), `legends_integration_tests` (:986), `pal_benchmarks` (:1098), `emulation_benchmarks` (:1114), `legends_ipc_benchmarks` (:1135), and `project_legends` (:1162, :1271).
- **Tier B** — `legends_set_legacy_cxx_standard()` (`CMakeLists.txt:126-138`): same interface library and C++23, no `-Werror`. **The function is defined but never called by any CMakeLists in the tree** (grep over the repo finds only the definition and a CONTRIBUTING.md mention). The legacy engine target `aibox_core` instead gets `-Wall -Wextra -Wpedantic -Wno-unused-parameter` (no `-Werror`) via directory-scope `add_compile_options` in `engine/CMakeLists.txt:75-81` (MSVC: `/W4 /wd4100`, `engine/CMakeLists.txt:117-122`) — de facto Tier B treatment through a different mechanism. `CONTRIBUTING.md:157` states Tier B is "Applied via `legends_set_legacy_cxx_standard()`", which does not match the code.
- The audit-local build script works around Tier A by passing `-DLEGENDS_WERROR=OFF` (`llm-wiki/_scratch/build.cmd:6`), but **no CMake file in the repo reads a `LEGENDS_WERROR` variable** (grep returns nothing) — the flag is inert; there is no built-in switch to disable Tier A's `-Werror`.

### Dependencies (cmake/dependencies.cmake)

Version pins are centralized as cache strings (`cmake/dependencies.cmake:19-26`). All git pins are tags, none has a commit hash or `URL_HASH`.

| Dependency | Pin | Strategy | Gated by |
|---|---|---|---|
| gsl-lite | `v1.0.0` | try `find_package(gsl-lite 1.0 QUIET)` then FetchContent (`cmake/dependencies.cmake:36-46`) | always |
| SDL3 | `release-3.2.8` | try `find_package(SDL3 QUIET)` then FetchContent, `GIT_SHALLOW` (`cmake/dependencies.cmake:61-73`) | `PAL_BACKEND_SDL3` |
| GoogleTest | `v1.14.0` | fetch-only (no find_package), declared in root CMakeLists (`CMakeLists.txt:615-621`) | `LEGENDS_BUILD_TESTS` |
| Google Benchmark | `v1.8.3` | fetch-only, declared in root CMakeLists (`CMakeLists.txt:1085-1091`) | `LEGENDS_BUILD_BENCHMARKS` |
| libcurl | none | find-only; "stub implementation" fallback if absent (`cmake/dependencies.cmake:84-89`) | `LEGENDS_ENABLE_AI` |
| FluidSynth | `v2.3.5` (pin declared but unused — no FetchContent_Declare) | find-only; feature unavailable if absent (`cmake/dependencies.cmake:25`, `:100-105`) | `LEGENDS_ENABLE_FLUIDSYNTH` |
| mt32emu (MUNT) | `v2.7.0` | try find_package then FetchContent, `GIT_SHALLOW`, `SOURCE_SUBDIR mt32emu` (`cmake/dependencies.cmake:115-129`) | `LEGENDS_ENABLE_MT32` |

### ModuleManifest / ModuleDAG enforcement

`cmake/ModuleManifest.cmake` declares six modules with public/private include roots and a target each: legends (`legends_core`), pal (`legends_pal`), engine (`aibox_core`), ipc (`legends_ipc`, MIT), proxy (`legends_proxy`, MIT), engine_host (`legends_engine_host`, GPL-2.0) (`cmake/ModuleManifest.cmake:7-51`). Allowed edges (`cmake/ModuleManifest.cmake:63-68`): `legends_core → aibox_core`; `legends_pal`, `aibox_core`, `legends_ipc` are leaves; `legends_proxy → legends_ipc`; `legends_engine_host → legends_core;legends_ipc`. The manifest also carries a public-header allowlist and forbidden include patterns (`../src/`, `../../`, `engine/src/`) (`cmake/ModuleManifest.cmake:74-90`).

`cmake/ModuleDAG.cmake` fails configure with `FATAL_ERROR` when a verified target links an internal target not in its manifest edge list (`cmake/ModuleDAG.cmake:92-105`), when Kahn's-algorithm cycle detection finds a cycle (`cmake/ModuleDAG.cmake:170-176`), or when the manifest was not included first (`cmake/ModuleDAG.cmake:12-14`). External deps matching whitelist patterns (`gsl::`, `GTest::`, `SDL*`, `benchmark::`, generator expressions, linker flags, mingw, `legends_compile_options`) are always allowed (`cmake/ModuleDAG.cmake:52-61`). The entry point `legends_verify_all_dags()` runs at the end of configure (`CMakeLists.txt:1408`) but **verifies only `legends_core`, `legends_pal`, and `aibox_core`** (`cmake/ModuleDAG.cmake:196-206`); cycle detection likewise hard-codes only those three modules (`cmake/ModuleDAG.cmake:124`). `legends_ipc`, `legends_proxy`, and `legends_engine_host` — the three license-critical targets — are never passed to `legends_verify_dag`. A dedicated `module-dag.yml` workflow configures the project and greps configure output for "DAG" / "FATAL_ERROR" rather than relying on exit codes alone (`.github/workflows/module-dag.yml:105-130`).

### IPC license-split targets and their build-time guard

Under `LEGENDS_USE_IPC=ON` (`CMakePresets.json:101`; ci.yml linux-ipc job, `.github/workflows/ci.yml:116`):

- `legends_ipc` (STATIC, MIT) — serialization, shared memory, control channel, engine spawner; links only `gsl::gsl-lite-v1` (`CMakeLists.txt:332-360`).
- `legends_engine_host` (executable, GPL-2.0) — links `legends_core` + `legends_ipc` (`CMakeLists.txt:373-395`).
- `legends_proxy` (STATIC, MIT) — implements the `legends_embed.h` C API over IPC; links only `legends_ipc` (`CMakeLists.txt:405-435`).
- The app executable links `legends_proxy + legends_pal` instead of `legends_core` in IPC mode (`CMakeLists.txt:1175-1184`), "removing all GPL object code from the binary" (`CMakeLists.txt:440-442`).

What guards the split at build time, as of this inventory: **comments and unchecked manifest entries only.** The no-GPL-links rule for `legends_ipc` and `legends_proxy` exists as comments citing REQ-ISO-003/REQ-ISO-016 (`CMakeLists.txt:362-363`, `:423-424`); the DAG verifier skips all three IPC-split targets (`cmake/ModuleDAG.cmake:196-206`); and `cmake/VerifyGPLIsolation.cmake` (the linker-map scan, "Usage: include(VerifyGPLIsolation) after defining the project_legends target", `cmake/VerifyGPLIsolation.cmake:8`) is included by no CMakeLists and referenced by no workflow. The linux-ipc CI job's post-build check only asserts the two IPC executables/libraries exist on disk (`.github/workflows/ci.yml:121-125`). This corroborates the 2026-06-09 facts above; it is consistency, not conflict.

### build.cmd

There is **no `build.cmd` at the repo root**. The only `build.cmd` in the tree is the audit-local scratch script `llm-wiki/_scratch/build.cmd` (the `llm-wiki/` directory is git-excluded). It: (1) sources the VS 2022 BuildTools `vcvars64.bat`; (2) if `ninja` is on PATH, configures with `cmake --preset dev -DLEGENDS_WERROR=OFF` and builds `build/dev`; (3) otherwise falls back to a Visual Studio 17 2022 x64 configure into `build/dev-vs` with `-DLEGENDS_BUILD_TESTS=ON -DLEGENDS_WERROR=OFF` and a Debug build; logs go to `llm-wiki/_scratch/configure.log` and `build.log`, and it echoes `BUILD_OK`/`CONFIGURE_FAILED`/`BUILD_FAILED` (`llm-wiki/_scratch/build.cmd:1-16`). Its own comment marks the `-Werror` bypass as "AUDIT-LOCAL (2026-06-05) ... so audit build compiles through F-009 discards" (`llm-wiki/_scratch/build.cmd:5`); as noted above, `LEGENDS_WERROR` is consumed by nothing in the CMake tree, so the dev-preset path still builds with Tier A `-Werror` active.

## Related

- [[Quality Gate Demotion (2026-06-08)]] — its acute failure mode
- [[Licensing Inconsistency]] — the unwired isolation enforcement
- [[Project Legends Test Suite]] — what the gates do (and don't) run
