# Design: presets-single-source

## Context

`CMakePresets.json` (schema v6, CMake >= 3.25) defines 2 hidden + 7 concrete configure presets, 8 build presets, 6 test presets. `grep -- --preset .github/workflows/` returns nothing; every job hand-rolls its flags (audit-wiki/wiki/entities/Build & CI System (Project Legends).md). Drift is live: the `asan` preset is address+undefined combined while CI runs them as separate matrix legs; the linux-ipc job mirrors the `ipc` preset plus a gcc-13 pin; CI's Windows, library-mode, and PAL jobs match no preset at all.

Constraints inherited from sibling changes:

- `ci-stabilize-mandatory-lanes` (R1) retires the MSan matrix cell — no `msan` preset, ever (Recommendation Review row G-7). It also adds `suppressions=` to the `tsan` preset's `TSAN_OPTIONS`; this change must not clobber that.
- `master-ruleset-required-checks` (R2) binds the exact check names `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`. Migration changes step bodies only; no job or display name changes.
- `preflight-gate-entrypoint` (R3) consumes the presets added here for its OS-reachable build/test legs.
- Dev environment is Windows (MSVC, no WSL) + Linux; `cmake --list-presets` on Windows must show only runnable presets (Recommendation Review rows M-2, A-1).

## Goals / Non-Goals

**Goals:**

- Every `cmake -B` / `cmake --build` / `ctest --test-dir` step in the four workflows becomes `cmake --preset` / `cmake --build --preset` / `ctest --preset`.
- Every CI build cell that survives R1 has a named preset; preset flags equal current CI flags except where a divergence is recorded below.
- Windows preset listings contain no Linux-only entries; Linux listings contain no Windows-only entries.

**Non-Goals:**

- No trigger, tier, `if:`, path-filter, or job-name changes (R2/R6/R8 territory).
- No `workflowPresets` section — R8's reusable workflow decides whether chained presets earn their keep; adding them now would duplicate the migration.
- No ctest-label or gtest-filter changes: steps that invoke test binaries directly (`--gtest_filter`) keep doing so; label migration is `test-estate-truth` (R12/M-6).
- No new sanitizer cells, no compiler caching (R14), no SDL3 source-build pinning (R14).

## Decisions

### D1 — Preset architecture: hidden toolchain bases + thin concrete presets

Two new hidden bases factor the compiler pins the CI matrix uses:

- `toolchain-gcc13` — `CMAKE_C_COMPILER=gcc-13`, `CMAKE_CXX_COMPILER=g++-13`; condition `${hostSystemName} == Linux`.
- `toolchain-clang18` — `CMAKE_C_COMPILER=clang-18`, `CMAKE_CXX_COMPILER=clang++-18`, `-stdlib=libc++` CXX/linker flags; condition `${hostSystemName} == Linux`.

Conditions are inherited, so every preset inheriting a toolchain base is automatically Linux-guarded. Alternative considered: per-preset duplicate pins (status quo pattern) — rejected; the pin drift between CI and presets is the bug this change fixes.

### D2 — Final configure-preset set

| Preset | Status | Definition (delta from inherits) | Guard |
|---|---|---|---|
| `default`, `default-ninja` | existing, modified | gain `CMAKE_EXPORT_COMPILE_COMMANDS=ON` (D8) | — |
| `dev`, `dev-mingw`, `release` | existing, unchanged | — | — |
| `release-tests` | **new** | default-ninja + Release + `LEGENDS_BUILD_TESTS=ON` | none (any OS) |
| `linux-gcc` | **new** | release-tests + toolchain-gcc13 | Linux (inherited) |
| `linux-clang` | **new** | release-tests + toolchain-clang18 | Linux (inherited) |
| `windows-msvc` | **new** | generator `Visual Studio 17 2022`, architecture `x64`, `LEGENDS_BUILD_TESTS=ON`, `LEGENDS_HEADLESS=ON` | Windows |
| `asan` | existing, **modified** | drops `,undefined` from all three sanitize flag strings; drops `UBSAN_OPTIONS` env; gains toolchain-clang18 inherit | Linux |
| `ubsan` | **new** | toolchain-clang18 + Debug + `-fsanitize=undefined -fno-omit-frame-pointer` flags + `UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1` env + tests | Linux |
| `tsan` | existing, modified | gains toolchain-clang18 inherit (flags unchanged; keep R1's `suppressions=` if landed) | Linux |
| `ipc` | existing, unchanged flags | — | none |
| `coverage` | existing, modified | guard only (flags already gcc-13-pinned) | Linux |
| `fuzz` | existing, modified | guard only | Linux |
| `library-mode` | **new** | toolchain-gcc13 + Release + tests + `LEGENDS_LIBRARY_MODE=ON` | Linux |
| `pal-headless` | **new** | toolchain-gcc13 + Debug + tests + explicit `PAL_BACKEND_HEADLESS=ON`, `PAL_BACKEND_SDL2=OFF`, `PAL_BACKEND_SDL3=OFF` | Linux |
| `pal-sdl2` | **new** | pal-headless + `PAL_BACKEND_SDL2=ON` | Linux |
| `pal-sdl3` | **new** | pal-headless + `PAL_BACKEND_SDL3=ON`, `PAL_DEFAULT_BACKEND=SDL3` | Linux |
| `package` | **new** | Ninja, Release, `PAL_BACKEND_SDL3=ON`, `LEGENDS_HEADLESS=OFF` | not-Windows |
| `package-windows` | **new** | VS 17 2022 + x64, `PAL_BACKEND_SDL3=ON`, `LEGENDS_HEADLESS=OFF` | Windows |

No `msan` preset (R1). `ubsan` uses raw `-fsanitize=undefined` flag strings like `asan`/`tsan`, not the `ENABLE_UBSAN` option — that option only sanitizes fuzz targets (CMakeLists.txt:42-44, tests/fuzz/CMakeLists.txt:85-106).

Each new configure preset gets a matching build preset; `windows-msvc` and `package-windows` build/test presets set `configuration: Release` (multi-config generator). Test presets are added for every configure preset whose job runs ctest.

### D3 — asan reconciliation: split wins over merge

CI runs address and undefined as separate legs and R1 hardens them separately; merging the legs to match the combined preset would change CI behavior inside a change whose contract is "no lane changes". So the preset side moves: `asan` becomes address-only, `ubsan` is born. Breaking for local users of `--preset asan`, recorded in the proposal.

### D4 — SDL3 variant cells: base preset + one `-D` overlay

`linux-sdl3` (gcc|clang), `windows-sdl3`, and `macos-sdl3` are their base cells plus `PAL_BACKEND_SDL3=ON`. They migrate to `cmake --preset <base> -DPAL_BACKEND_SDL3=ON` rather than getting four dedicated presets. Rationale: `cmake --preset X -D...` is still preset-sourced configuration with one documented overlay; dedicated presets per (toolchain × variant) cell is the combinatorial explosion presets' `inherits` exists to avoid, and R8's matrix consolidation will revisit cell identity anyway. The PAL workflow's `pal-sdl2`/`pal-sdl3` get real presets because they set PAL-specific vars (`PAL_DEFAULT_BACKEND`) that local PAL work needs.

### D5 — Recorded flag divergences (preset != current YAML)

Migration is flag-identical except these deliberate deltas, each an improvement or a no-op on the runner:

1. `linux-ipc` → `--preset ipc`: drops the explicit gcc-13 pin. ubuntu-latest (24.04) default gcc is 13; runner behavior unchanged, preset stays compiler-neutral for local use.
2. pal-ci `headless-tests` and `abi-c-compile` configure with no `CMAKE_BUILD_TYPE` (empty build type) → `--preset pal-headless` builds Debug. Empty-build-type was an accident, not a choice.
3. pal-ci jobs configure with no generator (Unix Makefiles) → all pal presets are Ninja. Faster, consistent with every other lane; runners install ninja-build.
4. pal-ci `asan-lifecycle` hand-rolls gcc ASan → `--preset asan` (clang-18 + libc++). One sanitizer toolchain repo-wide; the gtest invocation (`--gtest_filter=ContractGate_Lifecycle*` `--gtest_repeat=3`) is untouched.
5. `release-validation` configures coverage flags with the default compiler and CXX-only flags → `--preset coverage` (gcc-13 pin, C+CXX+linker flags). Superset; gcov tooling already assumes gcc-13 (`--gcov-tool gcov-13`).
6. sprint2 `multi-instance-tests` pins only `CMAKE_CXX_COMPILER` → `library-mode` pins both C and CXX via toolchain-gcc13.
7. `windows` job configures with no generator (defaults to VS 17 2022 on windows-latest) and no `-A` → `windows-msvc` makes generator and x64 architecture explicit. Same effective toolchain; module-dag `build-windows` already passes `-A x64`.

### D6 — Jobs that do not migrate (no cmake/ctest configure step)

`abi-check` (header-only gcc syntax check), `sdl-firewall` (grep), `include-rules` (python), `summary` (echo), `globals-registry` (python scripts), `tlaplus` (java), `dependency-scan` (osv-scanner). The fuzz job's fuzzer-binary invocations and the gtest-filter steps in `contract-gates`, `asan-lifecycle`, `multi-instance-tests`, `abi-c-compile` also stay as-is — only their configure/build halves migrate.

### D7 — Full job → preset migration map

| Workflow | Job | Configure | Build | Test |
|---|---|---|---|---|
| ci.yml | `linux` (gcc) | `--preset linux-gcc` | `--build --preset linux-gcc` | `ctest --preset linux-gcc` |
| ci.yml | `linux` (clang) | `--preset linux-clang` | `--build --preset linux-clang` | `ctest --preset linux-clang` |
| ci.yml | `linux-ipc` | `--preset ipc` | `--build --preset ipc` | `ctest --preset ipc` |
| ci.yml | `linux-sdl3` (gcc\|clang) | `--preset linux-gcc\|linux-clang -DPAL_BACKEND_SDL3=ON` | build preset | (build-verify only) |
| ci.yml | `windows` | `--preset windows-msvc` | `--build --preset windows-msvc` (Release config) | `ctest --preset windows-msvc` |
| ci.yml | `windows-sdl3` | `--preset windows-msvc -DPAL_BACKEND_SDL3=ON` | build preset | (build-verify only) |
| ci.yml | `macos` | `--preset release-tests` | `--build --preset release-tests` | `ctest --preset release-tests` |
| ci.yml | `macos-sdl3` | `--preset release-tests -DPAL_BACKEND_SDL3=ON` | build preset | (build-verify only) |
| ci.yml | `sanitizers` (address) | `--preset asan` | `--build --preset asan` | `ctest --preset asan` |
| ci.yml | `sanitizers` (undefined) | `--preset ubsan` | `--build --preset ubsan` | `ctest --preset ubsan` |
| ci.yml | `sanitizers` (thread) | `--preset tsan` | `--build --preset tsan` | `ctest --preset tsan` |
| ci.yml | `sanitizers` (memory) | (cell retired by R1 — no migration) | — | — |
| ci.yml | `static-analysis` | `--preset linux-clang` (compile_commands via D8) | (clang-tidy step unchanged) | — |
| ci.yml | `fuzz` | `--preset fuzz` | `--build --preset fuzz` (targets `fuzz-all generate_fuzz_corpus`) | (fuzzer invocations unchanged) |
| ci.yml | `coverage` | `--preset coverage` | `--build --preset coverage` | `ctest --preset coverage` |
| ci.yml | `packaging` (Linux/macOS) | `--preset package` | `--build --preset package` | — |
| ci.yml | `packaging` (Windows) | `--preset package-windows` | `--build --preset package-windows` | — |
| ci.yml | `release-validation` | `--preset coverage` | `--build --preset coverage` | `ctest --preset coverage` + existing `--label-exclude soak` |
| pal-ci.yml | `headless-tests` | `--preset pal-headless` | `--build --preset pal-headless` | `ctest --preset pal-headless` |
| pal-ci.yml | `sdl2-tests` | `--preset pal-sdl2` | `--build --preset pal-sdl2` | `ctest --preset pal-sdl2` |
| pal-ci.yml | `sdl3-tests` | `--preset pal-sdl3` | `--build --preset pal-sdl3` | `ctest --preset pal-sdl3` |
| pal-ci.yml | `contract-gates` | `--preset pal-headless` | `--build --preset pal-headless` | (gtest filter + nm checks unchanged) |
| pal-ci.yml | `asan-lifecycle` | `--preset asan` | `--build --preset asan` | (gtest filter unchanged) |
| pal-ci.yml | `abi-c-compile` | `--preset pal-headless` | `--build --preset pal-headless` | (abi binary + C11 compile unchanged) |
| pal-ci.yml | `windows-build` | `--preset windows-msvc` | `--build --preset windows-msvc` | `ctest --preset windows-msvc` |
| module-dag.yml | `cmake-dag` | `--preset release` (configure-only DAG check; tests OFF matches) | — | — |
| module-dag.yml | `build-linux` | `--preset linux-gcc` | `--build --preset linux-gcc` | `ctest --preset linux-gcc` |
| module-dag.yml | `build-windows` | `--preset windows-msvc` | `--build --preset windows-msvc` | `ctest --preset windows-msvc` |
| sprint2-checks.yml | `multi-instance-tests` | `--preset library-mode` | `--build --preset library-mode --target legends_unit_tests` | (gtest invocations unchanged) |

Build directories move from `build/` to the presets' `build/${presetName}`; every step that references `build/` paths in a migrated job (artifact globs, `test -f build/...`, fuzzer paths, lcov `--directory`, cpack `cd build`) updates to the preset's binary dir in the same edit.

### D8 — `CMAKE_EXPORT_COMPILE_COMMANDS=ON` moves into the hidden bases

`static-analysis` is the only job needing it; putting it in `default`/`default-ninja` costs nothing, serves local tooling, and lets static-analysis use `linux-clang` with no overlay. (Multi-config VS generator ignores it; harmless on `windows-msvc`.)

### D9 — Test presets gain `noTestsAction: error`

All test presets (existing and new) set `execution.noTestsAction: error` per cmake-presets practice (audit-wiki/wiki/sources/CI Design for C++-CMake Monorepos (2026-06).md, practice 1). A preset that selects zero tests fails instead of passing vacuously — the same hardening direction as `test-estate-truth`'s nonzero-selection rule.

## Risks / Trade-offs

- [Binary-dir move breaks path references] → D7 enumerates every dependent step; per-job verification task checks artifact globs, cache paths (`build/_deps/sdl3-*` → `build/<preset>/_deps/sdl3-*`), and hardcoded `./build/` invocations in the same commit as the job's migration.
- [`asan` split surprises local users who relied on combined address+undefined] → BREAKING flag in proposal; `ubsan` preset documented next to `asan`; running both presets reproduces old coverage.
- [Condition-guarded presets hidden on the "wrong" OS confuse contributors] → guards are the point (M-2); `cmake --list-presets` shows runnable presets per OS, and unguarded `dev`/`release-tests`/`ipc` remain everywhere.
- [R1 lands `tsan` suppressions concurrently with this change's `tsan` edit] → this change only adds the inherit/guard to `tsan`; rebase keeps R1's `TSAN_OPTIONS` value verbatim.
- [Preset typo or flag drift during migration silently changes a lane's config] → per-job task includes a flag-parity check: diff the effective cache (`cmake -N -LA` or `CMakeCache.txt`) of old vs new configure for each migrated job before deleting the old flags.
- [ubuntu-latest image roll changes default gcc, breaking the unpinned `ipc` lane assumption (D5.1)] → acceptable: the lane still builds with the image default, same as today's risk profile for every unpinned apt package; R8's consolidation revisits runner pinning.

## Migration Plan

1. Land `CMakePresets.json` additions/modifications alone; verify `cmake --list-presets` output on Windows and Linux, and that `dev`/`dev-mingw` users see no behavior change.
2. Migrate workflows one file per commit (ci.yml, pal-ci.yml, module-dag.yml, sprint2-checks.yml), per-job flag-parity check each.
3. Rollback: revert the workflow commit(s); presets are additive and stay.

## Open Questions

(none — the asan split, msan exclusion, and overlay-vs-preset boundary were resolved by Recommendation Review rows M-2/A-1/G-6 and D3/D4 above)
