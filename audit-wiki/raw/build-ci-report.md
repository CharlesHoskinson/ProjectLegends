# Build System & CI Audit — Project Legends

**Auditor role:** Build system & CI
**Date:** 2026-06-09 (HEAD = `ef11f20`, branch `master`)
**Prior audit:** `C:\projectLegends\AUDIT.md` (2026-02-24); scope items L5, L6, L7 re-verified below.

---

## 1. Executive summary

The build/CI infrastructure has impressive *breadth* — a 4-sanitizer matrix, libFuzzer jobs, 17 TLA+ model-checking steps, coverage with an 80% release gate, configure-time module-DAG verification, CPack packaging for three platforms, and centralized dependency pins. But as of commit `6900e7a` ("Stabilize CI and RuntimeHost adoption", 2026-06-08), almost all of that enforcement was demoted to nightly/manual-only ("Optional") to get a red pipeline green, which silently regresses prior-audit fixes H7 (fuzz in CI), H8 (TLA+ in CI), and M12 (sanitizer matrix) for every PR and merge. The flagship GPL-2.0 process-isolation guarantee has **zero automated enforcement**: `cmake/VerifyGPLIsolation.cmake` is never included by any CMakeLists, and the module-DAG verifier skips the three license-critical targets. The release pipeline (tag-triggered packaging, NSIS/DMG, checksums, 80% coverage gate) has **never executed once** — the repository has no git tags. Committed build logs at the repo root show the developer's own Windows clang dev preset failing to compile and link a day before this audit, on a toolchain no CI job covers.

Prior findings: **L6 resolved, L7 resolved, L5 partially resolved (Windows SDL2 path still broken).**

---

## 2. Prior-audit finding verification

### L5 — `project_legends` executable target unbuildable → **PARTIALLY RESOLVED (confirmed-open, narrowed)**

- `src/main.cpp` **now exists** (it did not at the prior audit).
- The SDL3 variant of `project_legends` builds in CI (`ci.yml` `linux-sdl3`/`windows-sdl3`/`macos-sdl3` jobs, tag/nightly only) and the SDL2 variant builds on Linux in `pal-ci.yml` `sdl2-tests` (system `libsdl2-dev` + `find_package(SDL2 REQUIRED)`, `CMakeLists.txt:260`).
- **Still broken on Windows**: the SDL2 target hardcodes `target_link_libraries(project_legends PRIVATE mingw32 SDL2main SDL2)` (`CMakeLists.txt:1189`) and references `external/SDL2/include` / `external/SDL2/lib` (`CMakeLists.txt:1162,1167`) — `external/` contains only `glad` and `stb`; there is no `external/SDL2/` directory. An MSVC or vcpkg SDL2 build on Windows cannot link (`mingw32` does not exist there), and the MinGW path needs a bundled SDL2 that is not in the tree.

### L6 — `check_gsl_lite_usage.py` false positives from `_deps` trees → **RESOLVED**

`scripts/check_gsl_lite_usage.py:207` now reads:
```python
exclude_dirs = ['build', 'build_test', 'cmake-build', 'third_party', 'vendor', 'external', '_deps']
```
`build_test` and `_deps` were added in commit `1bdf92b` (2026-02-24, same day as the prior audit). Residual nit: matching is by exact path component, so a CLion-style `cmake-build-debug` directory would still be scanned — but the presets standardize on `build/<preset>`, which is excluded.

### L7 — undeclared `pyyaml` dev dependency → **RESOLVED**

`requirements-dev.txt` exists at the root (added in `1bdf92b`) and contains `pyyaml>=6.0`. That is the only third-party import across `scripts/*.py` (verified: `yaml` is imported only by `check_globals.py:21` and `check_migration_status.py:18`, both with a friendly error message on ImportError). Minor drift: CI still installs it ad hoc (`sprint2-checks.yml:42` `pip install pyyaml`) rather than `pip install -r requirements-dev.txt`, so the file can rot without CI noticing.

---

## 3. New findings

### CI-01 (HIGH) — Quality gates demoted to nightly/manual; ci.yml no longer matches its own documented tiering (regression of H7/H8/M12)

Commit `6900e7a` (2026-06-08) added `if: github.event_name == 'schedule' || github.event_name == 'workflow_dispatch'` to the sanitizers (`ci.yml:333`), static-analysis (`:431`), fuzz (`:474`), TLA+ (`:554`), and dependency-scan (`:740`) jobs, and gated macOS (`:263`), Linux/Windows/macOS SDL3 (`:136`, `:229`, `:301`) to nightly/dispatch/tags. Per-PR and per-merge enforcement is now only: Linux gcc/clang headless Release, Linux IPC Debug, Windows MSVC headless, the abi-check, and report-only coverage.

Consequences:

1. **Dead code**: the fuzz job's "PR: Quick fuzz (30s per target)" step (`ci.yml:503-513`, `if: github.event_name == 'pull_request'`) can never run — the job-level `if` at line 474 excludes `pull_request` events entirely.
2. **Docs contradict reality**: `ci.yml:8-12` claims "merge-to-main: + sanitizers … PR / push to develop: build + unit tests"; `RELEASING.md:7` claims "merge-to-main triggers sanitizer builds"; `RELEASING.md:38` requires "All CI checks must pass (sanitizers, fuzz, TLA+)" before tagging. None of these happen on push or PR anymore.
3. **Prior-audit regression**: AUDIT.md recorded H7 ("No fuzzing in CI") and H8 ("No TLA+ verification in CI") and M12 ("No MSan/TSan jobs") as *fixed*. They are now effectively re-opened for the code paths that matter (PRs and merges).
4. **Soak claims are vapor**: `ci.yml:11` promises "nightly (cron): soak tests"; no workflow sets `LEGENDS_SOAK_ENABLED` (grep of `.github/workflows/` finds no SOAK reference), `cmake/SoakTestLabels.cmake` referenced by `CMakeLists.txt:1020-1024` does not exist, so the `test-soak` target (`CMakeLists.txt:1033-1037`) matches zero tests.

Also note TSan and MSan remain `allow_failure: true` (`ci.yml:351-365`) with honest comments about known engine data races (`g_active_instance`, `CrashBreadcrumb::add()`) and an uninstrumented libc++ — TSan signal has been muted since 2026-03-02 (`12b1f35`, `e87d3b7`) with no exit plan.

**Recommendation:** restore sanitizers + 60s fuzz + TLA+ on push to main/master (the original tiering), fix the dead PR-fuzz step by allowing `pull_request` in the job-level `if` and keeping the 30s step gate, add a dated exit plan for TSan/MSan allow-failure, and either implement the nightly soak job or delete the claim.

### CI-02 (HIGH) — GPL isolation has no automated enforcement: VerifyGPLIsolation.cmake is never included, and the module DAG skips all license-critical targets

The GPL-2.0 process-isolation architecture rests on `legends_ipc` and `legends_proxy` never linking GPL code. Current enforcement:

- `cmake/VerifyGPLIsolation.cmake` (linker-map scan via `scripts/verify_gpl_isolation.py`) says "Usage: include(VerifyGPLIsolation) after defining the project_legends target" (`VerifyGPLIsolation.cmake:8`) — but **no CMakeLists in the repository includes it** (grep hits only the module itself, docs, and openspec). `openspec/changes/phase-iso-process-isolation/tasks.md:54` confirms: "`[ ] 8.3 Linker verification: verify_gpl_isolation.py + CMake integration`" — unchecked. The Python script and its tests (`tests/scripts/test_verify_gpl_isolation.py`) exist but are orphaned.
- Even if included, it would do nothing in CI: the only IPC CI job (`ci.yml` `linux-ipc`, lines 95-127) builds headless without `PAL_BACKEND_SDL2/3`, so `project_legends` (the target the module instruments) does not exist.
- `legends_verify_all_dags()` (`cmake/ModuleDAG.cmake:191-213`) verifies only `legends_core`, `legends_pal`, `aibox_core`; `legends_detect_cycles()` hardcodes the same three (`ModuleDAG.cmake:124`). The manifest *defines* DAG entries for `legends_ipc`, `legends_proxy`, `legends_engine_host` (`cmake/ModuleManifest.cmake:66-68`), but nothing ever checks them. If someone adds `legends_core` to `legends_proxy`'s link line tomorrow, configure succeeds.
- The actual "enforcement" today is comments: "IMPORTANT: legends_ipc must NOT link any GPL-licensed targets. This is verified by REQ-ISO-003 and REQ-ISO-016" (`CMakeLists.txt:361-362`) and the same for proxy (`:422-423`). REQ-ISO-016 is not verified by anything.

**Recommendation (S/M):** (a) extend `legends_verify_all_dags()` to iterate every `LEGENDS_DAG_*` manifest entry; (b) wire `include(cmake/VerifyGPLIsolation.cmake)` guarded on target existence; (c) add a CI step in `linux-ipc` that runs `nm`/`verify_gpl_isolation.py` over `liblegends_proxy.a` + `liblegends_ipc.a` asserting no `aibox_*`/`legends_core` symbols (pal-ci.yml already does exactly this pattern for SDL symbols in `legends_core`, lines 165-172 — copy it).

### CI-03 (HIGH) — Release/packaging pipeline has never executed: zero git tags, untested CPack/NSIS, an 80% coverage gate that has never been measured

`git tag -l` returns **nothing**. Everything release-related is tag-gated:

- `packaging` job (`ci.yml:767-771`, `if: startsWith(github.ref, 'refs/tags/v')`) — never run; `cpack` NSIS/DragNDrop/TGZ generators (`cmake/packaging.cmake:17-23`) and `scripts/generate_checksums.py` have never been exercised in CI.
- `release-validation` (`ci.yml:844-888`) enforces `src/app/` line coverage ≥ 80% via `lcov`/`bc` — this gate has never been evaluated; first tag push will discover both whether the gate passes and whether the bash/grep plumbing works.
- `cmake/version.cmake:24` (`git describe --match "v[0-9]*"`) can never match a tag, so every build ships `LEGENDS_VERSION_STRING = "1.0.0+<hash>"` fallback (`version.cmake:46`) — and `CPACK_PACKAGE_VERSION` would contain a `+` that NSIS version fields handle poorly.
- `RELEASING.md` documents a branch/tag workflow (release/X.Y branches, rc tags) that has never been performed; it also asserts CI behavior that no longer exists (see CI-01).

**Recommendation (M):** do a release dry-run now, before v1.0 pressure: push a `v0.9.0-rc.1` tag from a throwaway branch, let packaging + release-validation run, and fix the fallout (expect: coverage below 80%, cpack surprises, version-string formatting). Make `release-validation` runnable via `workflow_dispatch` so it can be rehearsed without tags.

### CI-04 (MEDIUM) — PRs targeting `develop` bypass the primary CI

`ci.yml:22-23` restricts `pull_request` to `branches: [main, master]`, and `pal-ci.yml:13-14` likewise. But `RELEASING.md:5-10` defines the branch model as `feature/* → PR into develop`. A feature PR into develop therefore gets **no main build+test pipeline** — only `sprint2-checks.yml` (path-filtered, no branch filter) and `module-dag.yml` (includes develop, but its build jobs are schedule-gated, `module-dag.yml:127,160`). Breakage is discovered only after merge, on the `push: develop` trigger — too late to block.

**Recommendation (S):** add `develop` to `pull_request.branches` in `ci.yml` and `pal-ci.yml`, or drop the branch filter entirely.

### CI-05 (MEDIUM) — Dependency vulnerability scanning is a no-op while roadmap claims REQ-SEC-028 "Done"

`ci.yml:744-754`: the job downloads `osv-scanner` from `releases/latest` (unpinned), then runs `./osv-scanner --lockfile cmake/dependencies.cmake || true`. osv-scanner does not understand a CMake file as a lockfile — this invocation fails and is swallowed by `|| true`, the whole step has `continue-on-error: true`, and the job only runs nightly anyway (`:740`). Meanwhile `roadmap.md:1470` lists "dependency scanning (REQ-SEC-028)" under **Fully implemented** and `roadmap.md:3279` marks it **Done**. This is compliance theater: a green checkbox backed by a command that can never produce a finding.

**Recommendation (S):** scan what can actually be scanned — generate a CycloneDX/SPDX SBOM from the pinned tags (gsl-lite v1.0.0, SDL3 release-3.2.8, googletest v1.14.0, benchmark v1.8.3 in `cmake/dependencies.cmake:19-26`, plus the vendored DOSBox-X fork version) and feed that to osv-scanner; pin the scanner version; remove `|| true` (keep `continue-on-error` if triage capacity is the concern); correct the roadmap status to partial.

### CI-06 (MEDIUM) — No compiler caching, heavy job duplication: the 1M-line engine is rebuilt from scratch up to ~12 times per push, against 15-minute timeouts

No workflow uses ccache/sccache; the only `actions/cache` entries cover `build/_deps/sdl3-*` (SDL3 sources). Every one of these jobs compiles the full vendored engine cold: `ci.yml` linux×2, linux-ipc, windows, coverage (+ macOS, sanitizers×4, fuzz on nightly), `sprint2-checks.yml` multi-instance, `pal-ci.yml` headless/sdl2/sdl3/contract-gates/asan-lifecycle/abi-c-compile/windows-build (7 jobs, no schedule gating), `module-dag.yml` builds. `CIFix.md` ("CI is duplicated across CI, PAL CI, Module DAG, and Sprint 2 Checks, causing the same root cause to appear as several failures") already diagnoses this. The `linux` job's `timeout-minutes: 15` (`ci.yml:39`) leaves little headroom for a cold 1,177-file engine build plus ~170 tests.

**Recommendation (M):** add ccache with `actions/cache` keyed on compiler+flags (typical 5-10× rebuild speedup), consolidate pal-ci's seven always-on jobs into the main matrix or path-gate them, and reserve `sprint2-checks` for its Python lint steps (its `multi-instance-tests` job duplicates the full unit suite the `linux` job already runs).

### BUILD-01 (MEDIUM) — Dependency pinning is tag-based (mutable), duplicated, and violated outright by pal-ci building SDL3 from `main`

- All FetchContent pins are mutable git *tags*, not commit SHAs, with no `URL_HASH`/integrity verification (`cmake/dependencies.cmake:19-26,40-45,64-72`). A moved tag or compromised upstream changes the build silently. DEPENDENCIES.md sells this as "reproducible"/"hermetic" (lines 16-17), which overstates it.
- The GoogleTest pin is duplicated: root uses `${LEGENDS_DEP_GOOGLETEST_TAG}` (= v1.14.0), but `engine/CMakeLists.txt:327-330` hardcodes `GIT_TAG v1.14.0`. Bumping one side desynchronizes the two FetchContent declarations for the *same* dependency name.
- **Direct policy violation:** `pal-ci.yml:98` builds SDL3 with `git clone --depth 1 https://github.com/libsdl-org/SDL.git -b main` — upstream HEAD, unpinned, on every push touching `src/pal/**`. This both defeats the pin (`release-3.2.8`) and is a CI flakiness generator (recent commits "Stabilize optional SDL backend CI" `8fdd4c6`, "Relax SDL backend startup event tests" `911692f` are consistent with chasing a moving SDL).
- GitHub Actions are tag-pinned (`actions/checkout@v4`, `actions/setup-python@v5`, `codecov/codecov-action@v4`, etc.), not SHA-pinned; the osv-scanner binary comes from `releases/latest` (`ci.yml:746`).

**Recommendation (S/M):** convert `LEGENDS_DEP_*_TAG` values to commit SHAs (keep the human-readable tag in a comment and DEPENDENCIES.md), make engine/CMakeLists.txt consume the root pin variable, change pal-ci to `-b release-3.2.8` (or reuse the FetchContent path with the cache), and SHA-pin third-party actions.

### BUILD-02 (MEDIUM) — Committed build logs document a broken local dev build on a toolchain no CI covers; logs are repo-hygiene debt

`build_log.txt` (98KB, UTF-16) and `build_output.txt` (27KB, UTF-16) were committed at the repo root in `1dd76b4` (2026-06-08). They record the **dev preset failing**:

- Compile failures: `src/app/cli_parser.cpp:102` / `:133` and `src/app/ai_config.cpp:24` — "use of undeclared identifier 'gsl'" under `clang++` (LLVM for Windows, MSVC-compatible driver, Ninja, `build/dev`).
- Link failure of `legends_unit_tests.exe`: undefined `legends_ipc::FramebufferShm::create`, `legends::CrashReporter::enable`, `legends::overlay::{fillRect,darkenRect,drawString}` (cascade from the compile failures).

A partial CMake fix followed (`a5e70ca`, "Fix optional PAL app GSL linkage", touching only entry-point target wiring), but no commit after `1dd76b4` touched the failing sources, and **no CI job builds this configuration** — Windows CI is MSVC-only (`ci.yml:189-220`, `pal-ci.yml:247-265`); the presets' default generator is even "MinGW Makefiles" (`CMakePresets.json:12`), a third Windows toolchain nothing tests. The presets hardcode `clang-18`/`gcc-13` Linux compiler names (`CMakePresets.json:63-64,111-112`) so most presets are unusable on the Windows machine they ship defaults for, and CI does not use `--preset` at all — two parallel build-config sources that drift independently.

**Recommendation (S):** delete both logs (git rm + .gitignore `build_log.txt`/`build_output.txt`); add one CI job (or a local pre-push script) that exercises `cmake --preset dev` on windows-latest with LLVM clang, or change the presets to match what CI actually tests; verify HEAD actually builds on the dev preset.

### BUILD-03 (MEDIUM) — Root build force-overrides engine options: every consumer always builds 82 engine test files and fetches GoogleTest, even with tests off

`CMakeLists.txt:165-167`:
```cmake
set(AIBOX_BUILD_TESTS ON CACHE BOOL "Build engine tests alongside legends tests" FORCE)
set(AIBOX_HEADLESS ON CACHE BOOL "Build engine in headless mode" FORCE)
set(AIBOX_LIBRARY_MODE ON CACHE BOOL "Build engine as library" FORCE)
```
These are unconditional `FORCE` cache writes, independent of `LEGENDS_BUILD_TESTS`. Effects: (a) configs with `LEGENDS_BUILD_TESTS=OFF` — the `module-dag.yml` cmake-dag job (`module-dag.yml:107`) and the tag `packaging` job (`ci.yml:803-814`) — still fetch GoogleTest (`engine/CMakeLists.txt:323-339`) and compile the ~33k-line engine test suite; (b) an embedder consuming the project via `add_subdirectory` (the stated product shape: "embeddable framework") cannot turn engine tests off at all; (c) `AIBOX_HEADLESS` forced ON means engine SDL paths are dead code in every configuration, fine today but it makes the option set misleading.

**Recommendation (S):** `set(AIBOX_BUILD_TESTS ${LEGENDS_BUILD_TESTS} CACHE BOOL ... FORCE)` (or pass via `add_subdirectory`-scoped variables), and only FORCE what genuinely must be invariant.

### BUILD-04 (LOW) — Hardening flags are configuration-blind: `_FORTIFY_SOURCE=2` injected into `-O0` Debug builds

`legends_compile_options` applies `-fstack-protector-strong -D_FORTIFY_SOURCE=2` unconditionally (`CMakeLists.txt:89-91`) alongside `$<$<CONFIG:Debug>:-g -O0>` (`:85`). `_FORTIFY_SOURCE` is inert without optimization, and on glibc it triggers `features.h`'s `#warning _FORTIFY_SOURCE requires compiling with optimization (-O)` — which Tier A's `-Werror` (`:121`) escalates to a hard error on GCC/Clang Debug Linux builds (the `linux-ipc` job and all sanitizer presets are Debug). On Ubuntu 24.04's default-fortify GCC, an explicit `=2` can additionally collide with the distro default of `=3` (macro redefinition warnings). The committed Windows build log confirms the flag is being passed to a CRT where it does nothing (`build_log.txt` compile lines). Whether this currently breaks the Linux Debug jobs depends on the runner's glibc; either way the flag should be conditional.

**Recommendation (S):** wrap the define in `$<$<NOT:$<CONFIG:Debug>>:-D_FORTIFY_SOURCE=2>` and restrict it to non-Windows GNU-CRT platforms.

### BUILD-05 (LOW) — Warning policy quietly weaker than documented

- The "Tier A — tests should be strict too" comment (`CMakeLists.txt:776`) is contradicted three blocks later: `legends_unit_tests` gets `-Wno-error` on GCC/Clang (`:811-813`) and `legends_integration_tests` likewise (`:1006-1008`); MSVC test targets get `/wd4834`. The committed `build_output.txt` shows engine tests emitting a stream of `-Wunused-result` (`[[nodiscard]]` ignored) warnings — permanently non-fatal.
- The abi-check job's header-guard step (`ci.yml:414-422`) only `echo`es WARNING lines; it can never fail.
- The clang-tidy job (`ci.yml:452-465`) fails only on `error:` lines — `modernize-*,bugprone-*,performance-*` findings are unbounded and untracked (no baseline count, no diff-vs-main).
- `cmake_minimum_required(VERSION 3.20)` (`CMakeLists.txt:11`) vs `CMakePresets.json` schema version 6 requiring CMake ≥ 3.25 — cosmetic inconsistency.

**Recommendation (S/M):** burn down the test-target nodiscard debt and remove `-Wno-error` (the warnings are exactly the kind that hide real bugs in tests), make the header-guard check exit 1, and pin a clang-tidy warning-count baseline so the number can only go down.

---

## 4. CI platform/config coverage matrix (what is NOT tested)

| Dimension | Covered per-PR/push | Nightly/tag only | Never |
|---|---|---|---|
| Linux gcc/clang headless Release | yes (`ci.yml` linux) | | |
| Linux IPC mode | gcc Debug only | | clang IPC; Release IPC |
| Windows MSVC headless | yes | | |
| Windows IPC mode (`shared_memory_win`, `control_channel_win`, `engine_spawner_win` as host/proxy executables) | | | **never** — `LEGENDS_USE_IPC=ON` is built only on Linux (`ci.yml:95-127`); the lib's Windows .cpps compile in normal builds, but `legends_engine_host`/`legends_proxy` are never built or tested on Windows |
| Windows clang/Ninja (the committed dev preset) | | | **never** (see BUILD-02) |
| Windows MinGW (presets' default generator) | | | **never** |
| macOS | | nightly/tag | |
| SDL2 executable | Linux only (pal-ci) | | Windows SDL2 (broken, L5) |
| SDL3 executable | | nightly/tag (+pal-ci builds SDL@main) | |
| Sanitizers ASan/UBSan | | nightly | on PRs/merges |
| TSan/MSan | | nightly, allow-failure | meaningfully (muted since March) |
| Fuzzing | | nightly | on PRs (dead step) |
| TLA+ | | nightly | on PRs/merges |
| ARM64 (incl. macos runner is ARM but Linux/Windows ARM) | | macos-15 is arm64 nightly | Linux/Windows ARM |
| 32-bit, big-endian | | | never (relevant for a portable save-state wire format) |
| cpack/NSIS/DMG, checksums, release validation | | tag only | effectively never (no tags exist) |
| CMake presets as CI entry point | | | never (CI hand-rolls flags) |

---

## 5. Sprint-theme recommendations

1. **Re-arm the gates (S/M):** revert the `6900e7a` demotions for sanitizers/fuzz/TLA+ on push-to-master, fix the unreachable PR-fuzz step, add `develop` to `pull_request` branches, set a dated exit plan for TSan/MSan allow-failure, delete or implement the soak claim. Success = ci.yml's own header comment is true again.
2. **Make GPL isolation mechanically enforced (S/M):** DAG-verify all six manifest modules, wire `VerifyGPLIsolation.cmake`, add an `nm`-based GPL-symbol firewall for `liblegends_proxy.a`/`liblegends_ipc.a` to the linux-ipc job, and add a Windows IPC build job. This is the project's central legal/architectural promise; today it rests on comments.
3. **Release dry-run (M):** push a rc tag, run packaging + release-validation end-to-end, fix cpack/version-string/coverage-gate fallout; make release-validation dispatchable. Do this months before a real v1.0, not during it.
4. **Supply-chain and speed hygiene (M):** SHA-pin FetchContent and Actions, de-duplicate the GoogleTest pin, stop building SDL3 from `main` in pal-ci, replace the osv-scanner no-op with an SBOM-based scan, add ccache, consolidate the four overlapping workflows, remove committed build logs, and un-FORCE `AIBOX_BUILD_TESTS`.

---

## 6. Health grade: **C**

Rationale: the *machinery* is unusually complete for a project at this stage (sanitizer matrix, fuzzing, TLA+, DAG checks, packaging, coverage gates all exist), and the team demonstrably iterates on CI. But trust in a green check is currently low: the strongest gates were switched off repo-wide one day before this audit, the GPL-isolation guarantee is unenforced, the release path has never run, scanning is a no-op marked "Done", and the maintainer's own daily build configuration is broken in committed logs with no CI coverage. Breadth A, enforcement D — net C.
