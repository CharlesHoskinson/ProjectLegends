---
type: entity
entity_kind: system
aliases: ["GitHub Actions workflows", "workflow files", ".github/workflows"]
tags: [entity, type/entity, topic/audit, topic/ci]
created: 2026-06-10
updated: 2026-06-10
status: draft
related:
  - "[[Build & CI System (Project Legends)]]"
  - "[[CI Gate Coverage Map]]"
sources:
  - "[[Build & CI Audit (2026-06)]]"
  - "[[CI Run History (2026-06)]]"
---

# CI Workflows (GitHub Actions)

Inventory of the four workflow files in `.github/workflows/` as they stand on the current commit (branch `ci-audit`). Factual current-state only. Gate status (required vs. optional in branch protection) is covered in [[CI Gate Coverage Map]]; observed run behavior in [[CI Run History (2026-06)]]; the build system they drive in [[Build & CI System (Project Legends)]].

## ci.yml — `CI`

File: `.github/workflows/ci.yml` (931 lines).

**Triggers** (`.github/workflows/ci.yml:18-27`): push to branches `main`, `master`, `develop` and tags `v[0-9]*`; pull_request targeting `main`, `master`, `develop`; schedule cron `0 3 * * *` (nightly 03:00 UTC); `workflow_dispatch`. **No path filters** — every push/PR to those branches runs it regardless of which files changed. `permissions: contents: read` is set (`ci.yml:29-30`).

The header comment describes the tier design (REQ-OPS-004): PR/develop = build + unit tests; master = + sanitizers and fuzz smoke; nightly = soak/extended fuzz; tag = packaging (`ci.yml:8-12`).

**Jobs** (16 job IDs; matrix expansion yields up to 23 runner jobs):

| Job ID | Display name | Runner | Timeout | Trigger tier | Allow-failure |
|---|---|---|---|---|---|
| `linux` | Linux (gcc/clang) — 2-way matrix | ubuntu-latest | 15 min | every trigger (`ci.yml:36-42`) | no |
| `linux-ipc` | Linux IPC (gcc) | ubuntu-latest | 15 min | every trigger (`ci.yml:95-98`) | no |
| `linux-sdl3` | Optional Linux SDL3 (gcc/clang) — 2-way matrix | ubuntu-latest | 20 min | nightly / dispatch / tag only (`ci.yml:136`) | no |
| `windows` | Windows (MSVC) | windows-latest | 30 min | every trigger (`ci.yml:189-192`) | no |
| `windows-sdl3` | Optional Windows SDL3 (MSVC) | windows-latest | 30 min | nightly / dispatch / tag only (`ci.yml:229`) | no |
| `macos` | Optional macOS (AppleClang) | macos-15 | 15 min | nightly / dispatch / tag only (`ci.yml:263`) | no |
| `macos-sdl3` | Optional macOS SDL3 (AppleClang) | macos-15 | 20 min | nightly / dispatch / tag only (`ci.yml:301`) | no |
| `sanitizers` | address/undefined/thread/memory — 4-way matrix | ubuntu-latest | 20 min | PR, push-to-master, nightly, dispatch — plain pushes to `main`/`develop` are excluded (`ci.yml:333-337`) | `continue-on-error` for `thread` and `memory` via `matrix.allow_failure` (`ci.yml:332,361,373`) |
| `abi-check` | C ABI Verification | ubuntu-latest | 5 min | every trigger (`ci.yml:406-409`) | no |
| `static-analysis` | Optional Static Analysis (clang-tidy) | ubuntu-latest | 15 min | nightly / dispatch only; `needs: [linux]` (`ci.yml:439-440`) | errors fail, warnings allowed (`ci.yml:468-473`) |
| `fuzz` | Fuzz Testing | ubuntu-latest | 15 min | PR, push-to-master, nightly, dispatch; `needs: [linux]` (`ci.yml:482-487`); 30 s/target smoke on PR + push-to-master (`ci.yml:515-516`), 60 s/target on non-PR events (`ci.yml:540-578`) | no |
| `tlaplus` | Optional TLA+ Model Checking | ubuntu-latest | 15 min | nightly / dispatch only (`ci.yml:587`); 17 sequential TLC steps (`ci.yml:602-702`) | no |
| `coverage` | Code Coverage | ubuntu-latest | 15 min | every trigger (`ci.yml:707-710`) | report-only: "no minimum threshold is enforced by CI yet" (`ci.yml:749`) |
| `dependency-scan` | Optional Dependency Scan | ubuntu-latest | 10 min | nightly / dispatch only (`ci.yml:773`) | scan step has `continue-on-error: true` and `\|\| true` on both scanner invocations (`ci.yml:784-787`) |
| `packaging` | Package — 3-way OS matrix (ubuntu-latest, windows-latest, macos-15) | matrix | 30 min | tag push only; `needs: [linux, windows, macos, linux-sdl3, windows-sdl3, macos-sdl3]` (`ci.yml:804-805`) | no |
| `release-validation` | Release Validation | ubuntu-latest | 30 min | tag push only; `needs: [linux, packaging]`; enforces an 80% line-coverage threshold on `src/app/` (`ci.yml:879-880,916-921`) | no |

**Caching**: only the SDL3 dependency directory is cached. `actions/cache@v4` on `build/_deps/sdl3-*` keyed `sdl3-linux-<compiler>-${{ hashFiles('cmake/dependencies.cmake') }}` (`ci.yml:164-167`), `sdl3-windows-…` (`ci.yml:234-237`), `sdl3-macos-…` (`ci.yml:306-309`), and `sdl3-<os>-packaging-…` (`ci.yml:831-834`). No compiler cache (ccache/sccache) appears anywhere in the file; every job compiles the tree cold.

**Artifacts**: visual-diff PNGs on test failure, retention 14 days, from `linux` (`ci.yml:80-90`), `windows` (`ci.yml:210-220`), `macos` (`ci.yml:282-292`); `coverage-report` (filtered lcov info + policy note, default retention — none specified) (`ci.yml:751-757`) plus a conditional Codecov upload gated on `CODECOV_TOKEN` being non-empty (`ci.yml:759-764`); `dependency-scan` JSON `if: always()` (`ci.yml:789-795`); `package-<OS>` installers + `SHA256SUMS.txt` from `packaging` (`ci.yml:863-872`), downloaded back by `release-validation` (`ci.yml:923-931`).

## pal-ci.yml — `Optional PAL CI`

File: `.github/workflows/pal-ci.yml` (265 lines).

**Triggers** (`pal-ci.yml:3-24`): push and pull_request to `main`, `master`, `develop` **with path filters** — `src/pal/**`, `include/**`, `tests/unit/test_pal_*.cpp`, `cmake/**`, `CMakeLists.txt`, the workflow file itself; schedule cron `0 4 * * *`; `workflow_dispatch`. No `permissions:` block, no `concurrency:` group.

**Jobs** (8). None declares `timeout-minutes` (GitHub default 360 min applies). None is conditioned on event type — all 8 run on every matching trigger (PR + push + nightly + dispatch). No `continue-on-error` anywhere. All display names carry the "Optional" prefix.

| Job ID | Display name | Runner |
|---|---|---|
| `headless-tests` | Optional Headless Backend (`pal-ci.yml:27-51`) | ubuntu-latest |
| `sdl2-tests` | Optional SDL2 Backend (`pal-ci.yml:53-79`) | ubuntu-latest |
| `sdl3-tests` | Optional SDL3 Backend — clones SDL3 `main` at depth 1 and builds it from source every run (`pal-ci.yml:96-101`) | ubuntu-latest |
| `sdl-firewall` | Optional SDL Header Firewall — grep for SDL includes outside `src/pal/` (`pal-ci.yml:121-136`) | ubuntu-latest |
| `contract-gates` | Optional Contract Gates — `ContractGate*` gtest filter + `nm` symbol checks on `liblegends_core.a` (`pal-ci.yml:138-181`) | ubuntu-latest |
| `asan-lifecycle` | Optional ASan Lifecycle Tests — gcc ASan Debug build, `ContractGate_Lifecycle*` repeated 3× (`pal-ci.yml:183-214`) | ubuntu-latest |
| `abi-c-compile` | Optional Pure C ABI Verification — `legends_abi_test` binary + `gcc -std=c11 -fsyntax-only` (`pal-ci.yml:216-245`) | ubuntu-latest |
| `windows-build` | Optional Windows Build — MSVC headless Release + ctest (`pal-ci.yml:247-265`) | windows-latest |

**Caching**: none. The `sdl3-tests` job rebuilds SDL3 from a fresh upstream clone on each run with no cache step (`pal-ci.yml:96-101`), in contrast to ci.yml's cached FetchContent SDL3 (`ci.yml:164-167`).

**Artifacts**: none uploaded. `contract-gates` writes `contract-gates.xml` via `--gtest_output` (`pal-ci.yml:162-163`) but no upload step follows.

## module-dag.yml — `Module DAG`

File: `.github/workflows/module-dag.yml` (216 lines). Header states "STRICT ENFORCEMENT FROM DAY 1: All violations block PRs immediately" (`module-dag.yml:10-12`).

**Triggers** (`module-dag.yml:18-45`): push and pull_request to `main`, `master`, `develop` **with path filters** — `include/**`, `engine/include/**`, `src/**`, `engine/src/**`, `cmake/**`, `CMakeLists.txt`, `engine/CMakeLists.txt`, `scripts/check_includes.py`, the workflow file; schedule cron `30 4 * * *`; `workflow_dispatch`. No `permissions:` block, no `concurrency:` group.

**Jobs** (5). No job declares `timeout-minutes`. No `continue-on-error`.

| Job ID | Display name | Runner | Trigger tier |
|---|---|---|---|
| `include-rules` | Include Rules — `scripts/check_includes.py` + grep for `../src/` in public headers (`module-dag.yml:51-85`) | ubuntu-latest | every trigger |
| `cmake-dag` | CMake DAG — configure-only with `LEGENDS_BUILD_TESTS=OFF`; the verification is that configure succeeds (`module-dag.yml:90-118`) | ubuntu-latest | every trigger |
| `build-linux` | Optional Build (Linux) | ubuntu-latest | nightly / dispatch only; `needs: [include-rules, cmake-dag]` (`module-dag.yml:126-127`) |
| `build-windows` | Optional Build (Windows) | windows-latest | nightly / dispatch only; `needs: [include-rules, cmake-dag]` (`module-dag.yml:159-160`) |
| `summary` | Summary — `if: always()`, fails if either check job failed or either optional build failed-not-skipped (`module-dag.yml:182-216`) | ubuntu-latest | every trigger |

**Caching**: none. **Artifacts**: none.

## sprint2-checks.yml — `Sprint 2 Checks`

File: `.github/workflows/sprint2-checks.yml` (114 lines).

**Triggers** (`sprint2-checks.yml:3-27`): push and pull_request **with no branch filter** — any branch on push — gated only by path filters: `CMakeLists.txt`, `CMakePresets.json`, `docs/architecture/**`, `engine/**`, `src/**`, `include/**`, `scripts/**`, `tests/**`, the workflow file, `.github/baseline_globals.yaml`. No schedule, no `workflow_dispatch`, no `permissions:` block, no `concurrency:` group.

**Jobs** (2). No `timeout-minutes`, no `continue-on-error`, no tier conditions — both run on every matching push/PR.

| Job ID | Display name | Runner | Content |
|---|---|---|---|
| `globals-registry` | Globals Registry Validation | ubuntu-latest | Ten Python steps (nine checks plus the graphify enrichment build): `check_current_context.py`, `check_migration_status.py`, `check_globals.py` (baseline enforcement), `check_gsl_lite_usage.py`, `check_conflict_markers.py`, `check_case_collisions.py`, `check_openspec_staleness.py`, `check_capability_matrix.py`, plus Graphify enrichment build + strict check (`sprint2-checks.yml:44-85`) |
| `multi-instance-tests` | Multi-Instance Smoke Tests | ubuntu-latest | gcc-13 Release headless build with `LEGENDS_LIBRARY_MODE=ON` of target `legends_unit_tests`; runs the filtered `MultiInstance*:Sprint2*:GslContract*:ContractGates*` set, then the **full** unfiltered `legends_unit_tests` suite (`sprint2-checks.yml:98-114`) |

**Caching**: none. **Artifacts**: none.

## Inter-workflow build duplication

Jobs in three workflows compile the same CMake targets that ci.yml already builds:

- **module-dag `build-linux` vs. ci.yml `linux` (gcc leg)**: both configure gcc-13 / Release / `LEGENDS_BUILD_TESTS=ON` / `LEGENDS_HEADLESS=ON`, build the full tree, and run ctest (`module-dag.yml:138-151` vs. `ci.yml:63-77`). module-dag adds only `-DPAL_BACKEND_HEADLESS=ON`. Both fire on nightly/dispatch (module-dag's build jobs are nightly-gated; ci.yml's `linux` runs nightly too).
- **module-dag `build-windows` vs. ci.yml `windows`**: both MSVC Release headless builds with tests + ctest `-C Release` (`module-dag.yml:166-177` vs. `ci.yml:197-207`).
- **sprint2 `multi-instance-tests` vs. ci.yml `linux` (gcc leg)**: both gcc-13 Release headless builds of the test suite; sprint2 differs only in `LEGENDS_LIBRARY_MODE=ON` and the `legends_unit_tests` target subset, then runs the full unit-test binary that ci.yml's ctest run also executes (`sprint2-checks.yml:98-114` vs. `ci.yml:63-77`).
- **pal-ci `headless-tests` vs. ci.yml `linux` (gcc leg)**: g++-13 headless build with tests + ctest (`pal-ci.yml:38-51` vs. `ci.yml:63-77`); pal-ci uses `PAL_BACKEND_HEADLESS=ON` and default build type.
- **pal-ci `windows-build` vs. ci.yml `windows`**: MSVC headless Release build + ctest on windows-latest in both (`pal-ci.yml:253-265` vs. `ci.yml:197-207`).
- **pal-ci `abi-c-compile` vs. ci.yml `abi-check`**: both verify C11 compilation of `legends_embed.h`-consuming code with `gcc -std=c11 -fsyntax-only` (`pal-ci.yml:240-245` vs. `ci.yml:414-419`).
- **pal-ci `asan-lifecycle` vs. ci.yml `sanitizers` (address leg)**: both ASan Debug builds of the test suite (`pal-ci.yml:194-214`, gcc, lifecycle subset ×3 vs. `ci.yml:343-346,383-401`, clang-18, full ctest).
- **pal-ci `sdl3-tests` vs. ci.yml `linux-sdl3`**: both build an SDL3-backed Linux binary; pal-ci compiles SDL3 from an upstream `main` clone uncached (`pal-ci.yml:96-101`), ci.yml uses the cached FetchContent dependency (`ci.yml:164-178`).

## Cross-workflow observations

- **Job inventory**: 31 job definitions across the four files — ci.yml 16, pal-ci.yml 8, module-dag.yml 5, sprint2-checks.yml 2. Matrix expansion (linux ×2, linux-sdl3 ×2, sanitizers ×4, packaging ×3) brings ci.yml to 23 runner jobs, 38 total across all files when every tier fires.
- **Overlap clusters**: (1) Linux gcc headless build+test — built independently by ci.yml `linux`, ci.yml `coverage`, module-dag `build-linux`, sprint2 `multi-instance-tests`, pal-ci `headless-tests` (citations above); (2) Windows MSVC headless build+test — ci.yml `windows`, module-dag `build-windows`, pal-ci `windows-build`; (3) C11 ABI check — ci.yml `abi-check`, pal-ci `abi-c-compile`; (4) ASan build — ci.yml `sanitizers[address]`, pal-ci `asan-lifecycle`; (5) SDL3 build — ci.yml `linux-sdl3`, pal-ci `sdl3-tests`.
- **Concurrent execution on one push**: no workflow declares a `concurrency:` group. A push to `master` touching `include/**` matches ci.yml (no path filter, `ci.yml:18-23`), pal-ci (`pal-ci.yml:8,17`), module-dag (`module-dag.yml:22,34`), and sprint2-checks (`sprint2-checks.yml:11,23`) — all four run simultaneously. `src/**` or `cmake/**` likewise triggers ci.yml, module-dag, and sprint2 together (pal-ci joins on `cmake/**` and `CMakeLists.txt`).
- **Branch scope asymmetry**: ci.yml, pal-ci, and module-dag restrict push triggers to `main`/`master`/`develop`; sprint2-checks runs on pushes to **any** branch (`sprint2-checks.yml:4-14`).
- **Nightly stagger**: three distinct crons — ci.yml 03:00 UTC (`ci.yml:26`), pal-ci 04:00 UTC (`pal-ci.yml:23`), module-dag 04:30 UTC (`module-dag.yml:44`); sprint2-checks has no schedule.
- **Timeout coverage**: every ci.yml job sets `timeout-minutes` (5–30); none of the 15 jobs in the other three files sets any, leaving them at the GitHub default of 360 minutes.
- **Allow-failure surface**: confined to ci.yml — TSan and MSan matrix legs (`ci.yml:332,361,373`, with Sprint 7 exit plans noted at `ci.yml:355-356,366-367`) and the dependency-scan step (`ci.yml:784-787`).

## Related

- [[CI Gate Coverage Map]] — which of these jobs gate merges vs. carry the "Optional" prefix
- [[CI Run History (2026-06)]] — observed pass/fail behavior of these workflows
- [[Build & CI System (Project Legends)]] — the CMake machinery these jobs invoke
