# CI Gate Coverage Map

Maps every module from `cmake/ModuleManifest.cmake` and every non-module path family to the CI jobs that gate it, the tier those jobs run on, and the local checks that guard it — exposing where no mandatory (PR+push) gate fires. Subsystem context: [[Build & CI System (Project Legends)]]; what the test jobs actually execute: [[Project Legends Test Suite]].

## Trigger tiers

- **PR+push** — runs on pull requests and pushes to `main`/`master`/`develop`. `ci.yml` has **no `paths:` filter**, so it fires on every push/PR to those branches regardless of which files changed (`.github/workflows/ci.yml:18-27`). `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` are path-filtered: a change outside their `paths:` lists triggers nothing from them (`.github/workflows/pal-ci.yml:3-24`, `.github/workflows/module-dag.yml:18-45`, `.github/workflows/sprint2-checks.yml:3-27`). `sprint2-checks.yml` has no branch filter — it fires on matching pushes to any branch.
- **nightly** — cron: `ci.yml` 03:00 UTC (`.github/workflows/ci.yml:24-26`), `pal-ci.yml` 04:00 (`.github/workflows/pal-ci.yml:22-23`), `module-dag.yml` 04:30 (`.github/workflows/module-dag.yml:43-44`). `sprint2-checks.yml` has **no** schedule.
- **tag** — pushes of `v*` tags (`.github/workflows/ci.yml:21`).
- **manual** — `workflow_dispatch` on `ci.yml`, `pal-ci.yml`, `module-dag.yml`; not on `sprint2-checks.yml`.

A nuance inside the PR+push tier: the `sanitizers` and `fuzz` jobs run on every PR but, for pushes, **only on `master`** — pushes to `main` or `develop` skip them (`.github/workflows/ci.yml:333-337`, `.github/workflows/ci.yml:482-487`).

## Coverage table

| Target / path family | Workflow jobs that build or test it | Trigger tier | Local hook / check script | Mandatory (PR+push) gate |
|---|---|---|---|---|
| `legends_core` (`include/legends`, `src/legends`) | ci.yml: `linux`, `linux-ipc`, `windows`, `coverage` build+ctest (`ci.yml:36-90, 95-127, 189-220, 707-764`); `abi-check` C11-compiles `legends_embed.h` (`ci.yml:406-430`); `sanitizers`, `fuzz` (`ci.yml:328-401, 478-578`). pal-ci.yml: `contract-gates` runs `ContractGate*` tests and `nm` symbol/`main` firewall on `liblegends_core.a` (`pal-ci.yml:138-181`) — triggered only via `include/**`, not `src/legends/**` (`pal-ci.yml:6-21`). module-dag.yml: `include-rules`, `cmake-dag` via `src/**`+`include/**` (`module-dag.yml:21-42, 51-118`). sprint2-checks.yml: both jobs via `src/**`+`include/**` (`sprint2-checks.yml:5-27, 30-114`) | PR+push; sanitizers/fuzz: PR + push-to-master + nightly (`ci.yml:333-337, 482-487`) | `.githooks/pre-commit` → `scripts/check_includes.py` (opt-in; `.githooks/pre-commit:3-11`) | Yes |
| `legends_pal` (`include/pal`, `src/pal`) | ci.yml: `linux`, `linux-ipc`, `windows`, `coverage` (PAL is built into every build; `CMakeLists.txt:284`). pal-ci.yml: all eight jobs — `headless-tests`, `sdl2-tests`, `sdl3-tests`, `sdl-firewall`, `contract-gates`, `asan-lifecycle`, `abi-c-compile`, `windows-build` (`pal-ci.yml:27-265`), triggered by `src/pal/**`+`include/**` (`pal-ci.yml:6-21`). module-dag.yml + sprint2-checks.yml via `src/**`+`include/**` | PR+push; pal-ci also nightly + manual (`pal-ci.yml:22-24`) | pre-commit `check_includes.py` | Yes |
| `aibox_core` (`engine/include`, `engine/src`) | ci.yml: `linux`, `linux-ipc`, `windows`, `coverage` (engine built in all default builds); `fuzz` targets engine load-state/memory-blob fuzzers (`ci.yml:518-526`); `static-analysis` clang-tidy on `engine/src` is nightly/manual only (`ci.yml:435-473`). module-dag.yml via `engine/include/**`, `engine/src/**`, `engine/CMakeLists.txt` (`module-dag.yml:23-25, 28, 36-40`). sprint2-checks.yml via `engine/**` (`sprint2-checks.yml:9, 21`). pal-ci.yml does **not** cover engine paths (`pal-ci.yml:6-21`) | PR+push; clang-tidy: nightly/manual only (`ci.yml:439`) | pre-commit `check_includes.py` | Yes |
| `legends_ipc` (`include/legends_ipc`, `src/legends_ipc`) | Built unconditionally in every configure (`CMakeLists.txt:332-354`), so all ci.yml build jobs compile it; IPC integration tests require `LEGENDS_USE_IPC=ON` and run only in `linux-ipc` (`ci.yml:95-127`; `CMakeLists.txt:827-835`). module-dag.yml + sprint2-checks.yml via `src/**`+`include/**`; pal-ci.yml via `include/**` only | PR+push | pre-commit `check_includes.py` | Yes (IPC-mode tests: Linux gcc Debug only) |
| `legends_proxy` (`src/legends_proxy`) | Compiled only when `LEGENDS_USE_IPC=ON` (`CMakeLists.txt:405-432`) — `linux-ipc` is the only CI job that sets it (`ci.yml:108-116`). module-dag.yml and sprint2-checks.yml are *triggered* by `src/legends_proxy/**` changes (`src/**`) but configure without IPC, so they never compile the proxy (`module-dag.yml:103-109`; `sprint2-checks.yml:99-105`) | PR+push (single job) | pre-commit `check_includes.py` | Yes — one Linux gcc Debug job; never built on Windows or macOS at any tier |
| `legends_engine_host` (`src/engine_host`) | Compiled only when `LEGENDS_USE_IPC=ON` (`CMakeLists.txt:373-392`); `linux-ipc` builds it, asserts the binary exists, and runs ctest (`ci.yml:108-127`). Same trigger-without-build caveat as `legends_proxy` for module-dag/sprint2 | PR+push (single job) | pre-commit `check_includes.py` | Yes — one Linux gcc Debug job; never built on Windows or macOS at any tier |
| `.github/workflows/**` | No job validates workflow YAML content (no actionlint or schema check in any workflow). Editing `pal-ci.yml`, `module-dag.yml`, or `sprint2-checks.yml` re-runs that workflow via its self-referencing path entry (`pal-ci.yml:12, 21`; `module-dag.yml:30, 42`; `sprint2-checks.yml:14, 26`); editing `ci.yml` re-runs `ci.yml` because it has no path filter (`ci.yml:18-27`). The graphify module graph also excludes workflow YAML (`graphify-out/GRAPH_REPORT.md` covers only code communities) | PR+push (incidental re-execution only) | none | NONE (no content gate — only re-execution of the edited workflow) |
| `scripts/**` | sprint2-checks.yml `globals-registry` executes nine `check_*.py` scripts plus the graphify enrichment pair (`sprint2-checks.yml:44-85`), triggered by `scripts/**` (`sprint2-checks.yml:12, 24`). module-dag.yml `include-rules` runs `scripts/check_includes.py`, triggered by that one file (`module-dag.yml:29, 41, 64-66`). ci.yml runs `scripts/generate_checksums.py` only in tag-tier `packaging` (`ci.yml:861`) | PR+push (execution-as-test); no dedicated unit tests for the scripts | pre-commit runs `check_includes.py` only | Yes (by execution) |
| `cmake/**` | module-dag.yml `cmake-dag` configures and enforces the module DAG via `legends_verify_dag`/`legends_detect_cycles` (`module-dag.yml:90-118`; `cmake/ModuleDAG.cmake:37-179`), triggered by `cmake/**` (`module-dag.yml:26, 39`). pal-ci.yml triggered by `cmake/**` (`pal-ci.yml:10, 19`) — full backend builds. Every ci.yml build job exercises the cmake tree. sprint2-checks.yml is **not** triggered by `cmake/**` (its paths list only `CMakeLists.txt` and `CMakePresets.json`; `sprint2-checks.yml:6-7, 18-19`) | PR+push | none | Yes |
| `docs/**` | Only `docs/architecture/**` appears in any path filter (`sprint2-checks.yml:8, 20`); it triggers `globals-registry`, whose capability-matrix and graphify-enrichment checks read/write `docs/architecture` (`sprint2-checks.yml:65-85`). All other `docs/**` changes trigger only `ci.yml` (no path filter), which contains no docs check — it builds and tests unrelated code | PR+push for `docs/architecture/**`; rest: ci.yml fires but checks nothing in docs | none | NONE outside `docs/architecture/**` |
| `openspec/**` | Appears in no workflow's `paths:`. `ci.yml` fires on any push/PR (no path filter) but has no openspec step. `scripts/check_openspec_staleness.py` runs in sprint2-checks (`sprint2-checks.yml:62-63`), but `openspec/**` changes never trigger that workflow — the check fires only when an unrelated matching path (e.g. `src/**`, `scripts/**`) changes | ci.yml fires; no content gate at any tier triggered *by* openspec changes | none | NONE |
| `audit-wiki/**` | Appears in no workflow's `paths:` (`pal-ci.yml:6-21`; `module-dag.yml:21-42`; `sprint2-checks.yml:5-27`); no job reads it. Only `ci.yml` fires — no path filter (`ci.yml:18-27`) — for a full build/test of unrelated code | ci.yml fires; nothing examines the wiki | none | NONE |

## Structurally unguarded

**Path families with no mandatory content gate (NONE rows above):**

- `.github/workflows/**` — workflow YAML is never linted or validated; the only effect of editing one is re-running it (`ci.yml:18-27`; self-paths at `pal-ci.yml:12, 21`, `module-dag.yml:30, 42`, `sprint2-checks.yml:14, 26`).
- `docs/**` outside `docs/architecture/**` — triggers only the unfiltered `ci.yml`, which performs no docs check (`sprint2-checks.yml:8, 20` is the sole docs path entry anywhere).
- `openspec/**` — `check_openspec_staleness.py` exists (`sprint2-checks.yml:62-63`) but is orphaned from openspec changes: nothing in `sprint2-checks.yml:3-27` matches `openspec/**`.
- `audit-wiki/**` — no path filter anywhere matches it.

**Gates that exist only on the nightly/manual tier:**

- `static-analysis` (Optional Static Analysis, clang-tidy on `engine/src` + `src/legends`) — `.github/workflows/ci.yml:435-439`.
- `tlaplus` (Optional TLA+ Model Checking, 17 TLC model runs) — `.github/workflows/ci.yml:583-702`, gated at `ci.yml:587`.
- `dependency-scan` (Optional Dependency Scan, osv-scanner) — `.github/workflows/ci.yml:769-773`; additionally advisory even when it runs (`|| true` and `continue-on-error`, `ci.yml:784-787`).
- `linux-sdl3`, `windows-sdl3`, `macos`, `macos-sdl3` — schedule/dispatch/tag only (`ci.yml:136, 229, 263, 301`). Consequence: no macOS build and no SDL3 build of any module runs on the PR tier.
- `build-linux`, `build-windows` in Module DAG — schedule/dispatch only (`.github/workflows/module-dag.yml:127, 160`); on PRs the Module DAG workflow checks includes and configure-time DAG but compiles nothing.

**Tag-tier only:**

- `packaging` (`ci.yml:800-804`) and `release-validation` — the 80% line-coverage threshold on `src/app` is enforced **only** on `v*` tag pushes (`ci.yml:877-921`). The PR-tier `coverage` job is explicitly report-only with no threshold (`ci.yml:749`).

**Partial or advisory inside the mandatory tier:**

- `sanitizers` and `fuzz` skip pushes to `main` and `develop` — their `if:` accepts PRs, pushes to `refs/heads/master`, schedule, and dispatch only (`ci.yml:333-337, 482-487`).
- Thread and memory sanitizers carry `allow_failure: true`, so they are advisory even when they run (`ci.yml:332, 357-373`).
- All eight `pal-ci.yml` jobs and several `ci.yml`/`module-dag.yml` jobs are titled "Optional", independent of trigger tier — the pal-ci jobs do run on the PR+push tier when their paths match (`pal-ci.yml:3-24`).

**Local hook:**

- `.githooks/pre-commit` runs only `scripts/check_includes.py`, and only for developers who have run `git config core.hooksPath .githooks` (`.githooks/pre-commit:3, 7`). No other check script has a local guard.

**Platform gap in the IPC stack:**

- `linux-ipc` is the sole job at any tier that sets `LEGENDS_USE_IPC=ON` (`ci.yml:95-127`); `legends_proxy` and `legends_engine_host` are therefore never compiled on Windows or macOS in CI (`CMakeLists.txt:373, 405`).
