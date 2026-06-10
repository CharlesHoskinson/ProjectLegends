---
type: synthesis
aliases: ["Modularity Gap Analysis", "Workflow Factoring Gap Analysis"]
tags: [synthesis, type/synthesis, topic/audit, topic/ci, topic/gap-analysis]
created: 2026-06-10
updated: 2026-06-10
status: draft
question: Where does the factoring of the four CI workflows diverge from external practice — duplication, reusable-workflow opportunities, module-DAG alignment, path-filter precision?
sources:
  - "[[CI Design for C++-CMake Monorepos (2026-06)]]"
  - "[[Compiler Caching on GitHub Actions (2026-06)]]"
  - "[[Merge Queues & Required Checks (2026-06)]]"
  - "[[Local Preflight Design (2026-06)]]"
  - "[[Test Impact Analysis & Selection (2026-06)]]"
  - "[[Vendored & License-Isolated Dependency CI (2026-06)]]"
  - "[[CI Run History (2026-06)]]"
entities:
  - "[[CI Workflows (GitHub Actions)]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[Quality Gate Scripts & Hooks]]"
  - "[[Local Dev Loop]]"
maps:
  - "[[CI Gate Coverage Map]]"
confidence: moderate
---

# Gap Analysis — Modularity (2026-06)

How the four workflow files in `.github/workflows/` are factored, against external practice for C++/CMake monorepo CI. Scope: workflow factoring and overlap, reusable-workflow opportunities, module-DAG alignment of CI jobs, path-filter precision, and duplication across `ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`. Sibling gap analyses cover other dimensions; gate-tier semantics live in [[CI Gate Coverage Map]].

## Findings

### 1. The build-test skeleton is hand-copied across all four workflows; no reusable workflow exists

**Current.** [[CI Workflows (GitHub Actions)]] inventories 31 job definitions across the four files, and its "Inter-workflow build duplication" section documents five overlap clusters: the Linux gcc headless build+test is independently written in `ci.yml` `linux`, `ci.yml` `coverage`, `module-dag.yml` `build-linux`, `sprint2-checks.yml` `multi-instance-tests`, and `pal-ci.yml` `headless-tests`; the Windows MSVC headless build+test in `ci.yml` `windows`, `module-dag.yml` `build-windows`, and `pal-ci.yml` `windows-build`; the C11 ABI check in `ci.yml` `abi-check` and `pal-ci.yml` `abi-c-compile`; the ASan build in `ci.yml` `sanitizers[address]` and `pal-ci.yml` `asan-lifecycle`; the SDL3 build in `ci.yml` `linux-sdl3` and `pal-ci.yml` `sdl3-tests` (the latter rebuilding SDL3 from an uncached upstream `main` clone, `.github/workflows/pal-ci.yml:96-101`, where ci.yml caches a pinned FetchContent dependency, `.github/workflows/ci.yml:164-167`). No `workflow_call` appears anywhere in `.github/workflows/`.

**Practice.** [[CI Design for C++-CMake Monorepos (2026-06)]] practice 2: factor duplicated jobs into `on: workflow_call` reusable workflows called via `uses: ./.github/workflows/<file>.yml`, with typed inputs and a `strategy: matrix` in the thin caller — one `build-and-test.yml` taking `{os, preset, ctest-args}` "would replace most of `ci.yml`'s and `pal-ci.yml`'s body and end the drift between them." Practice 7: express the OS×configuration space as a declared matrix so missing cells are visible.

**Gap.** Each duplicate is a near-copy with small undocumented deltas (`PAL_BACKEND_HEADLESS=ON`, `LEGENDS_LIBRARY_MODE=ON`, gcc vs clang ASan, pinned vs upstream SDL3), so divergence is structural: a fix to one configure block does not propagate, and the deltas that matter are invisible among the boilerplate.

**Candidate recommendation.** Create `.github/workflows/build-and-test.yml` with `on: workflow_call` and inputs `{runner, preset, extra-cmake-args, ctest-args}`; rewrite the build jobs of `ci.yml`, `pal-ci.yml` (`headless-tests`, `sdl2-tests`, `sdl3-tests`, `windows-build`), `module-dag.yml` (`build-linux`, `build-windows`), and `sprint2-checks.yml` (`multi-instance-tests`) as matrix calls to it; delete `pal-ci.yml` `abi-c-compile` in favor of the existing `ci.yml` `abi-check`.

### 2. CI configures with raw flag lists; the checked-in presets are a parallel, unused configuration source

**Current.** [[Build & CI System (Project Legends)]]: "**No GitHub workflow invokes any preset**" — all four workflows configure with explicit `cmake -B build` flag lists, and ci.yml jobs *replicate* preset configurations by hand (`linux-ipc` mirrors the `ipc` preset plus a gcc pin, `.github/workflows/ci.yml:110-116`; `sanitizers` mirrors `asan`/`tsan` and adds `undefined`/`memory` configs that have no preset, `ci.yml:340-374`; `fuzz` mirrors `fuzz`, `ci.yml:499-505`; `coverage` mirrors `coverage`, `ci.yml:724-730`). [[Local Dev Loop]] confirms the same from the developer side: `CMakePresets.json` defines the lanes, CI passes raw `-D` flags (`.github/workflows/sprint2-checks.yml:99-105`, `.github/workflows/module-dag.yml:104-109`, `.github/workflows/pal-ci.yml:39-45`).

**Practice.** [[CI Design for C++-CMake Monorepos (2026-06)]] practice 1: presets exist precisely "to support CI builds"; migrating jobs to `cmake --preset` / `ctest --preset` collapses the duplicated flag blocks and turns the preset name into the natural matrix axis. [[Local Preflight Design (2026-06)]] practice 2: `CMakePresets.json` is already schema v6, so a `workflowPresets` array chaining configure→build→test is pure JSON — but CI must consume the presets, otherwise they are "a third copy of the flags."

**Gap.** Every configuration exists two or three times (preset, ci.yml flag block, and for some lanes a second workflow's flag block), with no mechanism keeping them equal; the `undefined` and `memory` sanitizer legs exist only in YAML and cannot be reproduced locally by preset at all.

**Candidate recommendation.** Convert the configure/build/test steps of `ci.yml` (`linux`, `linux-ipc`, `sanitizers`, `fuzz`, `coverage`), `sprint2-checks.yml` `multi-instance-tests`, and `pal-ci.yml` build jobs to `cmake --preset` / `ctest --preset`; add the missing presets (`ubsan`, `msan`, `library-mode`, headless-PAL variants) to `CMakePresets.json` so the preset set covers every CI cell; make the preset name the matrix variable of the reusable workflow from finding 1.

### 3. Three workflows are path-filtered at workflow level, which blocks required-check use; the fourth has no filter at all

**Current.** [[CI Gate Coverage Map]]: `ci.yml` has no `paths:` filter — it fires on every push/PR to its branches regardless of files changed (`.github/workflows/ci.yml:18-27`), so a docs-only or wiki-only change runs the full build matrix while no job examines the changed files. `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` are filtered at the workflow level (`pal-ci.yml:3-24`, `module-dag.yml:18-45`, `sprint2-checks.yml:3-27`). [[CI Workflows (GitHub Actions)]] adds that a push touching `include/**` triggers all four workflows simultaneously with no `concurrency:` group anywhere.

**Practice.** [[CI Design for C++-CMake Monorepos (2026-06)]] practice 3: "Never path-filter a required workflow; skip at job level instead" — a workflow skipped by `paths:` leaves its checks Pending forever on a PR that requires them, while a job skipped by `if:` reports Success. The prescribed factoring: trigger broadly, compute changed paths in a cheap first job, gate expensive jobs with job-level `if:` on its outputs. [[Merge Queues & Required Checks (2026-06)]] P4 draws the consequence: path-filtered workflows "must not be required as-is."

**Gap.** As factored, none of the fifteen jobs in the three filtered workflows can ever participate in branch protection, while the one workflow that could be required burns the full matrix on changes it does not inspect.

**Candidate recommendation.** Restructure around one entry workflow: move the path conditions of `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` out of `on.paths` and into a changed-paths detection job (e.g. `dorny/paths-filter` or a `git diff --name-only` step) whose outputs gate the downstream jobs via job-level `if:`; give `ci.yml` the same detection job so heavyweight build jobs skip-with-success on docs/wiki-only changes; add a `concurrency:` group keyed on ref to all entry workflows.

### 4. The path filters that do exist are imprecise — orphaned gates, over-broad triggers, and asymmetric branch scope

**Current.** [[CI Gate Coverage Map]]: `openspec/**` appears in no workflow's `paths:`, so `check_openspec_staleness.py` never fires on the changes it polices ([[Quality Gate Scripts & Hooks]] documents the same orphan); `sprint2-checks.yml` is not triggered by `cmake/**` although the module system it validates lives there (`sprint2-checks.yml:6-7, 18-19`); `docs/**` outside `docs/architecture/**` and `audit-wiki/**` trigger only the unfiltered `ci.yml` full build. [[CI Workflows (GitHub Actions)]]: `pal-ci.yml` triggers on all of `include/**` rather than its own module's headers (`pal-ci.yml:6-21`), so any public-header change runs all eight PAL jobs; `sprint2-checks.yml` alone has no branch filter and fires on pushes to any branch (`sprint2-checks.yml:4-14`); and the map notes module-dag/sprint2 are *triggered* by `src/legends_proxy/**` but configure without IPC, so they never compile what triggered them.

**Practice.** [[Test Impact Analysis & Selection (2026-06)]] practice 2: derive changed-path→target mapping from the machine-readable module manifest — `cmake/ModuleManifest.cmake` already declares per-module include/src path prefixes — with practice 3's safe fallback ("anything unrecognized → run everything"). [[CI Design for C++-CMake Monorepos (2026-06)]] practice 4: trigger hygiene, including consistent branch scoping across workflows.

**Gap.** Filters are maintained ad hoc per workflow rather than derived from the module layout, producing both false negatives (openspec, cmake/**) and false positives (all-of-`include/**` for PAL, proxy paths triggering jobs that cannot build the proxy).

**Candidate recommendation.** Generate the path-filter map from `cmake/ModuleManifest.cmake` prefixes and use it in the changed-paths job of finding 3: narrow the PAL trigger to `src/pal/**` + `include/pal/**` + `tests/unit/test_pal_*`; add `openspec/**` to the trigger set of the staleness gate and `cmake/**` to the sprint2 gate set; align `sprint2-checks.yml` branch scope with the other workflows (or document why any-branch is intended).

### 5. The CI job graph does not mirror the module DAG: license-critical modules get one job, leaf modules get five workflows

**Current.** [[CI Gate Coverage Map]]: `legends_proxy` and `legends_engine_host` — the MIT/GPL boundary targets — are compiled only when `LEGENDS_USE_IPC=ON`, which exactly one job at any tier sets (`ci.yml` `linux-ipc`, `.github/workflows/ci.yml:95-127`); they are never built on Windows or macOS. Meanwhile `legends_pal` is exercised by ci.yml's four build jobs plus all eight `pal-ci.yml` jobs plus module-dag and sprint2. [[Build & CI System (Project Legends)]]: `legends_verify_all_dags()` verifies only `legends_core`, `legends_pal`, and `aibox_core` (`cmake/ModuleDAG.cmake:196-206`) — the three IPC-split targets are never passed to the verifier — so the dedicated `module-dag.yml` workflow structurally cannot check the edges that carry the license guarantee.

**Practice.** [[Vendored & License-Isolated Dependency CI (2026-06)]] practice 1: extend the existing FATAL_ERROR DAG verifier to `legends_ipc`, `legends_proxy`, `legends_engine_host` — "a several-line change activating an existing gate on the exact MIT↔GPL boundary." [[Test Impact Analysis & Selection (2026-06)]]: the module DAG in `cmake/ModuleManifest.cmake` is the machine-readable ground truth CI jobs should be organized around.

**Gap.** CI effort is allocated inversely to module risk: the workflow named "Module DAG" verifies half the modules and none of the license-critical ones, and the IPC stack's platform coverage is a single Linux Debug job.

**Candidate recommendation.** In `module-dag.yml` `cmake-dag`, configure with `-DLEGENDS_USE_IPC=ON` and extend `legends_verify_all_dags()` / `legends_detect_cycles()` in `cmake/ModuleDAG.cmake` to the three IPC targets (guarded by `if(TARGET ...)`); add a Windows IPC cell to the matrix of the reusable build workflow (finding 1) so `legends_proxy`/`legends_engine_host` compile on both shipping platforms.

### 6. The monolithic unit-test binary makes per-module job factoring impossible downstream

**Current.** [[CI Workflows (GitHub Actions)]]: `sprint2-checks.yml` `multi-instance-tests` builds the full `legends_unit_tests` target, runs a `MultiInstance*:Sprint2*:GslContract*:ContractGates*` filtered subset, then runs the entire unfiltered binary that ci.yml's ctest run also executes (`sprint2-checks.yml:98-114` vs `ci.yml:63-77`); `pal-ci.yml` `contract-gates` similarly carves its slice with a gtest filter (`pal-ci.yml:138-181`). Every workflow that wants a module-scoped signal must first compile and link the whole suite.

**Practice.** [[Test Impact Analysis & Selection (2026-06)]]: the single `add_executable` is "the degenerate case" where build-graph selection saves nothing; the mitigations are module-level `LABELS` inside the suite (select with `ctest -L`, anchored regexes) and, for compile/link savings, splitting the binary along `cmake/ModuleManifest.cmake` module lines — "the only way path-based selection can also skip compilation and linking."

**Gap.** Workflow-level modularity is capped by target-level modularity: even a perfectly factored job matrix re-pays the full suite build for every module-scoped check, which is why sprint2 and pal-ci resort to gtest string filters over the monolith.

**Candidate recommendation.** Add module labels at the `gtest_discover_tests` registrations in `CMakeLists.txt` (e.g. `unit;mod_ipc`, `unit;mod_pal`) and replace the gtest string filters in `sprint2-checks.yml:110-114` and `pal-ci.yml:138-181` with `ctest -L` selections; treat splitting `legends_unit_tests` along manifest module lines as the follow-on that lets the finding-3 path gating skip whole build jobs.

### 7. The script-gate layer is factored as inline YAML steps, not a callable unit shared with the local loop

**Current.** [[Quality Gate Scripts & Hooks]]: the `globals-registry` job is ten consecutive Python steps written directly into `sprint2-checks.yml:44-85`; `module-dag.yml` inlines `check_includes.py` separately (`module-dag.yml:64-66`); `ci.yml` inlines the ABI compile (`ci.yml:414-419`). [[Local Dev Loop]]: no single command reproduces this set locally — the pre-commit hook runs one of the eleven scripts, and replicating the mandatory tier takes five manual steps across four workflows.

**Practice.** [[Local Preflight Design (2026-06)]] practice 1: one committed entry point that both CI and developers run, with CI rewired to invoke it so "the YAML degrades into a thin trigger wrapper" — the inverse of gate logic living in workflow steps. The same page's hook-manager practices make the entry point's subsets the hook tiers.

**Gap.** The gate suite has no module boundary of its own: adding, reordering, or fixing a check means editing workflow YAML in up to three files, and the local/CI divergence documented in [[Local Dev Loop]] is the direct result.

**Candidate recommendation.** Add `scripts/preflight.py` that runs the eleven check scripts plus the ABI compile with selectable subsets; replace the step lists in `sprint2-checks.yml:44-85` and `module-dag.yml:64-66` and the inline ABI step in `ci.yml:414-419` with single invocations of it; point `.githooks/pre-commit` (or a hook manager) at the same entry point.

### 8. Cross-cutting workflow policy is re-decided per file and has diverged

**Current.** [[CI Workflows (GitHub Actions)]] "Cross-workflow observations": every `ci.yml` job sets `timeout-minutes` while none of the fifteen jobs in the other three files does (GitHub default 360 min); only `ci.yml` sets `permissions: contents: read`; no workflow declares a `concurrency:` group; nightly crons are three separate values (03:00 / 04:00 / 04:30) with sprint2 having no schedule and no `workflow_dispatch`; "Optional" display-name prefixes appear on jobs that in fact run on the mandatory tier.

**Practice.** [[CI Design for C++-CMake Monorepos (2026-06)]] practice 4 (LLVM trigger and hardening hygiene: top-level read permissions, versioned runners, self-testing workflows) and practice 2: a reusable workflow is also where shared policy lives once instead of four times. [[Merge Queues & Required Checks (2026-06)]] P5 notes the same per-file divergence hazard for event whitelists in job-level `if:` conditions.

**Gap.** Because there is no shared layer, each hygiene property exists only where one file's author happened to add it; the four files disagree on timeouts, permissions, concurrency, scheduling, and naming conventions for the same tier.

**Candidate recommendation.** Centralize policy in the finding-1 reusable workflow (timeout, permissions, runner versions) and add to each remaining entry workflow a `permissions: contents: read` block, a `concurrency:` group, and explicit `timeout-minutes`; rename or re-tier the "Optional"-prefixed jobs so display names match the trigger tier recorded in [[CI Gate Coverage Map]].

## Candidate recommendations

| id | Summary | Affected gates |
|---|---|---|
| M-1 | Factor the checkout→configure→build→test skeleton into a `workflow_call` reusable workflow (`build-and-test.yml`) and call it from all four workflows; fold `pal-ci` `abi-c-compile` into `ci.yml` `abi-check` | ci.yml `linux`/`linux-ipc`/`windows`/`coverage`/`abi-check`; pal-ci `headless-tests`/`sdl2-tests`/`sdl3-tests`/`windows-build`/`abi-c-compile`; module-dag `build-linux`/`build-windows`; sprint2 `multi-instance-tests` |
| M-2 | Switch CI configure/build/test steps to `cmake --preset`/`ctest --preset`; add missing presets so every CI cell has one; make preset the matrix axis | ci.yml `linux`/`linux-ipc`/`sanitizers`/`fuzz`/`coverage`; sprint2 `multi-instance-tests`; pal-ci build jobs |
| M-3 | Replace workflow-level `paths:` filters with a changed-paths detection job plus job-level `if:` skips; add `concurrency:` groups; let ci.yml skip build jobs on docs/wiki-only changes | all jobs of pal-ci.yml, module-dag.yml, sprint2-checks.yml; ci.yml build jobs |
| M-4 | Derive path filters from `cmake/ModuleManifest.cmake`: narrow pal-ci's `include/**`, add `openspec/**` and `cmake/**` where their checks live, align sprint2's branch scope | pal-ci trigger set; sprint2 `globals-registry` (openspec staleness, cmake-adjacent checks); sprint2 branch filter |
| M-5 | Align CI with the module DAG: configure module-dag with `LEGENDS_USE_IPC=ON`, extend `legends_verify_all_dags()`/`legends_detect_cycles()` to the three IPC targets, add a Windows IPC build cell | module-dag `cmake-dag`; ci.yml `linux-ipc`; new Windows IPC job |
| M-6 | Add module-level CTest labels inside `legends_unit_tests` and replace gtest string filters with `ctest -L`; stage a split of the monolith along manifest module lines | sprint2 `multi-instance-tests`; pal-ci `contract-gates`; all ctest-running jobs |
| M-7 | Create `scripts/preflight.py` as the single gate entry point; rewire sprint2/module-dag script steps and ci.yml's inline ABI step to call it; point the pre-commit hook at the same command | sprint2 `globals-registry`; module-dag `include-rules`; ci.yml `abi-check`; `.githooks/pre-commit` |
| M-8 | Centralize cross-cutting policy (timeouts, `permissions`, `concurrency`, runner versions) in the reusable workflow and entry workflows; reconcile "Optional" job naming with actual tiers | all 31 job definitions across the four workflows |

## Related

- [[CI Gate Coverage Map]] — tier and path-coverage ground truth the findings cite
- [[CI Workflows (GitHub Actions)]] — duplication inventory underlying findings 1, 3, 8
- [[Build & CI System (Project Legends)]] — preset bypass and DAG-verifier scope (findings 2, 5)
- [[Quality Gate Scripts & Hooks]], [[Local Dev Loop]] — gate-layer factoring (finding 7)
