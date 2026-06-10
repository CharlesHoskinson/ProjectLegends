---
type: synthesis
aliases: ["Maintainability Gap Analysis", "CI Maintainability Gaps (2026-06)"]
tags: [synthesis, type/synthesis, topic/audit, topic/ci, topic/maintainability]
created: 2026-06-10
updated: 2026-06-10
status: draft
question: Where does the Project Legends CI/build machinery diverge from maintainability best practice — YAML size and drift, script sprawl, hook friction, caching, runtimes, doc/CI mismatch — and what would close each gap?
sources:
  - "[[CI Design for C++-CMake Monorepos (2026-06)]]"
  - "[[Local Preflight Design (2026-06)]]"
  - "[[Compiler Caching on GitHub Actions (2026-06)]]"
  - "[[Merge Queues & Required Checks (2026-06)]]"
  - "[[Test Impact Analysis & Selection (2026-06)]]"
  - "[[Vendored & License-Isolated Dependency CI (2026-06)]]"
  - "[[CI Run History (2026-06)]]"
confidence: moderate
---

# Gap Analysis — Maintainability (2026-06)

Gap analysis for the maintainability axis of the CI/build system: how hard the machinery is to read, change, run locally, and keep truthful. Current state is drawn from [[CI Workflows (GitHub Actions)]], [[Build & CI System (Project Legends)]], [[Quality Gate Scripts & Hooks]], [[Local Dev Loop]], and [[CI Gate Coverage Map]]; external practice from the 2026-06 research sources; empirical runtimes from [[CI Run History (2026-06)]]. Sibling axes (enforcement, verification-lane efficacy) are out of scope here. Candidate recommendations are inputs to the adversarial review and sprint derivation, not a ranked plan.

## Findings

### 1. Hand-rolled workflow YAML duplicates configuration that CMakePresets.json already centralizes

**Current** — `ci.yml` alone is 931 lines defining 16 job IDs; the four files in `.github/workflows/` total 31 job definitions ([[CI Workflows (GitHub Actions)]], `.github/workflows/ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`). No workflow invokes any CMake preset — every job configures with explicit `cmake -B build` flag lists, and CI jobs replicate the `ipc`, `asan`/`tsan`, `fuzz`, and `coverage` preset configurations by hand, flag for flag ([[Build & CI System (Project Legends)]], `CMakePresets.json`, `.github/workflows/ci.yml:110-116, 340-374, 499-505, 724-730`). The result is three copies of every lane definition: the preset, the YAML flag block, and whatever a developer types locally ([[Local Dev Loop]]).

**Practice** — CMake presets exist precisely "to support CI builds"; the preset name should be the single source of truth and the natural matrix axis, with `workflowPresets` chaining configure→build→test behind one `--preset` name ([[CI Design for C++-CMake Monorepos (2026-06)]], practices 1, 7). Duplicated checkout→configure→build→test skeletons belong in one `workflow_call` reusable workflow taking `{os, preset, ctest-args}` inputs ([[CI Design for C++-CMake Monorepos (2026-06)]], practice 2). `CMakePresets.json` is already at schema v6, where workflow presets are available, so the migration is pure JSON plus YAML deletion ([[Local Preflight Design (2026-06)]], practice 2).

**Gap** — Every flag change must be applied in two to four places, and nothing detects when the copies diverge; the asan/tsan presets and their CI counterparts can already drift silently because neither references the other.

**Candidate recommendation** — Add a `workflowPresets` array to `CMakePresets.json` covering the mandatory-tier lanes; create `.github/workflows/build-and-test.yml` (`on: workflow_call`, inputs `{os, preset, ctest-args}`); rewrite the build/test jobs of `ci.yml`, `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` to call it with `cmake --workflow --preset <name>` so the YAML carries no configure flags.

### 2. Five-way build duplication across workflows multiplies both compute and maintenance surface

**Current** — The same Linux gcc headless build+test is performed independently by `ci.yml linux`, `ci.yml coverage`, `module-dag.yml build-linux`, `sprint2-checks.yml multi-instance-tests`, and `pal-ci.yml headless-tests`; the Windows MSVC build by three workflows; the C11 ABI check, the ASan build, and the SDL3 build each by two ([[CI Workflows (GitHub Actions)]], "Inter-workflow build duplication" and "Overlap clusters"). No workflow declares a `concurrency:` group, and a push to `master` touching `include/**` runs all four workflows simultaneously ([[CI Workflows (GitHub Actions)]], "Cross-workflow observations").

**Practice** — Factor repeated jobs into one reusable workflow matrixed by preset, then trigger one entry workflow broadly and gate expensive jobs with job-level `if:` on a cheap changed-paths job — job-level skips report Success and stay required-check-compatible, unlike the workflow-level `paths:` filters that `pal-ci.yml` and `module-dag.yml` use today ([[CI Design for C++-CMake Monorepos (2026-06)]], practices 2-3). The rerun-everything posture is also the baseline that changed-path → module-DAG selection is meant to replace ([[Test Impact Analysis & Selection (2026-06)]], practice 2).

**Gap** — Each duplicated build is a separately maintained flag set that drifts (pal-ci builds default-buildtype where ci.yml builds Release; sprint2 adds `LEGENDS_LIBRARY_MODE=ON`), and each runs cold (finding 3), so the duplication is paid in full on every matching push.

**Candidate recommendation** — Collapse the overlap clusters into the finding-1 reusable workflow: delete `pal-ci.yml`'s `headless-tests`, `windows-build`, and `abi-c-compile` jobs and `module-dag.yml`'s `build-linux`/`build-windows` jobs in favor of matrix cells of the entry workflow; keep their distinguishing checks (PAL backend flags, contract gates, DAG configure) as job-level steps or `ctest` label selections; add a `concurrency:` group per workflow.

### 3. No compiler cache anywhere; one job rebuilds SDL3 from an upstream clone every run

**Current** — The only caching in any workflow is `actions/cache@v4` on the SDL3 dependency directory in four `ci.yml` jobs; "No compiler cache (ccache/sccache) appears anywhere in the file; every job compiles the tree cold" ([[CI Workflows (GitHub Actions)]], `.github/workflows/ci.yml:164-167`). The 1M-line vendored engine rebuilds cold up to ~12 times per push ([[Build & CI System (Project Legends)]]). `pal-ci.yml sdl3-tests` clones SDL3 `main` at depth 1 and builds it from source on each run with no cache step, in contrast to ci.yml's cached, pinned FetchContent SDL3 ([[CI Workflows (GitHub Actions)]], `pal-ci.yml:96-101`).

**Practice** — Adding `-DCMAKE_C[XX]_COMPILER_LAUNCHER` is mechanical for the six Ninja-based Linux jobs; Windows needs `-G Ninja` plus sccache with its native GHA backend; per-configuration cache keys written by push builds on `master`/`develop` and read by PRs; the launcher propagates to FetchContent sub-builds with no extra wiring, and engine TUs should hit at a very high rate once warmed because typical PRs do not touch `engine/` ([[Compiler Caching on GitHub Actions (2026-06)]], practices 1, 2, 4, 5, 7).

**Gap** — The dominant compute in every job is recompilation of code that did not change, and the one job that builds SDL3 from a moving upstream branch re-pays a full third-party build per run while also floating its dependency pin.

**Candidate recommendation** — Add ccache via `hendrikmuhs/ccache-action` plus launcher flags to the `linux`, `linux-ipc`, `linux-sdl3`, `sanitizers`, `fuzz`, and `coverage` jobs in `ci.yml`; convert the `windows`/`windows-sdl3` jobs to `-G Ninja` + sccache (`SCCACHE_GHA_ENABLED`); in `pal-ci.yml sdl3-tests`, replace the upstream `main` clone with the pinned FetchContent path and the existing `sdl3-*` cache key pattern; print cache statistics in every job.

### 4. Job runtimes are unbounded outside ci.yml and unmeasured against any budget

**Current** — Median job durations from the 30-run sample: `Optional Windows Build` 1037 s, `Windows (MSVC)` 960 s, the four sanitizer legs 628–680 s, `Code Coverage` 502 s; the sum of all job medians is ≈3 h 05 min of serial compute per full cycle ([[CI Run History (2026-06)]], "Job-level"). Every `ci.yml` job sets `timeout-minutes` (5–30), but none of the 15 jobs in the other three workflow files sets any, leaving them at GitHub's 360-minute default — including the slowest job measured, pal-ci's Windows build ([[CI Workflows (GitHub Actions)]], "Timeout coverage").

**Practice** — Wall-clock of the gating lane bounds integration cycle time, and the cost per run is what makes a merge queue (or simply frequent pushes) affordable — compiler caching in `ci.yml` is named as the prerequisite for cheap re-validation ([[Merge Queues & Required Checks (2026-06)]], P4, P6). Cache-hit compiles cost a small fraction of cold compiles, so the same jobs shrink without losing coverage ([[Compiler Caching on GitHub Actions (2026-06)]], practice 7).

**Gap** — A hung pal-ci or sprint2 job can occupy a runner for six hours before GitHub kills it, and there is no recorded runtime budget against which a regression in job duration would even be noticed.

**Candidate recommendation** — Set `timeout-minutes` on all 15 jobs in `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml`, sized from the [[CI Run History (2026-06)]] medians (e.g. 2× median); after finding-3 lands, re-extract the job-duration table and record the warmed medians as the budget baseline in the wiki.

### 5. Eleven gate scripts with no aggregate entry point, one orphan, and gate logic embedded in YAML steps

**Current** — Eleven `check_*.py` scripts exist under `scripts/`; ten run in CI — nine as Python steps of the `sprint2-checks.yml globals-registry` job (eight standalone checks plus the strict graphify check, alongside its enrichment step) and one (`check_includes.py`) in `module-dag.yml` `include-rules`, and one — `scripts/check_compiler.py` — is invoked by no workflow and no hook ([[Quality Gate Scripts & Hooks]], `scripts/`, `.github/workflows/sprint2-checks.yml:44-85`). The scripts have no dedicated unit tests; their only validation is execution-as-test when the workflow happens to fire ([[CI Gate Coverage Map]], `scripts/**` row). No single command — documented or scripted — reproduces the mandatory tier; replication takes five manual steps across four workflows ([[Local Dev Loop]], "Replicating the mandatory CI tier locally").

**Practice** — Design checks to run locally first, then have CI call the same script developers call, each script "responsible for a unit of work"; gate logic living only in workflow YAML steps is the inverted architecture, and divergence between local and CI commands is the documented failure mode ([[Local Preflight Design (2026-06)]], practice 1). Python is already the gate-script language and CI already pip-installs the one dependency, so a `scripts/preflight.py` wrapping script gates + ABI check + OS-reachable workflow presets is the smallest-delta single entry point ([[Local Preflight Design (2026-06)]], practices 1, 4).

**Gap** — Adding or reordering a gate means editing workflow YAML rather than one script; nothing a developer can run locally corresponds to what CI enforces; and an orphaned script sits in the gate directory indistinguishable from the live ones.

**Candidate recommendation** — Create `scripts/preflight.py` with sub-commands for the script-gate suite, the ABI check, and the workflow-preset builds; rewrite `sprint2-checks.yml`'s ten gate steps and `ci.yml`'s `abi-check` step body to invoke it; either wire `scripts/check_compiler.py` in as a preflight diagnostic or delete it; document `preflight` as the pre-push command in `CONTRIBUTING.md`.

### 6. Hook installation is opt-in, single-check, and documented nowhere a contributor looks

**Current** — `.githooks/pre-commit` runs exactly one of the eleven check scripts (`check_includes.py`), takes effect only after a developer runs `git config core.hooksPath .githooks`, and that instruction exists solely as a comment inside the hook file; `README.md`, `CONTRIBUTING.md`, `AGENTS.md`, and `docs/` contain no developer-facing mention of hook installation, `check_` scripts, or `scripts/` ([[Quality Gate Scripts & Hooks]], `.githooks/pre-commit:3, 7`; [[Local Dev Loop]]). Of fourteen mandatory-tier gate rows, the default local loop covers three; installing the hook adds exactly one ([[Local Dev Loop]], gate table).

**Practice** — Both mainstream hook managers fix the two defects at once: a committed config covering all checks and a one-line documented install (`pre-commit install` / `lefthook install`), with installation verified rather than trusted (`lefthook check-install`, or the preflight target probing `core.hooksPath`) and the identical config run in CI so opting out only moves the failure later ([[Local Preflight Design (2026-06)]], practices 3, 6). The bash-only hook depending on Git-for-Windows' bundled sh is specifically called the weakest option for a Windows+Linux team ([[Local Preflight Design (2026-06)]], practice 5).

**Gap** — A contributor following the written docs never installs the hook and first encounters ten of the eleven gates as post-push CI failures; the one gate the hook does run is silently absent on any clone where the undocumented `git config` step was skipped.

**Candidate recommendation** — Adopt a hook manager (pre-commit with `repo: local` entries, or lefthook) with a committed config tiering the eleven scripts (staged-file checks at commit, script suite + one workflow preset at push); replace `.githooks/pre-commit` with the manager shim; add a Setup section to `CONTRIBUTING.md` (clone → bootstrap → hook install → preflight); have `sprint2-checks.yml` run the same hook config as its gate step.

### 7. Documentation asserts gates and mechanisms that the code does not implement

**Current** — `CONTRIBUTING.md:157` states Tier B is "Applied via `legends_set_legacy_cxx_standard()`", but that function is defined and never called; the engine gets de-facto Tier B treatment through a different mechanism ([[Build & CI System (Project Legends)]], `CMakeLists.txt:126-138`, `engine/CMakeLists.txt:75-81`). The `LEGENDS_WERROR` flag passed by the audit-local build script is read by no CMake file — there is no built-in switch to disable Tier A's `-Werror` ([[Build & CI System (Project Legends)]], `llm-wiki/_scratch/build.cmd:6`). `README.md:91` lists OpenSpec among the "Quality and architecture gates", but no workflow runs the `openspec` CLI, and `openspec/**` appears in no workflow's `paths:`, so even the staleness scan never fires on openspec changes ([[Quality Gate Scripts & Hooks]], "The openspec validation gate"; [[CI Gate Coverage Map]], `openspec/**` row). The isolation verifier is documented as a CI gate but never executed ([[Build & CI System (Project Legends)]]; `cmake/VerifyGPLIsolation.cmake`).

**Practice** — The parity principle generalizes: documentation that names a command no one runs is the same drift class as a local loop that diverges from CI, and the cure is making the documented entry point the thing CI executes ([[Local Preflight Design (2026-06)]], practices 1, 6). For the licensing instance specifically, mechanically checked per-file ground truth with prose demoted to an overview is the pattern that "ends the LICENSE-vs-source drift class for good" — checked artifacts over asserted ones ([[Vendored & License-Isolated Dependency CI (2026-06)]], practices 2, 4).

**Gap** — A reader of `CONTRIBUTING.md` or the README acquires beliefs about enforcement (Tier B mechanism, OpenSpec gating, isolation verification) that are false at HEAD, and there is no check that fails when docs and machinery part ways.

**Candidate recommendation** — Correct `CONTRIBUTING.md:157` to describe the actual engine warning mechanism (or call `legends_set_legacy_cxx_standard()` on `aibox_core` so the doc becomes true); implement `LEGENDS_WERROR` as a real CMake option in `CMakeLists.txt` or delete it from `llm-wiki/_scratch/build.cmd`; either add an `openspec validate --strict` step plus `openspec/**` path entries to `sprint2-checks.yml` or remove OpenSpec from the README gate diagram; wire `cmake/VerifyGPLIsolation.cmake` into the `linux-ipc` job (per the licensing research) or strike the claim from the docs.

### 8. The workflow files themselves are the only unvalidated source files in the repo

**Current** — No job lints or validates workflow YAML content; the only effect of editing a workflow is re-running it ([[CI Gate Coverage Map]], `.github/workflows/**` row). The run history shows a concrete consequence: the `Optional Linux SDL3 (${{ matrix.compiler }})` job recorded under its unexpanded template name, never executing as such ([[CI Run History (2026-06)]], "Nightly/manual-only lanes"). All four workflows use mutable action tags and `*-latest`/`macos-15` runner labels; only `ci.yml` sets a `permissions:` block ([[CI Workflows (GitHub Actions)]]).

**Practice** — LLVM's CI rules: workflows should be tested by the PRs that change them, third-party actions hash-pinned to commit SHAs because release tags are mutable, runner images versioned so rolls are opt-in, and read-only default permissions set at the top of every file ([[CI Design for C++-CMake Monorepos (2026-06)]], practice 4). Required-check selection by exact expanded job name makes name drift a merge-blocking hazard, so the names need machine checking before anything is made required ([[Merge Queues & Required Checks (2026-06)]], P4).

**Gap** — A typo, a renamed job, a broken `if:` expression, or a mutated action tag in 1,526 lines of workflow YAML across four files reaches `master` unchecked, and the failure surfaces only as the next confusing run — or, once checks become required, as a merge deadlock.

**Candidate recommendation** — Add an `actionlint` job (running on push/PR with `.github/workflows/**` in scope) to `ci.yml` or a new `lint.yml`; in the same pass, hash-pin all third-party actions, replace `ubuntu-latest`/`windows-latest` with versioned labels, and add `permissions: contents: read` to `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml`.

## Candidate recommendations

| id | Summary | Affected gates |
|---|---|---|
| A-1 | Move all configure flags into CMake presets + `workflowPresets`; factor builds into one reusable `workflow_call` workflow | all build/test jobs in ci.yml, pal-ci.yml, module-dag.yml, sprint2-checks.yml |
| A-2 | Collapse the duplicate Linux/Windows/ABI/ASan/SDL3 builds across workflows into matrix cells of the entry workflow; add `concurrency:` groups | pal-ci `headless-tests`/`windows-build`/`abi-c-compile`, module-dag `build-linux`/`build-windows`, sprint2 `multi-instance-tests`, ci.yml `abi-check` |
| A-3 | Add ccache (Linux/macOS) and Ninja+sccache (Windows) compiler caching; pin and cache pal-ci's SDL3 build | ci.yml `linux`, `linux-ipc`, `linux-sdl3`, `windows`, `windows-sdl3`, `sanitizers`, `fuzz`, `coverage`; pal-ci `sdl3-tests` |
| A-4 | Set `timeout-minutes` on the 15 unbounded jobs; baseline job-duration budgets from run-history medians | all jobs in pal-ci.yml, module-dag.yml, sprint2-checks.yml |
| A-5 | Create `scripts/preflight.py` as the single gate entry point; CI steps call it; resolve the `check_compiler.py` orphan | sprint2 `globals-registry` (all ten script steps), ci.yml `abi-check` |
| A-6 | Replace the one-check opt-in hook with a committed hook-manager config covering all check scripts; document setup in CONTRIBUTING.md; run the same config in CI | `.githooks/pre-commit`, sprint2 `globals-registry` |
| A-7 | Reconcile docs with machinery: Tier B claim, inert `LEGENDS_WERROR`, README OpenSpec gate, unwired isolation verifier | sprint2 `globals-registry` (openspec step), ci.yml `linux-ipc`, CMake Tier A/B functions |
| A-8 | Lint the workflows: actionlint job, SHA-pinned actions, versioned runner images, default read permissions | new lint job; all four workflow files |

## Related

- [[CI Workflows (GitHub Actions)]], [[Build & CI System (Project Legends)]], [[Quality Gate Scripts & Hooks]], [[Local Dev Loop]] — current-state inventories cited above
- [[CI Gate Coverage Map]] — per-path enforcement context for the affected gates
- [[CI Run History (2026-06)]] — empirical runtimes behind findings 3-4
- [[Sprint Plan Derivation (2026-06)]] — downstream consumer of these candidates
