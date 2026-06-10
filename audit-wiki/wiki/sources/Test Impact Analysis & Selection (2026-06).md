---
type: source
aliases: ["Test Impact Analysis", "TIA Research", "Regression Test Selection Research"]
tags: [source, type/source, topic/ci, topic/testing, topic/research]
created: 2026-06-10
updated: 2026-06-10
status: draft
title: Test Impact Analysis & Selection (2026-06)
authors: [web research synthesis]
url: see per-claim citations
publisher: multiple (Microsoft, Meta, Google, Kitware, bazel-contrib, ACM/ISSTA)
published: 2015-2026
accessed: 2026-06-10
source_type: research-synthesis
covers:
  - "[[Project Legends Test Suite]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[CI Workflows (GitHub Actions)]]"
---

# Test Impact Analysis & Selection (2026-06)

## Summary

Research synthesis on selecting which tests to run per change instead of rerunning everything. Raw passages in `raw/research/test-impact-analysis.md`. Project Legends context: C++23/CMake/CTest, GoogleTest with ~4,600 `TEST` macros across 252 files, most of them compiled into one `legends_unit_tests` binary (`CMakeLists.txt:629`), plus engine tests (`engine/tests/CMakeLists.txt`) and integration suites; the module DAG is already machine-readable in `cmake/ModuleManifest.cmake` (`LEGENDS_DAG_*` variables plus per-module include/src path prefixes); CI currently reruns all suites on every push (see [[CI Workflows (GitHub Actions)]]).

The literature splits into three schools: *safe* selection (run every test whose dependencies changed — Ekstazi, classic RTS), *heuristic/predictive* selection (run the tests most likely to fail — Meta, Google TAP scheduling), and *tiering* (run a cheap labeled subset always, the rest on a schedule — Microsoft TIA's periodic full runs, CTest labels). For a repo of this size the practical path is tiering plus path→module mapping, with safe fallback to everything; the monolithic unit-test binary caps how much any build-graph-based technique can save.

## Background: what TIA does

Test Impact Analysis selects, for a given commit, "only the subset of tests required to validate the code being committed", built from a dependency map of the form test → {files it exercised}, recorded at file granularity during prior runs ^[from https://learn.microsoft.com/en-us/azure/devops/pipelines/test/test-impact-analysis?view=azure-devops (retrieved 2026-06-10)]. Classical RTS phrases the correctness bar precisely: a technique is *safe* if "the subset of selected tests includes all tests whose behavior may be affected by the changes" ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)]. The economic motivation is also classical: Google observed linear growth in changes times linear growth in suite runtime = quadratic total test execution cost ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)].

## Applicable practices

### 1. Label-based tiering with CTest (lowest effort, already half-built)

CTest natively selects by label: `-L <regex>` runs only tests whose labels match (multiple `-L` AND together), `-LE` excludes, and `--print-labels` enumerates; a test with no labels is never included by `-L` ^[from https://cmake.org/cmake/help/latest/manual/ctest.1.html (retrieved 2026-06-10)]. Label matching is regex-substring, so unanchored short labels over-match ("running CTest with `-L es` will match all five tests") ^[from https://cmake.org/cmake/help/latest/manual/ctest.1.html (retrieved 2026-06-10)].

**Applicability to Project Legends.** Labels already exist at suite granularity: `gtest_discover_tests(legends_unit_tests … LABELS "unit")` (`CMakeLists.txt:819-822`), `legends_ipc_integration_tests` → `"integration;ipc"` (`CMakeLists.txt:853-855`), `legends_abi_test` → `"abi;unit"` (`CMakeLists.txt:881-887`), `legends_toolchain_tests` → `"toolchain"` (`CMakeLists.txt:929-931`), `legends_integration_tests` → `"integration"` (`CMakeLists.txt:1014-1017`), `aibox_unit_tests` → `"unit"` (`engine/tests/CMakeLists.txt:111-114`), `aibox_determinism_tests` → `"determinism"` (`engine/tests/determinism/CMakeLists.txt:33-36`). What is missing is *module-level* labels inside the monolithic unit suite: all ~4,600 unit tests share the single label `unit`, so `ctest -L` cannot today express "only IPC unit tests". Splitting the `gtest_discover_tests` call per source group (or adding `LABELS "unit;mod_ipc"` etc. via multiple discovery calls / `PROPERTIES` on discovered prefixes) is the cheapest way to make the existing label machinery selective. Anchor label regexes (`-L '^unit$'`) given the substring semantics.

### 2. Changed-path → module mapping over the existing DAG (the CMake equivalent of Bazel target determination)

The Bazel ecosystem's standard practice is to diff two commits, map changed files to build targets, and take the reverse-dependency closure to find affected test targets; bazel-contrib's target-determinator "determine[s] which Bazel targets changed between two git commits" and its `driver` binary "runs the same logic … then tests all identified targets" ^[from https://github.com/bazel-contrib/target-determinator (retrieved 2026-06-10)]. Two of its design choices transfer directly: an `-ignore-file` list for files that "shan't affect the build graph", and a default failure behavior of `ignore-and-build-all` — when the "before" analysis fails, it tests everything rather than nothing ^[from https://github.com/bazel-contrib/target-determinator (retrieved 2026-06-10)].

**Applicability to Project Legends.** The repo already has the inputs: `cmake/ModuleManifest.cmake` defines per-module path prefixes (`LEGENDS_MODULE_*_PUBLIC_INCLUDE`, `*_PRIVATE_INCLUDE`) and explicit DAG edges (`LEGENDS_DAG_legends_core "aibox_core"`, `LEGENDS_DAG_legends_proxy "legends_ipc"`, `LEGENDS_DAG_legends_engine_host "legends_core;legends_ipc"`, leaves `legends_pal`/`aibox_core`/`legends_ipc`), enforced at configure time by `ModuleDAG.cmake`. A small CI script can: (a) `git diff --name-only` against the merge base, (b) classify each path by module prefix, (c) take the reverse closure over `LEGENDS_DAG_*`, (d) emit a CTest label expression (per practice 1) or a test-name list for `ctest --tests-from-file` (CMake ≥ 3.29 runs exact test names from a file, combinable with `-R`/`-L` ^[from https://cmake.org/cmake/help/latest/manual/ctest.1.html (retrieved 2026-06-10)]). Any path that matches no module prefix (CMake files, `.github/`, `cmake/`, scripts, toolchain files) must map to "run everything" — that is Microsoft's safe-fallback rule, see practice 3.

### 3. Safe fallback and periodic full runs (non-negotiable guardrails)

Microsoft TIA ships three guardrails as first-class features: selection includes "existing impacted tests, previously failing tests, and newly added tests"; "for commits and scenarios that TIA can't understand, it falls back to running all tests" (e.g., file types it cannot reason about); and "you can run all tests at a configured periodicity", which the docs call "the means to regulate test selection" ^[from https://learn.microsoft.com/en-us/azure/devops/pipelines/test/test-impact-analysis?view=azure-devops (retrieved 2026-06-10)]. Microsoft also documents a validation protocol: run selected tests (T1) then all tests (T2) in sequence and check that T1's verdict predicts T2's ^[from https://learn.microsoft.com/en-us/azure/devops/pipelines/test/test-impact-analysis?view=azure-devops (retrieved 2026-06-10)]. Even Meta, with probabilistic selection, runs every change through "exhaustive testing before it is deployed from the trunk to production" — selection only gates the pre-trunk loop ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)].

**Applicability to Project Legends.** Concretely: selected-subset runs on push/PR; full suite on merge to master, nightly, and whenever the diff touches any `CMakeLists.txt`, `cmake/*.cmake`, or `.github/workflows/*`. Always append previously-failed tests (`ctest --rerun-failed` reuses the last failure set) and new test files to the selection. During rollout, run the T1/T2 shadow comparison on a few PRs before trusting the subset verdict.

### 4. Risk-based prioritization (which tests first, not only which tests)

Google's TAP analysis of >500K changes found "very few of our tests ever fail, but those that do are generally 'closer' to the code they test; certain frequently modified code and certain users/tools cause more breakages; and code recently modified by multiple developers (more than 3) breaks more often" ^[from https://research.google/pubs/taming-google-scale-continuous-testing/ (retrieved 2026-06-10)]. Meta operationalized the same idea with a gradient-boosted decision-tree model trained on historical test outcomes, catching "more than 99.9 percent of all regressions … while running just a third of all tests that transitively depend on modified code", with production accuracy requirements (>95% outcome prediction, >99.9% of faulty changes flagged) and regular retraining as the codebase evolves ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)].

**Applicability to Project Legends.** Full predictive selection is over-scaled for this repo, but the cheap orderings transfer: run previously-failing tests and dependency-near tests first so a doomed run fails in seconds; keep the determinism suite (`engine/tests/determinism/`) and ABI test (`legends_abi_test`) in every tier because they police cross-cutting invariants no path filter can scope. A history-trained model is also currently *unlearnable* here: per [[CI Run History (2026-06)]] the `CI` workflow failed 87.2% of runs over the window, so historical outcomes encode pipeline breakage, not test-level regression signal. A green baseline is a prerequisite for any history-based selection.

### 5. Dependency granularity: prefer coarse and correct over fine and fragile

Ekstazi's central result is that *coarse* (file-level) dependency tracking beats fine (method-level) tracking on end-to-end time even though it selects more tests, because analysis and collection get cheap: "Although Ekstazi selects some more tests and thus has a longer execution phase, its use of much coarser dependencies shortens both the analysis and collection. As a result, Ekstazi has a much lower end-to-end time" (32% mean reduction, 54% for long suites) ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)]. Fine granularity is also where safety bugs live: naive method-level intersection misses tests affected by an *added* overriding method ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)].

**Applicability to Project Legends.** Module-prefix granularity (practice 2) is the C++ analogue of Ekstazi's file-level choice: crude, but auditable against `ModuleManifest.cmake` and cheap to compute in CI. Do not attempt per-TEST coverage-map TIA (the Microsoft dynamic-instrumentation style) first; for native code it requires per-test coverage collection infrastructure the repo lacks, and Microsoft's own implementation never supported this configuration outside managed code — its documented escape hatch for C++ is a *manually maintained, possibly approximate* dependency-map file mapping path patterns to test-case filters ^[from https://learn.microsoft.com/en-us/azure/devops/pipelines/test/test-impact-analysis?view=azure-devops (retrieved 2026-06-10)]. That manual-map pattern is exactly what `ModuleManifest.cmake` + labels can generate.

### 6. Keep fixture semantics intact when subsetting

When CTest executes a subset, setup/cleanup tests for any `FIXTURES_REQUIRED` fixture are added to the set automatically (opt-out via `-FA/--fixture-exclude-any`) ^[from https://cmake.org/cmake/help/latest/manual/ctest.1.html (retrieved 2026-06-10)].

**Applicability to Project Legends.** If integration suites grow fixtures (e.g., engine-host process startup for IPC tests), label-based subsets stay coherent for free — a reason to prefer `ctest -L` selection over invoking test binaries directly with `--gtest_filter`, which bypasses CTest's fixture and dependency machinery. Note the existing comment at `CMakeLists.txt:1023`: `gtest_discover_tests` registers tests at CTest time, so discovery-time properties are where labels must be attached.

## The monolithic binary as a TIA obstacle

Meta's diagnosis of build-dependency selection applies verbatim: "It ends up saying 'yes, this test is impacted' more often than is actually necessary … when there is a change to one of our low-level libraries, it would be inefficient to rerun all tests on every project that uses that library" ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)]. `legends_unit_tests` (`CMakeLists.txt:629-840`) is the degenerate case: one `add_executable` linking the test files plus `legends_core`, so at build-graph granularity *every* source change impacts the single test target and selection saves nothing — every change still pays the full link and, naively, the full run. Ekstazi documents the same blind spot in Google TAP: cross-project selection "provides no benefit *within a project*" ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)].

Two mitigations, not mutually exclusive:

- **Select within the binary by test name.** `gtest_discover_tests` already registers each `TEST` as an individual CTest entry, so `ctest -R`, `-L` (with finer labels), or `--tests-from-file` can run a slice without splitting the target. This saves run time but not compile/link time — the binary still rebuilds fully.
- **Split the binary along `ModuleManifest.cmake` module lines** (e.g., `legends_unit_tests_ipc`, `legends_unit_tests_pal`, …). This is the only way path-based selection can also skip compilation and linking, and it makes the build graph granularity match the module DAG that `ModuleDAG.cmake` already enforces. The cost is CMake churn across the test registration block at `CMakeLists.txt:629-840`.

## Known failure modes of TIA (honest accounting)

- **Selection is only as safe as the dependency map.** Ekstazi explicitly provides "no formal proof" of safety and inherits it informally from prior class-dependency results; method-level shortcuts are demonstrably unsafe (added-override example), and ignoring non-code dependencies (config files, data files) breaks safety, which is why Ekstazi tracks *files*, not classes ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)]. For Project Legends: tests that read fixtures from disk, environment variables, or generated headers will not be captured by a path→module map; those suites must be pinned to "always run" labels.
- **Non-code and meta changes defeat the analyzer.** Microsoft TIA "falls back to running all tests" whenever a commit contains file types it cannot reason about — correct but it silently erases the speedup, and over-eager path filters (`TIA_IncludePathFilters`) reintroduce unsafety by declaring files irrelevant ^[from https://learn.microsoft.com/en-us/azure/devops/pipelines/test/test-impact-analysis?view=azure-devops (retrieved 2026-06-10)]. Expect the fallback to fire often here: top-level `CMakeLists.txt` edits have been frequent in this repo's history.
- **Flakiness corrupts both the signal and the training data.** At Google, ~1.5% of all test runs report a flaky result, ~16% of tests show some flakiness, and "about 84% of the transitions we observe from pass to fail involve a flaky test" ^[from https://testing.googleblog.com/2016/05/flaky-tests-at-google-and-how-we.html (retrieved 2026-06-10)]. A selected-subset run makes this worse: with fewer tests executed, a flaky failure is more likely to be misread as the changed code's fault (and vice versa). Meta had to aggressively retry failures when collecting training data to separate real regressions from flakes ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)]. Quarantine helps but "could easily mask a real race condition" ^[from https://testing.googleblog.com/2016/05/flaky-tests-at-google-and-how-we.html (retrieved 2026-06-10)]. For Project Legends, the concurrency findings in [[Concurrency & Determinism Audit (2026-06)]] mean flake-vs-regression ambiguity is live, not hypothetical.
- **Build-graph granularity bounds the benefit.** Coarse target graphs over-select (Meta: a quarter of all tests per mobile change ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)]); a single test target (the `legends_unit_tests` case above) is the limit where selection degenerates to all-or-nothing.
- **Caching and environment drift produce wrong diffs.** target-determinator documents that cached "before" analyses computed under different environment variables "may produce spurious differences" because env vars are deliberately outside the cache key ^[from https://github.com/bazel-contrib/target-determinator (retrieved 2026-06-10)]. Any cached change-detection layer here (e.g., caching configure outputs across CI runs) inherits the same hazard.
- **Probabilistic selection misses regressions by design.** Meta's production bar lets up to 0.1% of faulty changes through the selective gate and catches them only in post-trunk exhaustive testing ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)]. Without that downstream full-run backstop, the same policy is just silent coverage loss.

> [!conflict]
> The schools disagree on whether selection may sacrifice safety. Classical RTS defines correctness as *safe* selection — every possibly-affected test must run ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)] — and Microsoft TIA keeps the same posture via all-tests fallback ^[from https://learn.microsoft.com/en-us/azure/devops/pipelines/test/test-impact-analysis?view=azure-devops (retrieved 2026-06-10)]. Meta explicitly abandons safety as the criterion: safe transitive selection was "inefficient", so it accepts a measured miss rate (≥99.9% of faulty changes caught, not 100%) in exchange for running a third of the tests ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)]. For a repo without Meta's post-trunk exhaustive-testing backstop and release engineering, the safe/tiered posture is the defensible one; status: open trade-off, resolved here in favor of safety.

> [!conflict]
> Granularity advice points in two directions. Ekstazi argues *coarser* dependencies win (file-level beats method-level on end-to-end time) ^[from https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf (retrieved 2026-06-10)], while Meta's complaint is that its build graph was *too* coarse and over-selected ^[from https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/ (retrieved 2026-06-10)]. The reconciliation is scale-dependent: there is a sweet spot between method-level (analysis too expensive, unsafe shortcuts) and monorepo-target-level (over-selection); for Project Legends the module granularity of `cmake/ModuleManifest.cmake` sits in that band, but the claim that it is the optimum is untested here; status: context-dependent.

## Where this lands for Project Legends

1. Add module labels inside the unit suite and select with `ctest -L` / `-LE` (practice 1, 6).
2. Drive label selection from a changed-path → `LEGENDS_DAG_*` reverse-closure script with an explicit "anything unrecognized → run everything" rule and scheduled full runs (practices 2, 3).
3. Treat splitting `legends_unit_tests` along module lines as the prerequisite for selection that saves build time, not just run time (monolithic-binary section).

Risk-based ordering (practice 4) and any history-trained selection are blocked on a green CI baseline per [[CI Run History (2026-06)]].

## Related

- [[Project Legends Test Suite]] — suite inventory and registration points
- [[Build & CI System (Project Legends)]] — build graph, module DAG enforcement
- [[CI Workflows (GitHub Actions)]] — the rerun-everything status quo
- [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]] — lanes that must stay outside any selection (cross-cutting invariants)
- Raw notes: `raw/research/test-impact-analysis.md`
