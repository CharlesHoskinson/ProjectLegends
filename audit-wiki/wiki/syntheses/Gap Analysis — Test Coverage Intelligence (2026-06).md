---
type: synthesis
aliases: ["Test Coverage Intelligence Gap Analysis"]
tags: [synthesis, type/synthesis, topic/audit, topic/testing, topic/ci]
created: 2026-06-10
updated: 2026-06-10
status: draft
question: Where does Project Legends' test-coverage intelligence — tiering, selection, ratcheting, fuzz cadence, oracle scope, fixtures — fall short of documented external practice, and what concrete changes would close each gap?
sources:
  - "[[Test Impact Analysis & Selection (2026-06)]]"
  - "[[Coverage Policy Ratcheting (2026-06)]]"
  - "[[Continuous Fuzzing in CI (2026-06)]]"
  - "[[Flaky-Test Detection & Quarantine (2026-06)]]"
  - "[[CI Design for C++-CMake Monorepos (2026-06)]]"
  - "[[Sanitizer Lane Strategy (2026-06)]]"
  - "[[Merge Queues & Required Checks (2026-06)]]"
  - "[[Vendored & License-Isolated Dependency CI (2026-06)]]"
  - "[[CI Run History (2026-06)]]"
entities:
  - "[[Project Legends Test Suite]]"
  - "[[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]"
  - "[[CI Workflows (GitHub Actions)]]"
concepts:
  - "[[Determinism Oracle Weakness]]"
confidence: moderate
---

# Gap Analysis — Test Coverage Intelligence (2026-06)

Gap analysis for the test suite considered as an *instrument*: which tests run, when, against what oracle, and what the green checkmark certifies. Current state is drawn from [[Project Legends Test Suite]], [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]], [[CI Workflows (GitHub Actions)]], and [[CI Gate Coverage Map]]; practice is drawn from the 2026-06 research source pages. Recommendations are candidates, not a ranked plan — sequencing belongs to [[Sprint Plan Derivation (2026-06)]] and its successors.

## Findings

### 1. Suite tiering exists as a comment, not as a mechanism

**Current.** `ci.yml`'s header describes a tier design (PR/develop = build + unit tests; master = + sanitizers and fuzz smoke; nightly = soak/extended fuzz; tag = packaging) at `.github/workflows/ci.yml:8-12`, but the ctest invocations inside `linux`, `linux-ipc`, `windows`, `macos`, `coverage`, and `sanitizers` are undifferentiated — no job selects by label, and the determinism suite runs only as folded-in content of the build jobs (`.github/workflows/ci.yml:77, 127, 207, 398-401`) ^[from [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]]. CTest labels stop at suite granularity: all ~4,600 unit tests share the single label `unit` (`CMakeLists.txt:822`, `engine/tests/CMakeLists.txt:114`), and `ci.yml` has no `paths:` filter, so every push reruns everything ^[from [[Project Legends Test Suite]]] ^[from [[CI Gate Coverage Map]]].

**Practice.** Label-based tiering is the lowest-effort selection scheme and is "already half-built" here; what is missing is module-level labels inside the monolithic unit suite, attached at `gtest_discover_tests` time, with anchored label regexes ^[from [[Test Impact Analysis & Selection (2026-06)]]]. Tier membership should be expressed as matrix cells named by CMake preset, with job-level `if:` skips rather than workflow-level path filters, so skipped jobs still satisfy required checks ^[from [[CI Design for C++-CMake Monorepos (2026-06)]]]. The required set itself should be a small, deterministic, exact-name list of reliably green jobs ^[from [[Merge Queues & Required Checks (2026-06)]]].

**Gap.** The tier design and the execution have no connection: every tier runs the same ctest content, so the PR tier pays nightly-tier cost while the nightly tier adds nothing the PR tier did not already run (soak and extended fuzz, the nightly tier's stated content, do not exist — see findings 4 and 8).

**Candidate recommendation.** Attach module-level labels (`mod_ipc`, `mod_pal`, `mod_engine`, …) in the `gtest_discover_tests` calls at `CMakeLists.txt:819-824, 853-856, 1014-1019` and `engine/tests/CMakeLists.txt:111-115`; replace the undifferentiated `ctest` steps in `ci.yml`'s `linux`, `windows`, and `coverage` jobs with tier-explicit `ctest -L '^<label>$'` invocations so each tier's contents are declared in the workflow rather than implied by a comment.

### 2. Test selection: the module DAG is machine-readable and unused, and the monolithic binary caps what selection can save

**Current.** CI reruns all suites on every push to `main`/`master`/`develop` because `ci.yml` carries no path filter ^[from [[CI Gate Coverage Map]]]. The repo already owns the inputs for changed-path selection — `cmake/ModuleManifest.cmake` declares per-module path prefixes and explicit `LEGENDS_DAG_*` edges, enforced at configure time by `cmake/ModuleDAG.cmake` — but nothing consumes them for test selection ^[from [[CI Workflows (GitHub Actions)]]]. All 124 unit `.cpp` files compile into the single `legends_unit_tests` target (`CMakeLists.txt:629, 944-984` for the integration sibling) ^[from [[Project Legends Test Suite]]].

**Practice.** The practical path for a repo of this size is tiering plus a changed-path → module mapping with reverse-dependency closure over `LEGENDS_DAG_*`, a safe fallback ("anything unrecognized → run everything"), previously-failed and new tests always appended, and scheduled full runs as the regulator ^[from [[Test Impact Analysis & Selection (2026-06)]]]. The same source flags the hard ceiling: a single test target is the degenerate case where build-graph selection saves nothing — splitting the binary along module lines is the prerequisite for selection that skips compilation, not just execution ^[from [[Test Impact Analysis & Selection (2026-06)]]]. History-trained selection is explicitly blocked here: with the `CI` workflow failing 87.2% of runs, historical outcomes encode pipeline breakage, not regression signal ^[from [[Test Impact Analysis & Selection (2026-06)]]] ^[from [[CI Run History (2026-06)]]].

**Gap.** Selection infrastructure is two-thirds present (DAG, labels, CTest machinery) and zero percent connected; meanwhile the monolithic unit binary guarantees that even a perfect selector pays the full compile and link on every change.

**Candidate recommendation.** Add a `scripts/select_tests.py` that diffs against the merge base, classifies paths by `cmake/ModuleManifest.cmake` prefixes, takes the reverse closure over `LEGENDS_DAG_*`, and emits a ctest label expression — falling back to the full suite when any path matches no module, when `CMakeLists.txt`/`cmake/**`/`.github/workflows/**` change, and on all master/nightly runs; wire it into `ci.yml`'s `linux` job. Separately, split `legends_unit_tests` (`CMakeLists.txt:629-840`) into per-module test targets aligned with `ModuleManifest.cmake`.

### 3. Coverage policy: report-only on every tier that runs, enforced only on a tier that has never run

**Current.** The `coverage` job runs on every trigger but writes its policy into an artifact instead of asserting anything — `"Coverage policy: report-only; no minimum threshold is enforced by CI yet."` (`.github/workflows/ci.yml:749`); the only numeric threshold in the repo is 80% on `src/app/` inside `release-validation`, gated on `v*` tags that have never been pushed (`.github/workflows/ci.yml:877-879, 907-921`) ^[from [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]] ^[from [[CI Gate Coverage Map]]]. The lcov filter (`ci.yml:744-747`) removes `/usr/*`, `*/build/_deps/*`, `*/tests/*` but not `engine/`, and the Codecov upload is conditional on a token secret (`ci.yml:759-764`) ^[from [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]].

**Practice.** Gate PRs on diff coverage rather than absolute coverage (one `diff-cover --fail-under` step on the existing `coverage.filtered.info`, token-free); ratchet the absolute floor from today's measured value via a committed floor file rather than jumping to 80%; exclude the vendored engine from the policy denominator before any number means anything; set per-module floors aligned to the module DAG; never let enforcement depend on the Codecov token; and verify any gate can actually fail before trusting it ^[from [[Coverage Policy Ratcheting (2026-06)]]].

**Gap.** No coverage number anywhere binds a merge, the one threshold that exists has never executed and may not even pass, and the published artifact mixes first-party coverage with a vendored ~1M-line engine the team does not own.

**Candidate recommendation.** In `ci.yml`'s `coverage` job: add `'*/engine/*'` to the `lcov --remove` list (`ci.yml:744-747`), replace the echo at `ci.yml:749` with a `diff-cover coverage.filtered.info --compare-branch=origin/master --fail-under=<N>` step plus a comparison against a committed `coverage-floor.txt`, and rehearse `release-validation` once via `workflow_dispatch` so its first execution is not on the release path.

### 4. Fuzzing: budgets below every documented floor, a corpus that evaporates with the runner, crashes discarded unrecorded

**Current.** The `fuzz` job runs five libFuzzer targets at 30 s each on PRs and pushes to master, 60 s otherwise (`.github/workflows/ci.yml:514-578`); the seed corpus is regenerated from scratch into `build/tests/fuzz/corpus` every run (`ci.yml:511-512`) with no cache or artifact step anywhere in the job, and no checked-in `tests/fuzz/corpus/` exists even though `tests/fuzz/CMakeLists.txt:46-49` would copy one ^[from [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]]. The harnesses are never CTest-registered (`tests/fuzz/CMakeLists.txt` has no `add_test`) ^[from [[Project Legends Test Suite]]]. The lane failed 6 of 6 sampled executions ^[from [[CI Run History (2026-06)]]].

**Practice.** Persist and grow the corpus across runs (`actions/cache` per target plus nightly `-merge=1` pruning), commit a curated seed set including past crash reproducers; convert the PR step to deterministic corpus-and-reproducer replay (libFuzzer file-list mode) and fund real fuzzing at 600 s+ per target on the nightly cron; capture crash artifacts via `-artifact_prefix` plus `upload-artifact` on failure; separate pre-existing from new crashes with a baseline so PR red means "this change broke something"; invest in seeds and dictionaries for the save-state and config formats; consider ClusterFuzzLite as the managed form of all of the above ^[from [[Continuous Fuzzing in CI (2026-06)]]].

**Gap.** Every run re-explores the same shallow frontier and then discards both its discoveries and its crash reproducers, so a permanently red lane produces failures instead of bug reports; the 30-60 s budgets are below every documented floor while still occupying a 15-minute job slot.

**Candidate recommendation.** In `ci.yml`'s `fuzz` job: wrap `build/tests/fuzz/corpus` in per-target `actions/cache` steps and stop overwriting it with `generate_fuzz_corpus` on warm starts; add `-artifact_prefix=artifacts/` to every invocation plus an `actions/upload-artifact` step with `if: failure()`; convert the PR-tier step to seed/reproducer replay and raise the scheduled steps to 600 s+ per target; commit a seed corpus under `tests/fuzz/corpus/<target>/` (including the save-state heap-overflow reproducer) and a `.dict` per format passed via `-dict=`.

### 5. Determinism oracle: the lane's green certifies less than its name implies, and no lane is even dedicated to it

**Current.** Every determinism and save/load roundtrip test asserts on `dosbox_lib_get_state_hash` in Fast mode, which omits GPRs, EIP, EFLAGS, segment registers, guest RAM, and VRAM — Full mode now hashes conventional memory but has no callers in production or tests, and VGA/device coverage is deferred (H7 still open) ^[from [[Determinism Oracle Weakness]]]. No CMake preset, workflow job, or `ci.yml` step selects `-L determinism`; the suite executes only as undifferentiated ctest content inside the build jobs, so no per-lane pass/fail signal exists ^[from [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]] (`engine/tests/determinism/CMakeLists.txt:33-45`, `.github/workflows/ci.yml:77, 127, 207`).

**Practice.** A gate that has never been observed to fail is untested code — verify that checks can fail before trusting them ^[from [[Coverage Policy Ratcheting (2026-06)]]]. A lane that cannot detect what it is named for is spend without signal; the honest options are to fund it to where it verifies something or to stop presenting it as verification — the MSan analysis applies verbatim ^[from [[Sanitizer Lane Strategy (2026-06)]]]. Explicit lanes with declared cells make coverage holes visible as missing cells; cross-cutting invariant suites like determinism must stay in every tier, outside any selection scheme ^[from [[CI Design for C++-CMake Monorepos (2026-06)]]] ^[from [[Test Impact Analysis & Selection (2026-06)]]].

**Gap.** The product's central claim is policed by an instrument blind to most violations of it, and that instrument's results are not even separable in CI — a determinism regression and an unrelated unit failure produce the identical signal.

**Candidate recommendation.** Switch the determinism harness (`engine/tests/determinism/determinism_harness.h:37-38, 93-96`) and the riding tests (`tests/integration/test_workflow_determinism.cpp`, `test_determinism_hash.cpp`, `test_replay_determinism.cpp`, `tests/unit/test_determinism_at_scale.cpp`) to `HashMode::Full`; extend Full mode to the VGA/device state the header contract promises (closing H7/REQ-DT-004); and add a dedicated `determinism` job to `ci.yml` running `ctest -L '^determinism$'` on the PR tier so the lane has its own red/green, with a deliberately-divergent canary test proving the oracle can fail.

### 6. Fixture debt: green-reporting stubs, a residual monolith, a placeholder engine suite, and three COM programs carrying the whole emulator

**Current.** A quarter of registered integration test files are skip stubs that report green (8 of 33) ^[from [[Project Legends Test Suite]]]. The 2026-03-20 fixture plan's eight deliverables all exist, but the residual `test_legends_embed.cpp` monolith still compiles alongside its five split successors; engine integration tests remain a commented-out placeholder (`engine/tests/CMakeLists.txt:121-136`); the shared fixtures are include-path header conventions, not CTest fixtures; and the entire determinism/CPU-execution surface rests on three hand-assembled COM programs in `tests/fixtures/` ^[from [[Project Legends Test Suite]]].

**Practice.** A test that runs and reports green while verifying nothing is the assertion-relaxation antipattern — quarantine without a ticket or an exit; the visible alternatives are `DISABLED_` prefixes or a `flaky`/`stub` label excluded from gating lanes but run and counted on a schedule ^[from [[Flaky-Test Detection & Quarantine (2026-06)]]]. CTest's `FIXTURES_REQUIRED` machinery keeps subset runs coherent automatically, and is a reason to select via `ctest -L` rather than raw `--gtest_filter` ^[from [[Test Impact Analysis & Selection (2026-06)]]]. Input-fixture quality has a dominant effect on what dynamic testing can reach — the ideal set is minimal inputs with maximal coverage ^[from [[Continuous Fuzzing in CI (2026-06)]]].

**Gap.** The suite's headline counts include tests that verify nothing (stubs) and fixtures that exercise a sliver of the surface the oracles claim to check; because the stubs report green rather than skipped-with-a-marker, no metric distinguishes covered from hollow.

**Candidate recommendation.** Convert the 8 skip-stub integration files to `GTEST_SKIP()` with a tracked-issue comment or a `stub` CTest label excluded from `test-integration` (`CMakeLists.txt:1030-1034`) and counted in CI output; delete `test_legends_embed.cpp` once its split successors' coverage is confirmed; replace the commented-out placeholder at `engine/tests/CMakeLists.txt:121-136` with a real engine integration target; register cross-test setup (IPC engine-host startup) as `FIXTURES_REQUIRED`; and grow `tests/fixtures/` beyond the three COM programs toward the interrupt/VGA/device behaviors the Full-mode hash (finding 5) will start observing.

### 7. Orphaned tests: sources on disk that no runner will ever execute

**Current.** Three integration sources are compiled into no target at all — `tests/integration/test_context_synchronization.cpp`, `test_dual_ffi.cpp`, and `test_error_propagation.cpp` appear in no CMakeLists (the `legends_integration_tests` source list at `CMakeLists.txt:944-984` omits them) ^[from [[Project Legends Test Suite]]]. `tests/scripts/test_verify_gpl_isolation.py` — the test for `scripts/verify_gpl_isolation.py` — is referenced by no CMakeLists, workflow, or cmake module ^[from [[Project Legends Test Suite]]]; nothing in any workflow executes it ^[from [[CI Workflows (GitHub Actions)]]].

**Practice.** Newly added tests must enter the executed set automatically — selection systems treat "include new tests" as a non-negotiable guardrail, which presupposes that adding a test file adds an executed test ^[from [[Test Impact Analysis & Selection (2026-06)]]]. The GPL-isolation case compounds an already-documented orphan: the subject script's CMake wrapper is itself never included in the build, and the prescribed fix is to wire it in fail-closed and run it in the `linux-ipc` job ^[from [[Vendored & License-Isolated Dependency CI (2026-06)]]].

**Gap.** Test code exists, reviews as coverage, and contributes nothing: the three integration sources test synchronization, FFI, and error-propagation paths that currently have zero executable representation, and the license-firewall verifier is unverified by its own orphaned test.

**Candidate recommendation.** Add the three orphaned sources to the `legends_integration_tests` source list at `CMakeLists.txt:944-984` (or delete them if superseded, with the removal recorded); register `tests/scripts/test_verify_gpl_isolation.py` as a step in the `linux-ipc` job of `ci.yml` (or a pytest step in `sprint2-checks.yml`'s `globals-registry` job) alongside the wiring-in of `cmake/VerifyGPLIsolation.cmake` itself; and add a CI consistency check that fails when a `tests/**/*.cpp` file appears in no CMake source list.

### 8. The phantom `soak` label: selection logic for a set that is provably empty

**Current.** The `soak` label is referenced but never applied: `CMakeLists.txt:1021-1028` defers label application to `cmake/SoakTestLabels.cmake` "(if present)" and no such file exists, so `ctest -L soak` (the `test-soak` target, `CMakeLists.txt:1037-1041`, 13 h timeout) selects zero tests, every `--label-exclude soak` (`CMakeLists.txt:1031, 1045`; `.github/workflows/ci.yml:905`) excludes nothing, and the soak endurance tests in `tests/integration/test_soak_endurance.cpp` run under the ordinary `integration` label with TIMEOUT 60 ^[from [[Project Legends Test Suite]]]. The promised soak suite therefore cannot run on any tier ^[from [[Project Legends Test Suite]]].

**Practice.** CTest label selection is only as real as label application — a test with no labels is never included by `-L`, and label regexes should be anchored against substring over-matching ^[from [[Test Impact Analysis & Selection (2026-06)]]]. Long-running content belongs on the nightly tier as an explicitly declared cell, not interleaved into PR-tier suites where its timeout is silently wrong ^[from [[CI Design for C++-CMake Monorepos (2026-06)]]].

**Gap.** Every consumer of the label behaves vacuously in both directions: the soak selector runs nothing, the soak excluders exclude nothing, and the endurance tests themselves run on the PR tier under a 60-second timeout that contradicts their purpose.

**Candidate recommendation.** Create `cmake/SoakTestLabels.cmake` (or apply `LABELS "soak"` plus a long TIMEOUT directly via discovery-time `PROPERTIES` on the `test_soak_endurance.cpp` tests in the `gtest_discover_tests` call at `CMakeLists.txt:1014-1019`); verify `ctest -L '^soak$'` selects a nonzero set and `--label-exclude soak` shrinks `test-integration`; and add a nightly-tier step to `ci.yml` that runs the `test-soak` target, making the header comment's nightly soak tier (`ci.yml:8-12`) true for the first time.

## Candidate recommendations

| Id | Summary | Affected gates |
|---|---|---|
| T-1 | Add module-level CTest labels and make `ci.yml` tiers select by label instead of running undifferentiated ctest | `ci.yml` `linux`/`windows`/`coverage` ctest steps; `CMakeLists.txt` + `engine/tests/CMakeLists.txt` test registration |
| T-2 | Drive test selection from a changed-path → `LEGENDS_DAG_*` reverse-closure script with safe fallback; split `legends_unit_tests` per module | `ci.yml` `linux` job; new `scripts/select_tests.py`; `CMakeLists.txt:629-840` |
| T-3 | Exclude `engine/` from the lcov denominator, gate PRs on diff coverage, add a committed ratchet floor, rehearse `release-validation` | `ci.yml` `coverage` and `release-validation` jobs |
| T-4 | Persist the fuzz corpus across runs, upload crash artifacts, convert PR step to replay, fund scheduled fuzzing to 600 s+ per target, commit seeds + dictionaries | `ci.yml` `fuzz` job; `tests/fuzz/corpus/` (new); `tests/fuzz/CMakeLists.txt` |
| T-5 | Move the determinism oracle to `HashMode::Full` (extended to VGA/devices), give determinism its own PR-tier CI job with a canary that proves the oracle can fail | new `determinism` job in `ci.yml`; `engine/tests/determinism/determinism_harness.h`; determinism tests in `tests/` |
| T-6 | Make skip stubs visible (GTEST_SKIP/`stub` label), retire the embed monolith, build the engine integration target, adopt `FIXTURES_REQUIRED`, grow the COM fixture set | `legends_integration_tests` / `test-integration`; `engine/tests/CMakeLists.txt`; `tests/fixtures/` |
| T-7 | Compile the three orphaned integration sources into a target, give `test_verify_gpl_isolation.py` a runner, add an unreferenced-test-file check | `CMakeLists.txt:944-984`; `ci.yml` `linux-ipc` job or `sprint2-checks.yml` `globals-registry` |
| T-8 | Apply the `soak` label for real (via `cmake/SoakTestLabels.cmake` or discovery-time properties) and run `test-soak` on the nightly tier | `test-soak` / `test-integration` targets; `ci.yml` nightly tier; `CMakeLists.txt:1014-1045` |

## Related

- [[Project Legends Test Suite]] — the instrument under analysis
- [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]] — per-lane enforcement status these findings extend
- [[CI Gate Coverage Map]] — which jobs gate what, on which tier
- [[Determinism Oracle Weakness]] — the concept behind finding 5
- [[Quality Gate Demotion (2026-06-08)]] — the event that makes tiering and gating reform urgent rather than cosmetic
- [[Sprint Plan Derivation (2026-06)]] — where sequencing of these candidates belongs
