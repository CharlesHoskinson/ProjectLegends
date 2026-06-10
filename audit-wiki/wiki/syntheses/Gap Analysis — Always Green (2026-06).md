---
type: synthesis
aliases: ["Always Green gap analysis", "Always-Green gaps"]
tags: [synthesis, type/synthesis, topic/audit, topic/ci, topic/dev-loop]
created: 2026-06-10
updated: 2026-06-10
status: draft
question: What separates Project Legends from an always-green master, and what concrete changes would close each gap?
sources:
  - "[[CI Run History (2026-06)]]"
  - "[[Local Preflight Design (2026-06)]]"
  - "[[Merge Queues & Required Checks (2026-06)]]"
  - "[[CI Design for C++-CMake Monorepos (2026-06)]]"
  - "[[Sanitizer Lane Strategy (2026-06)]]"
  - "[[Continuous Fuzzing in CI (2026-06)]]"
  - "[[Flaky-Test Detection & Quarantine (2026-06)]]"
  - "[[Coverage Policy Ratcheting (2026-06)]]"
  - "[[Compiler Caching on GitHub Actions (2026-06)]]"
  - "[[Test Impact Analysis & Selection (2026-06)]]"
  - "[[Sprint 0 Implementation Audit (2026-06-10)]]"
concepts:
  - "[[Quality Gate Demotion (2026-06-08)]]"
related:
  - "[[Local Dev Loop]]"
  - "[[CI Workflows (GitHub Actions)]]"
  - "[[Quality Gate Scripts & Hooks]]"
  - "[[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]"
  - "[[CI Gate Coverage Map]]"
confidence: moderate
---

# Gap Analysis — Always Green (2026-06)

Gap analysis for the **Always Green** objective: master should never advance to a failing commit, and a developer should be able to predict CI's verdict before pushing. Each finding pairs the repository's current state (entity/map pages, repo paths) with external practice (research source pages), states the gap, and proposes a candidate recommendation. Candidate recommendations are inputs to [[Sprint Plan Derivation (2026-06)]]-style prioritization; this page does not rank them.

The empirical baseline that frames everything below: 82.3% of retained Actions runs on `master` concluded failure across the 2026-01-16 → 2026-06-10 window (265 of 322), the primary `CI` workflow passed 6 of 164 runs, and all 6 successes started within hours of the [[Quality Gate Demotion (2026-06-08)]] — green was achieved by muting gates, not by fixing failures ([[CI Run History (2026-06)]]).

## Findings

### 1. Green came from demotion, not repair

**Current** — Commit 6900e7a (2026-06-08) moved sanitizers, fuzz, TLA+, and static analysis off the PR/merge tier to get a red pipeline green ([[Quality Gate Demotion (2026-06-08)]], `.github/workflows/ci.yml`). The `CI` workflow's only successes in five months of retained history started within hours of that commit; the demoted lanes appear in the recent job sample with median duration 0 — rarely executed at all ([[CI Run History (2026-06)]]). Sprint 0 re-armed ASan/UBSan and the fuzz smoke on PR and push-to-master ([[Quality Gate Demotion (2026-06-08)]], resolved callout; [[Sprint 0 Implementation Audit (2026-06-10)]]), but the underlying lanes still fail when they run ([[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]).

**Practice** — Demoting a whole lane because some of its tests fail is muting, not quarantining: the mandatory tier should run everything reliably green, and individual failing tests get quarantined with tracked bugs while a scheduled lane keeps running them ([[CI Design for C++-CMake Monorepos (2026-06)]], practice 6). Gate-level relaxation is the macro form of the assertion-relaxation antipattern ([[Flaky-Test Detection & Quarantine (2026-06)]], practice 6). Heavyweight lanes may leave the blocking set only with a schedule plus an exit plan ([[Merge Queues & Required Checks (2026-06)]], P4).

**Gap** — The repository's only path to green so far has been removing the instruments; re-arming the gates (Sprint 0) restores the signal but the signal is red again unless the lanes are fixed test-by-test rather than tier-by-tier.

**Candidate recommendation** — Triage the re-armed `sanitizers` and `fuzz` jobs in `.github/workflows/ci.yml` failure-by-failure: quarantine individual failing tests (G-9 mechanism) and suppress known races (G-7 mechanism) until each lane is deterministically green, and record in the workflow file which lane is gating versus scheduled and why. Do not demote a lane again without a dated exit criterion in a tracked issue.

### 2. Nothing binds CI's verdict to merges

**Current** — No branch protection or ruleset is in effect: 233 of 397 retained runs are `push` events, i.e. commits landing on `master` with no pre-merge gate, and master ran 82.3% red across the window ([[CI Run History (2026-06)]]). The workflows already trigger on `pull_request` (`.github/workflows/ci.yml`; [[CI Workflows (GitHub Actions)]]) — they just gate nothing. The coverage map's "mandatory tier" is a trigger-tier derivation, not an enforcement statement ([[CI Gate Coverage Map]]).

**Practice** — The not-rocket-science rule: automatically maintain a repository that always passes its tests; master never advances to a failing commit ([[Merge Queues & Required Checks (2026-06)]], P1). Enforcement belongs in an Active ruleset targeting exactly `master`: require a PR, require a small exact-name check set, require branches up to date, block force pushes (P3, P4, P10). Protection is the last step of a green-up, not the first (P2): switching required checks on over the current 87%-failing job set would freeze the repository.

**Gap** — The repo has CI as an observer, not a gate; every red run documents a breakage it had no power to prevent. Sequencing matters: required checks bind only after the candidate set is reliably green.

**Candidate recommendation** — After the G-1 green-up, create a repository ruleset on `master` (repo settings, not workflow files): require pull requests, require status checks `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification` (expanded job names from `.github/workflows/ci.yml`), require branches up to date before merging, block force pushes. Grant admin bypass but treat each bypass as an incident visible in the ruleset audit log.

### 3. Most workflows are structurally ineligible to be required checks

**Current** — `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` are workflow-level path-filtered, so on PRs not touching their paths they report nothing (`.github/workflows/pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`; [[CI Gate Coverage Map]], trigger tiers). The run history also shows a matrix job recorded under its unexpanded template name (`Optional Linux SDL3 (${{ matrix.compiler }})`) that never executed ([[CI Run History (2026-06)]]).

**Practice** — A workflow skipped by `paths:` leaves its checks Pending forever and blocks any PR that requires them; the design rule is to trigger broadly and skip at job level with `if:`, because a job-level skip reports Success ([[CI Design for C++-CMake Monorepos (2026-06)]], practice 3). Required checks match on the expanded job name; a check registered under a name that never reports blocks every merge ([[Merge Queues & Required Checks (2026-06)]], P4).

**Gap** — The script gates (ten Python steps), the include-rules gate, and all PAL jobs cannot join the required set as written; making them required would deadlock unrelated PRs, and leaving them out means the gates that exist today still can't bind.

**Candidate recommendation** — Restructure `sprint2-checks.yml` and `module-dag.yml` (and, when consolidating, `pal-ci.yml`) to trigger without `paths:` filters, compute changed paths in a cheap first job, and gate the expensive jobs with job-level `if:` on its outputs, so skipped jobs report Success and become requirable. Register required checks only under expanded matrix names.

### 4. Merge-queue readiness is zero, and a queue is not yet the right tool

**Current** — No workflow declares a `merge_group` trigger ([[CI Workflows (GitHub Actions)]], `.github/workflows/*.yml`), and the job-level `if:` conditions in `ci.yml` enumerate `pull_request`/`push`/`schedule`/`workflow_dispatch` (`ci.yml:333-337, 482-487`), which would silently skip on a `merge_group` event. No workflow uses a compiler cache; every job compiles the vendored engine cold ([[CI Workflows (GitHub Actions)]], caching notes). PR volume is low: 56 `pull_request` events in five months ([[CI Run History (2026-06)]]).

**Practice** — Every workflow producing a required check must trigger on `merge_group`, or queued merges fail on never-reporting checks ([[Merge Queues & Required Checks (2026-06)]], P5). At low PR volume the full invariant is achievable without a queue: ruleset + required checks + require-branches-up-to-date forces revalidation against current master before every merge (P10). Each queue speculation re-runs the required lanes, so compiler caching is a prerequisite for queue affordability (P6; [[Compiler Caching on GitHub Actions (2026-06)]]).

**Gap** — Adopting a queue today would deadlock on missing `merge_group` triggers and job-level event whitelists, while the up-to-date requirement delivers the same guarantee at this PR volume with zero new plumbing.

**Candidate recommendation** — Defer the merge queue; include "require branches to be up to date" in the G-2 ruleset instead. If concurrent-PR contention later materializes, first add `merge_group:` to the `on:` block of `.github/workflows/ci.yml` and audit every job-level `if:` event whitelist in `ci.yml` for `merge_group`, and land compiler caching (G-11) beforehand.

### 5. Developers can see three of fourteen mandatory gates before pushing

**Current** — The documented local loop (configure + build + `ctest`, `README.md:146-150`, `CONTRIBUTING.md:43-49`) covers compile, unit, and integration tests in one configuration of the CI matrix; installing the opt-in hook adds exactly one more gate (include rules). Every other mandatory-tier gate — the nine sprint2 check-script gates, the ABI check, sanitizers, fuzz, the IPC/MSVC/coverage configurations — runs for the first time after push ([[Local Dev Loop]], gate table). No single command reproduces the mandatory tier ([[Local Dev Loop]], replication section).

**Practice** — Local-first CI: design checks to run on the developer's machine first, then run the same checks remotely; CI must invoke the same entry point developers invoke, or developers learn to ignore the local path ([[Local Preflight Design (2026-06)]], practice 1). The preflight contract is "every gate that can run on this OS," with the residue left to remote CI by design (practice 2, scope note).

**Gap** — A developer cannot predict CI's verdict locally, so red-after-push is the structural norm; the gate logic lives only in workflow YAML where nothing local can call it.

**Candidate recommendation** — Add `scripts/preflight.py` that runs the eleven `scripts/check_*.py` gates, the C11 ABI compile, and the OS-reachable build/test configurations; rewrite the step lists in `.github/workflows/sprint2-checks.yml` and the `abi-check` job in `ci.yml` to invoke the same script (or its sub-commands), so the YAML degrades into a thin trigger wrapper and local/CI divergence becomes structurally impossible. Document the command in `CONTRIBUTING.md`.

### 6. The repo ships presets that nothing uses — and its only build script diverges from CI

**Current** — `CMakePresets.json` declares configure/build/test presets for every lane (`dev`, `release`, `asan`, `tsan`, `ipc`, `coverage`, `fuzz`) but no `workflowPresets`, and CI bypasses presets entirely with raw `-D` flags (`ci.yml:64-71`, `sprint2-checks.yml:99-105`, `module-dag.yml:104-109`, `pal-ci.yml:39-45`; [[Local Dev Loop]]). The only build script in the tree, `llm-wiki/_scratch/build.cmd`, disables `LEGENDS_WERROR`, which CI never does ([[Local Dev Loop]]).

**Practice** — Presets exist precisely to share configuration with CI; workflow presets (schema v6, already the file's version) chain configure→build→test behind one name, and CI must switch to `cmake --workflow --preset` so the preset is the shared definition rather than a third copy of the flags ([[Local Preflight Design (2026-06)]], practice 2; [[CI Design for C++-CMake Monorepos (2026-06)]], practices 1 and 7). The `WERROR=OFF` deviation is the canonical local-passes/remote-fails violation ([[Local Preflight Design (2026-06)]], practice 4 conflict note).

**Gap** — Three copies of the build configuration exist (presets, workflow flags, scratch script) and the one developers actually run is the most permissive, so local green systematically overpredicts CI green.

**Candidate recommendation** — Add a `workflowPresets` array to `CMakePresets.json` (one per mandatory-tier configuration: `preflight-dev`, `preflight-ipc`, `release`), migrate the configure steps in `.github/workflows/ci.yml`, `sprint2-checks.yml`, `module-dag.yml`, and `pal-ci.yml` to `cmake --workflow --preset`, and delete or align `llm-wiki/_scratch/build.cmd` so no tracked or scratch entry point builds with flags CI doesn't use.

### 7. Allow-failure lanes are muted indefinitely, with the exit plan in a YAML comment

**Current** — TSan and MSan carry `allow_failure: true` (`ci.yml:332, 357-373`); TSan has been advisory over known named races since 2026-03-02, MSan crashes on startup by construction (stock libc++) and verifies nothing; the exit plans live in in-file comments deferring to Sprint 7 ([[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]). All four sanitizer lanes — including the nominally enforced ASan/UBSan — failed every sampled execution ([[CI Run History (2026-06)]]). The dependency-scan step is double-muted with `continue-on-error: true` and `|| true` (`ci.yml:784-787`; [[CI Workflows (GitHub Actions)]]).

**Practice** — The only sanctioned run-but-don't-gate mode is explicitly temporary with a filing destination: failures convert into filed bugs, narrow issue-linked suppressions, and a green *enforced* lane that catches regressions — never a red lane humans stop reading ([[Sanitizer Lane Strategy (2026-06)]], practice 2). For TSan on legacy globals, suppress-to-green beats defer-to-red: `race:<global>` entries in a checked-in suppression file, then drop `allow_failure` so the lane gates on new races immediately (practice 3). MSan is instrumented-libc++ or nothing, and nothing is the defensible default (practice 4).

**Gap** — Allow-failure here means ignore-forever: no artifact distinguishes "same known races" from "new race introduced by this PR," so the lanes burn runners while regressions land silently.

**Candidate recommendation** — Check a `tsan-suppressions.txt` into the repo (one issue-linked entry per known race, wired via `TSAN_OPTIONS` in `.github/workflows/ci.yml` and in the `tsan` preset in `CMakePresets.json`, with `llvm-symbolizer` added to the job's installed packages), then remove `allow_failure: true` from the `thread` matrix leg. Retire the `memory` leg from `ci.yml` until an MSan-instrumented libc++ exists. Remove the `|| true` from the dependency-scan invocations so its conclusion at least reports truthfully.

### 8. The fuzz lane produces red checkmarks instead of bug reports

**Current** — The `fuzz` job regenerates its seed corpus from scratch every run, persists nothing (`ci.yml:511-512`, no cache/artifact step; [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]), uploads no crash artifacts, and failed every sampled execution ([[CI Run History (2026-06)]]). There is no baseline separating pre-existing crashes from new ones, so any PR can draw a red X from someone else's bug ([[Continuous Fuzzing in CI (2026-06)]], current-state summary; `.github/workflows/ci.yml:478-578`).

**Practice** — Split the lane: a deterministic PR step that replays seeds and known reproducers (libFuzzer file-list mode, ASan on) as the gating check, and a scheduled lane that owns real exploration at documented budgets with a persisted, pruned corpus; capture `crash-<sha1>` artifacts on every failure and recycle minimized reproducers into a committed seed corpus ([[Continuous Fuzzing in CI (2026-06)]], practices 1-4). Demotion-instead-of-triage is the anti-pattern the baseline concept prevents (practice 3).

**Gap** — A 6/6-red lane that discards its reproducers cannot be triaged and cannot gate; as built it can only be ignored or demoted — both of which happened.

**Candidate recommendation** — In `.github/workflows/ci.yml` `fuzz` job: add `-artifact_prefix` plus an `actions/upload-artifact` step with `if: failure()`; wrap the per-target corpus in `actions/cache`; commit a seed corpus under `tests/fuzz/corpus/<target>/` (the CMake copy hook in `tests/fuzz/CMakeLists.txt` already exists and is dead); convert the PR step to corpus+reproducer replay and move exploration budgets to the nightly cron.

### 9. No flake ledger, no quarantine mechanism — stabilization happened by deleting assertions

**Current** — The run-history extract carries no rerun signatures (latest attempts only), no quarantine mechanism exists in the suite, and the documented stabilization commits (911692f, 8fdd4c6) relaxed SDL backend assertions to `(void)` casts rather than quarantining — the tests now pass while verifying less ([[Flaky-Test Detection & Quarantine (2026-06)]], summary and practice 4; `tests/unit/test_pal_sdl2_backend.cpp`, `test_pal_sdl3_backend.cpp`). The only stability probe is `--gtest_repeat=3` in one pal-ci job (`pal-ci.yml:208-214`; [[CI Workflows (GitHub Actions)]]).

**Practice** — Quarantine means removing from the gate, not from existence, and never silently: `DISABLED_` rename or a `flaky` CTest label with a linked issue, a scheduled lane that keeps running quarantined tests, and exit by surviving `ctest --repeat until-fail:N` ([[Flaky-Test Detection & Quarantine (2026-06)]], practices 3-5). Detection without rerun history uses deterministic re-execution: a scheduled burn-in lane (`--repeat until-fail`, `--gtest_shuffle`) plus an ongoing `run_attempt` snapshotter (practices 1-2).

**Gap** — Without a quarantine convention, every flaky test forces a choice between living with red and weakening the test; the repo chose weakening, which is quarantine without a ticket or an exit.

**Candidate recommendation** — Restore the deleted SDL assertions in `tests/unit/test_pal_sdl2_backend.cpp` and `test_pal_sdl3_backend.cpp` and quarantine the restored tests (`DISABLED_` prefix or a `flaky` label excluded via `ctest -LE flaky` in the gating lanes of `.github/workflows/ci.yml`), each with a linked issue. Add a nightly burn-in step (`ctest --repeat until-fail:10` plus `--gtest_shuffle`) and a scheduled job that snapshots `run_attempt > 1` runs into the repo as the flake ledger.

### 10. The coverage gate is an apology in an artifact

**Current** — The per-PR `coverage` job is report-only — it writes "no minimum threshold is enforced by CI yet" into an artifact (`ci.yml:749`) — and the only numeric threshold (80% on `src/app/`) sits in tag-gated `release-validation`, which has never executed because the repo has no tags ([[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]; [[CI Gate Coverage Map]], tag-tier only). The lcov filter does not exclude the vendored `engine/` tree (`ci.yml:744-747`).

**Practice** — Gate PRs on diff coverage, not absolute coverage — achievable on every PR regardless of the legacy total — using diff-cover directly on the existing lcov artifact, token-free; exclude the vendored engine from the policy denominator first; stage informational-then-enforced; and note that an enforced step in a non-required job is still report-only in effect ([[Coverage Policy Ratcheting (2026-06)]], practices 1, 4, 5, 6).

**Gap** — Coverage runs on every PR yet asserts nothing anywhere a merge can feel it; the one real threshold guards a path that has never been exercised.

**Candidate recommendation** — In the `coverage` job of `.github/workflows/ci.yml`: add `'*/engine/*'` to the `lcov --remove` list, replace the policy echo with `diff-cover coverage.filtered.info --compare-branch=origin/master --fail-under=<target>` (informational for one cycle, then enforced), and add the `Code Coverage` job to the G-2 required set once enforced. Rehearse `release-validation` once via `workflow_dispatch` before the first real tag.

### 11. Every job compiles the engine cold, making the green loop slow everywhere

**Current** — No workflow uses ccache/sccache; the only caching anywhere is the SDL3 dependency directory, and the vendored DOSBox-X engine recompiles from zero in every job of every workflow ([[CI Workflows (GitHub Actions)]], caching notes; `.github/workflows/ci.yml:164-167`). The serial-compute estimate for a full cycle is about three hours, with the Windows lane at ~16 minutes median ([[CI Run History (2026-06)]]).

**Practice** — Add `-DCMAKE_C[XX]_COMPILER_LAUNCHER` to every compile job: ccache via `ccache-action` on the Ninja-based Linux jobs is mechanical; the MSVC jobs need `-G Ninja` plus sccache with the GHA backend; warm caches must be written by push runs on `master`/`develop` so PRs inherit them; engine TUs should hit at a very high rate since typical PRs don't touch `engine/` ([[Compiler Caching on GitHub Actions (2026-06)]], practices 1, 2, 4, 7).

**Gap** — Slow cold builds raise the price of every always-green mechanism — preflight runs, required checks, up-to-date revalidation, burn-in lanes, any future queue speculation — and the dominant compute is recompiling code no PR changed.

**Candidate recommendation** — Add compiler-launcher flags to the `linux`, `linux-ipc`, `linux-sdl3`, `sanitizers`, `fuzz`, and `coverage` configure steps in `.github/workflows/ci.yml` with per-configuration ccache keys and size caps; convert the `windows` job to `-G Ninja` + sccache (`SCCACHE_GHA_ENABLED`). Keep the existing `sdl3-*` source caches as-is.

### 12. Hook installation is undocumented, single-check, and unverified

**Current** — `.githooks/pre-commit` runs exactly one of the eleven check scripts, is opt-in via `git config core.hooksPath .githooks`, and that instruction exists only as a comment inside the hook itself; `README.md` and `CONTRIBUTING.md` mention no hook, no `scripts/check_*.py`, and no setup step ([[Quality Gate Scripts & Hooks]], pre-commit hook section; [[Local Dev Loop]]).

**Practice** — Commit the hook config, make installation one documented command, and verify installation rather than trusting it; CI runs the identical hook config so opting out only moves the failure later, never around it; a managed hook tool (pre-commit `repo: local` or lefthook) turns all eleven scripts into named, glob-filtered, tiered entries with an explicit Windows story ([[Local Preflight Design (2026-06)]], practices 3-6).

**Gap** — The one mechanism meant to catch gate failures before push is invisible to new contributors and covers a single check of eleven even when installed.

**Candidate recommendation** — Adopt a committed hook config (lefthook.yml or `.pre-commit-config.yaml`) covering the eleven `scripts/check_*.py` in tiers (fast staged-file checks at commit, script gates + one workflow preset at push); replace `.githooks/pre-commit` with the manager shim; add a Setup section to `CONTRIBUTING.md` (clone → bootstrap → hook install → preflight); have the G-5 preflight script warn when hooks are not installed; run the identical hook config as a CI step in `sprint2-checks.yml`.

## Candidate recommendations

| Id | Summary | Affected gates |
|---|---|---|
| G-1 | Triage re-armed sanitizer/fuzz lanes to deterministic green via per-test quarantine and per-race suppression; no lane demotion without a tracked exit criterion | sanitizers, fuzz |
| G-2 | Ruleset on `master`: require PR, required checks (Linux gcc/clang, Linux IPC, Windows MSVC, C ABI), branches up to date, no force push | all mandatory-tier build/test gates |
| G-3 | Remove workflow-level `paths:` filters; compute changed paths in a first job and skip at job level so script/PAL/DAG gates become requirable | sprint2 script gates, include rules, cmake-dag, pal-ci jobs |
| G-4 | Defer merge queue; rely on require-up-to-date; pre-stage `merge_group` triggers and `if:` audits in `ci.yml` only if contention appears | all required checks |
| G-5 | `scripts/preflight.py` as the single entry point; rewire `sprint2-checks.yml` and the `abi-check` job to call it | all script gates, ABI check, build/test configurations |
| G-6 | Add `workflowPresets`; migrate all four workflows to `cmake --workflow --preset`; eliminate the `WERROR=OFF` scratch-script divergence | compile, unit/integration tests, sanitizer/IPC/coverage configurations |
| G-7 | Issue-linked `tsan-suppressions.txt`, then drop TSan `allow_failure`; retire the MSan leg; remove `\|\| true` from dependency-scan | TSan, MSan, dependency-scan |
| G-8 | Fuzz lane split: PR replay of committed seeds/reproducers, nightly funded exploration, cached corpus, crash-artifact upload | fuzz |
| G-9 | Quarantine convention (`DISABLED_`/`flaky` label + issue), restore relaxed SDL assertions, nightly burn-in, `run_attempt` flake ledger | unit/integration tests, PAL backend tests |
| G-10 | Diff-coverage gate on the existing lcov artifact; exclude `engine/` from the denominator; rehearse `release-validation` via dispatch | coverage, release-validation |
| G-11 | Compiler launchers (ccache/sccache) on every compile job; Ninja + sccache on Windows | all compile-bearing gates |
| G-12 | Committed, tiered, managed hook config covering all eleven check scripts; documented setup; CI runs the identical config | include rules, all script gates |

## Related

- [[Local Dev Loop]] — the local-vs-CI delta findings 5, 6, 12 close
- [[CI Workflows (GitHub Actions)]] — the four workflow files most recommendations modify
- [[Quality Gate Scripts & Hooks]] — the script and hook inventory behind findings 5 and 12
- [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]] — per-lane enforcement status behind findings 7, 8, 10
- [[CI Gate Coverage Map]] — mandatory-tier derivation underlying findings 2 and 3
- [[Quality Gate Demotion (2026-06-08)]] — the event finding 1 generalizes
- [[Sprint Plan Derivation (2026-06)]] — where these candidates get prioritized
