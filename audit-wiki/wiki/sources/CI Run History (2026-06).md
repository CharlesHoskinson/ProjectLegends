---
type: source
aliases: ["CI Run History", "Actions Run History 2026-06"]
tags: [source, type/source, topic/ci, topic/empirics]
created: 2026-06-10
updated: 2026-06-10
status: draft
title: CI Run History (2026-06)
authors: [GitHub Actions API extract]
url: https://github.com/CharlesHoskinson/ProjectLegends/actions
publisher: GitHub
published: 2026
accessed: 2026-06-10
source_type: dataset
covers:
  - "[[Build & CI System (Project Legends)]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
---

# CI Run History (2026-06)

## Summary

Observational run data for all 397 retained GitHub Actions runs of Project Legends, spanning 2026-01-16T10:07:58Z to 2026-06-10T08:31:29Z (`raw/ci-run-history-2026-06.json`, `window`). Aggregate figures come from that file; per-run figures (example run ids, the since-2026-05-10 trend, the branch split) are computed from the per-run records of the same API pull and anchored below to concrete run URLs. Headline: across the full window 308 of 397 runs concluded failure (77.6%), 50 success, 39 cancelled; the primary `CI` workflow concluded success in only 6 of 164 runs, and all 6 successes occurred on 2026-06-08/09 — immediately after the [[Quality Gate Demotion (2026-06-08)]]. The since-2026-05-10 slice shows the overall failure share falling to 49 of 80 runs (61.3%), driven by `Module DAG` and `Sprint 2 Checks` turning mostly green, not by the `CI` workflow, whose failure rate is unchanged.

## Window

- 397 runs retained; oldest started 2026-01-16T10:07:58Z, newest 2026-06-10T08:31:29Z (`raw/ci-run-history-2026-06.json`, `window`).
- Run records carry only the latest attempt per run (see Rerun signal below).

## Pass/fail/cancelled mix per workflow (full window)

All counts from `raw/ci-run-history-2026-06.json`, `conclusions_by_workflow`.

| Workflow | success | failure | cancelled | total | failure share |
|---|---:|---:|---:|---:|---:|
| CI | 6 | 143 | 15 | 164 | 87.2% |
| Sprint 2 Checks | 27 | 86 | 13 | 126 | 68.3% |
| PAL CI | 0 | 43 | 5 | 48 | 89.6% |
| Module DAG | 11 | 32 | 6 | 49 | 65.3% |
| Optional PAL CI | 6 | 4 | 0 | 10 | 40.0% |
| **All** | **50** | **308** | **39** | **397** | **77.6%** |

Stated factually:

- The `CI` workflow concluded success in 6 of 164 runs. Example failures: [27261935629](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27261935629), [27261725107](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27261725107). Most recent success: [27177241772](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27177241772) (2026-06-09, master). All 6 successes started between 2026-06-08T22:48Z and 2026-06-09T01:07Z.
- `PAL CI` never concluded success in the retained window — 0 of 48 runs. Example failures: [27162454617](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27162454617), [27161057479](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27161057479). There is no successful run URL to cite.
- `Optional PAL CI` (10 runs, all since 2026-05-10) succeeded 6 of 10. Example failures: [27175545834](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27175545834), [27175062487](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27175062487). Most recent success: [27261956965](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27261956965) (2026-06-10, master).
- `Module DAG` succeeded 11 of 49. Example failures: [27162454615](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27162454615), [27161057469](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27161057469). Most recent success: [27263669750](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27263669750) (2026-06-10, master — the newest retained run).
- `Sprint 2 Checks` succeeded 27 of 126. Example failures: [27161057388](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27161057388), [24415529319](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/24415529319). Most recent success: [27261935624](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27261935624) (2026-06-10, master).

## Recent trend (runs started since 2026-05-10)

Computed from the per-run records behind `raw/ci-run-history-2026-06.json`; 80 runs, every one on `master`.

| Workflow | success | failure | total | failure share (recent) | failure share (full window) |
|---|---:|---:|---:|---:|---:|
| CI | 6 | 40 | 46 | 87.0% | 87.2% |
| Module DAG | 9 | 2 | 11 | 18.2% | 65.3% |
| Optional PAL CI | 6 | 4 | 10 | 40.0% | 40.0% |
| PAL CI | 0 | 2 | 2 | 100% | 89.6% |
| Sprint 2 Checks | 10 | 1 | 11 | 9.1% | 68.3% |
| **All** | **31** | **49** | **80** | **61.3%** | **77.6%** |

The overall failure rate is improving — 61.3% recent versus 77.6% over the full window — but the improvement is concentrated in `Module DAG` and `Sprint 2 Checks`. The `CI` workflow's failure rate is stable at ~87% in both slices; its only successes in the entire retained history fall inside this recent window, on 2026-06-08/09, the days following the [[Quality Gate Demotion (2026-06-08)]]. `PAL CI` has effectively stopped running (2 recent runs, both failures) while `Optional PAL CI` appears only in this window (10 runs).

## Rerun signal

`rerun_runs` is empty in the aggregate (`raw/ci-run-history-2026-06.json`). The per-run records confirm: no run among the 397 has `run_attempt > 1`. Caveat: the GitHub API returns only the latest attempt of each run, so earlier attempts that were re-run are invisible in this extract; the absence of `run_attempt > 1` records means no run's *latest* state is a rerun, not that nobody ever pressed re-run.

## Job-level (30 most recent runs)

All figures from `raw/ci-run-history-2026-06.json`, `job_seconds` (per-job duration/failure stats over the 30 most recent runs; `n` = sampled executions).

**Slowest jobs by median duration:**

| Job | median (s) | max (s) | n |
|---|---:|---:|---:|
| Optional Windows Build | 1037 | 1084 | 7 |
| Windows (MSVC) | 960 | 1063 | 11 |
| Optional address Sanitizer | 680 | 680 | 1 |
| Optional thread Sanitizer | 679 | 679 | 1 |
| Optional undefined Sanitizer | 663 | 663 | 1 |
| thread Sanitizer | 643 | 662 | 6 |
| undefined Sanitizer | 639 | 647 | 6 |
| address Sanitizer | 628 | 653 | 6 |
| Code Coverage | 502 | 526 | 11 |
| Optional Linux SDL3 (clang) | 500 | 500 | 2 |
| Linux (clang) | 433 | 459 | 11 |
| Optional SDL3 Backend | 409 | 429 | 7 |

**Jobs with nonzero fail counts in the sample:**

- address, memory, thread, and undefined Sanitizer: each failed 6 of 6 sampled executions.
- Fuzz Testing: failed 6 of 6.
- Optional address / memory / thread / undefined Sanitizer: each failed 1 of 1.
- Optional Static Analysis (clang-tidy): failed 2 of 11; Optional Windows SDL3 (MSVC): failed 2 of 11.
- Optional Fuzz Testing: failed 1 of 5; Optional SDL3 Backend: failed 1 of 7; Windows (MSVC): failed 1 of 11.

Every sampled execution of the four mandatory sanitizer lanes and the fuzz lane failed.

**Serial compute estimate:** the sum of all job medians is 11,109 seconds ≈ 3 h 05 min of serial compute per full run cycle. This is an estimate over the 30-run sample, spans jobs from all workflows, and undercounts rarely-run lanes whose median is 0 (skipped in most sampled runs).

## Nightly/manual-only lanes in the job sample

The lanes demoted to schedule/dispatch by the [[Quality Gate Demotion (2026-06-08)]] do appear in the 30-run job sample, but almost all with median 0 — i.e. skipped in most sampled runs and executed rarely (all from `raw/ci-run-history-2026-06.json`, `job_seconds`):

- Optional Static Analysis (clang-tidy): n=11, median 0, max 34s — executed in a minority of runs; failed 2 of those.
- Optional TLA+ Model Checking: n=11, median 0, max 305s — executed at least once.
- Optional Dependency Scan: n=11, median 0, max 13s — executed at least once, briefly.
- Optional macOS (AppleClang) / Optional macOS SDL3 (AppleClang): n=11 each, median 0, max 413s / 548s — executed at least once each.
- Optional Linux SDL3 (`${{ matrix.compiler }}`): n=9, median 0, max 0 — never actually executed under the unexpanded matrix name; the expanded `(clang)` and `(gcc)` rows ran twice each (500s / 353s).
- Optional Windows SDL3 (MSVC): n=11, median 0, max 1120s — executed rarely; failed 2.
- Package (`${{ matrix.os }}`) and Release Validation: n=11 each, median 0, max 0 — never executed in the sample (consistent with the tag-gated release pipeline having never run; see [[Build & CI System (Project Legends)]]).

## Reading guidance

This is observational run data, not gate semantics — for what each workflow actually enforces and on which trigger tier, see [[CI Gate Coverage Map]] and [[Build & CI System (Project Legends)]]. `head_branch` matters when reading the failure counts: `master` dominates the dataset (322 of 397 runs) and the failures (265 of 308, 86.0%). The conclusion mix, computed from the per-run records:

| Branch | success | failure | cancelled | total | failure share |
|---|---:|---:|---:|---:|---:|
| master | 42 | 265 | 15 | 322 | 82.3% |
| all others | 8 | 43 | 24 | 75 | 57.3% |

The non-master runs are mostly the `ci/fix-ci-failures-2026-02-28` branch (68 of 75; 36 failures) plus `feature/beta-blockers` (5 runs, 5 failures, e.g. [24415529319](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/24415529319)). Every run since 2026-05-10 is on `master`, so the recent-trend table above is a pure master signal. Events split 233 push / 108 schedule / 56 pull_request across the window.

## Covers

- [[Build & CI System (Project Legends)]] — empirical run-level ground truth for the subsystem: 77.6% of all retained runs failed, the primary CI workflow passed 6 times in 164 runs (all on 2026-06-08/09), PAL CI never passed, the mandatory sanitizer and fuzz lanes failed every sampled execution, and the packaging/release-validation jobs never executed.
- [[Quality Gate Demotion (2026-06-08)]] — the demoted lanes (static analysis, TLA+, dependency scan, macOS/SDL3, sanitizers-as-Optional) appear in the 30-run job sample only with median 0 (rarely executed); the CI workflow's first and only successes started within hours of the demotion landing.
