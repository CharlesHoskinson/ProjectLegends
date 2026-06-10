---
type: source
aliases: ["CI Monorepo Best Practices Research"]
tags: [source, type/source, topic/research, topic/ci]
created: 2026-06-10
updated: 2026-06-10
status: draft
title: CI Design for C++/CMake Monorepos (2026-06)
authors: [LLVM Project, GitHub Docs, Kitware, Google ClusterFuzzLite, John Micco (Google)]
url:
publisher: multiple (see raw record)
published: 2016-2026
accessed: 2026-06-10
source_type: research
covers:
  - "[[Build & CI System (Project Legends)]]"
  - "[[CI Workflows (GitHub Actions)]]"
  - "[[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]]"
  - "[[Project Legends Test Suite]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Local Dev Loop]]"
---

# CI Design for C++/CMake Monorepos (2026-06)

## Summary

External best-practice research for redesigning the Project Legends CI: how mature C++ shops factor workflows, design OS matrices, filter by path without breaking required checks, and split mandatory from nightly tiers. Six authoritative sources: LLVM's official CI best-practices document, two GitHub official docs pages (required-check troubleshooting, reusable workflows), the cmake-presets(7) manual, Google's ClusterFuzzLite docs, and Google's flaky-tests engineering post. Raw extracts in `raw/research/cpp-cmake-monorepo-ci.md`.

## Practices

### 1. Presets as the single source of truth for CI job configuration

CMake presets exist precisely to share configure settings "to support CI builds"; `CMakePresets.json` is the checked-in project-wide file, `CMakeUserPresets.json` the uncommitted developer overlay. Hidden base presets plus `inherits` factor common flags; `condition` on `${hostSystemName}` gates OS-specific presets; test presets encode strictness (`outputOnFailure`, `noTestsAction: error`); workflow presets (schema v6) chain configure→build→test→package behind one `--preset` name. ^[from https://cmake.org/cmake/help/latest/manual/cmake-presets.7.html (retrieved 2026-06-10)]

**Applicability to Project Legends:** `CMakePresets.json` already defines the right lanes (`dev`, `release`, `asan`, `tsan`, `ipc`, `coverage`, `fuzz` configure/build/test presets with `inherits`), but no workflow uses them — every job in `.github/workflows/ci.yml`, `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` hand-rolls `cmake -B build` flag lists. Migrating jobs to `cmake --preset` / `ctest --preset` collapses the duplicated flag blocks, makes [[Local Dev Loop]] reproduce CI exactly, and turns the preset name into the natural matrix axis. Adding `workflowPresets` would let the never-exercised packaging lane run as one step.

### 2. Factor duplicated jobs into `workflow_call` reusable workflows, matrixed by preset

Reusable workflows live in `.github/workflows/` (subdirectories unsupported), declare `on: workflow_call` with typed inputs, and are called at job level via `uses: ./.github/workflows/<file>.yml` — the same-repo form pins the called workflow to the caller's commit. A `strategy: matrix` job can call a reusable workflow once per combination, passing matrix values as inputs. Limits: ten workflow levels, no loops, permissions only narrow down the chain, secrets pass only one hop unless `secrets: inherit`. ^[from https://docs.github.com/en/actions/how-tos/sharing-automations/reuse-workflows (retrieved 2026-06-10)]

**Applicability to Project Legends:** the four workflows in `.github/workflows/` repeat the same checkout→configure→build→test skeleton across Linux gcc/clang, Windows MSVC, sanitizers, IPC, and PAL variants. One `build-and-test.yml` reusable workflow taking `{os, preset, ctest-args}` inputs, called from a thin `ci.yml` with a matrix over preset names (practice 1), would replace most of `ci.yml`'s and `pal-ci.yml`'s body and end the drift between them that the Build & CI audit documented (engine rebuilt cold in every job, IPC tested on one OS only).

### 3. Never path-filter a required workflow; skip at job level instead

GitHub is explicit: "If a workflow is skipped due to path filtering, branch filtering or a commit message, then checks associated with that workflow will remain in a 'Pending' state. A pull request that requires those checks to be successful will be blocked from merging." The asymmetry is the design rule — a job skipped by an `if:` conditional reports Success and satisfies required checks; a workflow skipped by `paths:` reports nothing and blocks forever. For required jobs downstream of other jobs, combine `needs` with `always()`, since dependents of a failed job are silently skipped. Merge queues additionally require the `merge_group` trigger or the queued merge fails. ^[from https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/collaborating-on-repositories-with-code-quality-features/troubleshooting-required-status-checks (retrieved 2026-06-10)]

**Applicability to Project Legends:** `pal-ci.yml` (paths: `src/pal/**`) and `module-dag.yml` are workflow-level path-filtered, so none of their jobs can ever be made required as written — exactly the enforcement gap the audit graded D. The fix when consolidating into a single entry workflow (practice 2): trigger broadly, compute changed paths in a cheap first job, and gate expensive jobs with job-level `if:` on its outputs, so skipped jobs still report Success and branch protection can require them.

### 4. Trigger hygiene: unrestricted `pull_request`, restricted `push`, self-testing workflows

LLVM's rules: `pull_request` events should not contain a `branches` key (branch-restricting PR triggers silently exempts PRs into other branches); `push` events should be restricted to `main` and release branches to avoid double-running; every workflow should also trigger on `pull_request` paths matching its own definition file so workflow edits are tested in the PR that makes them. Also: hash-pin third-party actions to commit SHAs (release tags are mutable), use versioned runner images (`ubuntu-22.04`, never `-latest`), default `permissions: contents: read` at workflow top, and set `persist-credentials: false` on checkout. ^[from https://llvm.org/docs/CIBestPractices.html (retrieved 2026-06-10)]

**Applicability to Project Legends:** this directly resolves audit finding CI-04 — `ci.yml` and `pal-ci.yml` restrict `pull_request` to main/master while the documented flow routes feature PRs into develop, so they merge untested. Dropping the `branches` key from `pull_request` (and keeping it on `push`) is a two-line fix per workflow. The hardening items (SHA-pinned actions, versioned runners, top-level read permissions) apply to all four workflow files and matter more than usual here because the repo vendors a GPL engine whose isolation claims depend on CI integrity.

> [!conflict]
> LLVM says `pull_request` triggers "should not contain a branches key" ^[from https://llvm.org/docs/CIBestPractices.html (retrieved 2026-06-10)], while GitHub's own reusable-workflows documentation shows its example caller with `on: pull_request: branches: [main]` ^[from https://docs.github.com/en/actions/how-tos/sharing-automations/reuse-workflows (retrieved 2026-06-10)], and the required-checks page warns that branch filtering leaves required checks Pending ^[from https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/collaborating-on-repositories-with-code-quality-features/troubleshooting-required-status-checks (retrieved 2026-06-10)]. GitHub's docs treat branch-filtered PR triggers as normal; LLVM and GitHub's own troubleshooting page give reasons to avoid them. For this repo the LLVM position wins: CI-04 is a live instance of the failure mode.

### 5. Tier fuzzing: short coverage-guided PR fuzz, scheduled batch fuzz, shared corpus

ClusterFuzzLite's model for libFuzzer in CI: code-change fuzzing runs on PRs, defaults to 10 minutes, quits on first crash; batch fuzzing runs "on a schedule such as once daily", runs every target for a long budget, and builds the corpus that later PR runs reuse; corpus pruning is "mandatory when you are using batch fuzzing"; coverage reports generated from the batch corpus let PR fuzzing run only the fuzzers a change affects; a continuous-builds baseline lets PR fuzzing suppress pre-existing crashes so only regressions block. ^[from https://google.github.io/clusterfuzzlite/running-clusterfuzzlite/ (retrieved 2026-06-10)]

**Applicability to Project Legends:** `ci.yml` has the right shape dead in it — the "PR: Quick fuzz (30s per target)" step is unreachable because the job-level `if` excludes `pull_request` (audit CI-01). The model to restore: a short per-PR fuzz job (minutes, not 30s, per target on changed areas), a nightly scheduled batch job with a persisted corpus (actions/cache or artifacts), plus pruning. The fuzz preset in `CMakePresets.json` already builds the targets; the tiering, corpus persistence, and baseline-crash triage are what is missing.

### 6. Mandatory tier must be near-zero-flake; quarantine, don't mute

Google's two-tier gating: pre-submit gates code submission, post-submit gates release, and both demand all-green. At thousands-of-tests scale, ~1.5% of runs flake, ~16% of tests show some flakiness, and 84% of observed pass→fail transitions involve a flaky test — so an unreliable mandatory tier trains people to ignore it: "It is human nature to ignore alarms when there is a history of false signals." Mitigations: rerun-only-failed, automatic quarantine that removes a flaky test from the critical path *and files a bug*, and flakiness-level monitoring — with the stated hazard that quarantine "could easily mask a real race condition." ^[from https://testing.googleblog.com/2016/05/flaky-tests-at-google-and-how-we.html (retrieved 2026-06-10)]

**Applicability to Project Legends:** this is the principled version of what commit 6900e7a (see [[Quality Gate Demotion (2026-06-08)]]) did unprincipledly. Demoting whole lanes (sanitizers, fuzz, TLA+) to nightly because some engine tests race is muting, not quarantining: TSan has been `allow_failure: true` in `ci.yml` over known races since 2026-03-02 with no exit plan — the exact alarm-fatigue failure Google describes. The correct split: the mandatory tier runs everything that is reliably green (ASan/UBSan on the MIT-side code, IPC suite, unit suites) and individual flaky tests get GoogleTest filters/quarantine labels with tracked bugs; nightly runs the full matrix including the quarantined set, with results triaged, not ignored.

### 7. Matrix design: explicit axes, versioned images, preset-named cells

Composite of the above: the three-OS matrix should be a `strategy: matrix` over `{runner-image × preset}` cells calling one reusable workflow ^[from https://docs.github.com/en/actions/how-tos/sharing-automations/reuse-workflows (retrieved 2026-06-10)], with runner images explicitly versioned rather than `-latest` so image rolls are opt-in ^[from https://llvm.org/docs/CIBestPractices.html (retrieved 2026-06-10)], and each cell's entire build/test behavior named by a preset so the matrix definition contains no flags ^[from https://cmake.org/cmake/help/latest/manual/cmake-presets.7.html (retrieved 2026-06-10)].

**Applicability to Project Legends:** `ci.yml` currently encodes the OS matrix as separate hand-written jobs (linux-gcc, linux-clang, windows-msvc, macos) with diverging flag sets, which is how Windows IPC and the `dev` preset's clang/Ninja toolchain ended up never covered (audit BUILD-02, coverage gaps). A declared matrix makes the holes visible as missing cells; mandatory-vs-nightly tiering (practice 6) is then expressed as which cells run on `pull_request` versus `schedule`.

## Covers

- [[Build & CI System (Project Legends)]] — practices 1-7 are the external standard against which the audit's C grade was implicitly measured; presets-as-truth and reusable-workflow factoring address the four-workflow duplication directly.
- [[CI Workflows (GitHub Actions)]] — trigger hygiene, path-filter correctness, and matrix design prescribe the restructuring of `ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`.
- [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]] — ClusterFuzzLite's PR/batch split and Google's quarantine model define which lanes belong in the mandatory tier and how the rest stay observed rather than muted.
- [[Project Legends Test Suite]] — the flaky-test economics at thousands-of-tests scale govern what the suite must satisfy before it can be a required check.
- [[Quality Gate Demotion (2026-06-08)]] — practice 6 is the disciplined alternative to the wholesale nightly demotion of 6900e7a.
- [[Local Dev Loop]] — preset-driven CI is what makes local `cmake --preset` runs equal to CI runs.
