# Raw research record — CI Design for C++/CMake Monorepos

Topic: job/workflow factoring, reusable workflows, matrix design, path-filter correctness, tiering mandatory vs nightly for a C++23/CMake monorepo with vendored GPL engine, three-OS matrix, GoogleTest at scale, libFuzzer, report-only lcov.

All pages fetched with scrapling (`Fetcher.get`, stealthy headers) on 2026-06-10. This file is immutable; synthesis lives in `wiki/sources/CI Design for C++-CMake Monorepos (2026-06).md`.

---

## Source 1: LLVM CI Best Practices

- URL: https://llvm.org/docs/CIBestPractices.html
- Retrieved: 2026-06-10 (page footer: "Last updated on 2026-06-10")
- Publisher: LLVM Project (official documentation, Reference section)

Extracted passages:

> "This document contains a list of guidelines and best practices to use when working on LLVM's CI systems. These are intended to keep our actions reliable, consistent, and secure."

Disabling jobs in forks:

> "We currently default to preventing actions from running outside of the LLVM organization to prevent them from running in forks... Adhering to this best practice looks like adding the following to each of the jobs specified within a workflow: `if: github.repository_owner == 'llvm'`"

Hash pinning actions:

> "It is best practice to specify an exact commit SHA from which to pull the action, noting the version in a comment... Specifying an exact SHA rather than just a major version ensures we end up running the same action originally specified... The biggest reason to prefer hash pinned dependencies is security. Release assets on GitHub are mutable, allowing an attacker to change the code within a specific version of an action after the fact... Hash pinning the dependencies prevents this as the hash would change with the code."

Versioned runner images:

> "GitHub actions allows the use of either specifically versioned runner images (e.g., `ubuntu-22.04`), or just the latest runner image (e.g., `ubuntu-latest`). It is best practice to use explicitly versioned runner images. This prevents breakages when GitHub rolls the latest runner image to a new version with potentially breaking changes, instead allowing us to explicitly opt-in to using the new image when we have done sufficient testing."

Top-level read permissions:

> "The top of every workflow should specify that the job only has read permissions: `permissions: contents: read`. If specific jobs within the workflow need additional permissions, those permissions should be added within the specific job. This practice locks down all permissions by default... better enforcing the principle of least privilege."

Event correctness (verbatim, both rules):

> "1. Workflows that are designed to run on pull requests should not be restricted by target branch. Restricting the target branch unnecessarily will prevent any stacked PRs from being tested. `pull_request` events should not contain a branches key."
> "2. Workflows that are designed to also trigger on push events (e.g., for testing on `main` or one of the release branches) need to be restricted by branch... stacked PRs will end up running jobs twice if the `push` event does not have any branch restrictions. `push` events should have their branches restricted at the very least to `main` and the release branches."

Workflow self-testing:

> "Whenever possible, workflows should also run whenever the workflow definition is updated. This enables easily testing the workflow whenever modifying it. For example, if we have a workflow with a definition in `.github/workflows/foo.yaml`, we should have at least the following event within the workflow: `pull_request: paths: - .github/workflows/foo.yaml`"

Credential persistence:

> "Github's `actions/checkout` action will by default leave credentials from the default Github token inside the git checkout it creates... This should be disabled by default as follows: `persist-credentials: false`."

Containers: prefer fully qualified registry names (`docker.io/library/ubuntu:24.04@sha256:<digest>`) and hash-pin container images by SHA256 digest; updates handled by Renovate.

---

## Source 2: GitHub Docs — Troubleshooting required status checks

- URL: https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/collaborating-on-repositories-with-code-quality-features/troubleshooting-required-status-checks
- Retrieved: 2026-06-10
- Publisher: GitHub official documentation

Extracted passages:

Successful statuses:

> "In order for a pull request to be merged, all required checks must pass against the latest commit SHA... Successful check statuses are: `success`, `skipped`, and `neutral`."

The path-filter trap (verbatim warning):

> "If a workflow is skipped due to path filtering, branch filtering or a commit message, then checks associated with that workflow will remain in a 'Pending' state. A pull request that requires those checks to be successful will be blocked from merging."

The crucial asymmetry between workflow-level and job-level skipping:

> "If, however, a job within a workflow is skipped due to a conditional, it will report its status as 'Success'."

Dependent jobs:

> "When a job fails, any jobs that depend on the failed job are skipped and do not report a failure. A pull request that requires the check may not be blocked. To use a required check on a job that depends on other jobs, use the `always()` conditional expression in addition to `needs`."

Worked example: a workflow with `on: pull_request: paths: ['scripts/**']` whose `build` job is required — "a pull request that only changes a file in the root of the repository will not trigger this workflow and is blocked from merging. On the pull request, you would see 'Waiting for status to be reported.'"

Merge queues:

> "You must use the `merge_group` event to trigger your GitHub Actions workflow when a pull request is added to a merge queue... Otherwise, status checks will not be triggered when you add a pull request to a merge queue. The merge will fail as the required status check will not be reported."

(Implication drawn by GitHub's docs structure: required checks should be skipped at the job level via `if:` conditionals — which report Success — not at the workflow level via `paths:`/`branches:`, which leave checks Pending forever. The widely-referenced community workaround for workflow-level filtering is a same-named no-op workflow with inverse `paths-ignore`.)

---

## Source 3: GitHub Docs — Reuse workflows

- URL: https://docs.github.com/en/actions/how-tos/sharing-automations/reuse-workflows (served as /actions/how-tos/reuse-automations/reuse-workflows)
- Retrieved: 2026-06-10
- Publisher: GitHub official documentation

Extracted passages:

> "Reusable workflows are YAML-formatted files, very similar to any other workflow file... you locate reusable workflows in the `.github/workflows` directory of a repository. Subdirectories of the workflows directory are not supported. For a workflow to be reusable, the values for `on` must include `workflow_call`."

Inputs/secrets: defined under `on.workflow_call.inputs` / `on.workflow_call.secrets`; callers pass them with `with:` and `secrets:`; same-org callers may use `secrets: inherit`. "Environment secrets cannot be passed from the caller workflow as `on.workflow_call` does not support the `environment` keyword."

Calling:

> "You call a reusable workflow by using the `uses` keyword... you call reusable workflows directly within a job, and not from within job steps." Reference syntaxes: `{owner}/{repo}/.github/workflows/{filename}@{ref}` or `./.github/workflows/{filename}` for same-repo. "If you use the second syntax option the called workflow is from the same commit as the caller workflow." "Using the commit SHA is the safest option for stability and security."

Matrix × reusable workflow:

> "Jobs using the matrix strategy can call a reusable workflow. A matrix strategy lets you use variables in a single job definition to automatically create multiple job runs that are based on the combinations of the variables. For example, you can use a matrix strategy to pass different inputs to a reusable workflow." (Example: `strategy: matrix: target: [dev, stage, prod]` then `uses: .../deployment.yml` with `target: ${{ matrix.target }}`.)

Nesting limits:

> "You can connect a maximum of ten levels of workflows — that is, the top-level caller workflow and up to nine levels of reusable workflows... Loops in the workflow tree are not permitted." "Permissions can only be maintained or reduced — not elevated — throughout the chain."

Secrets through chains: "Secrets are only passed to directly called workflow, so in the workflow chain A > B > C, workflow C will only receive secrets from A if they have been passed from A to B, and then from B to C."

Outputs: reusable workflows expose `on.workflow_call.outputs` mapped from job-level outputs; callers read `needs.<job>.outputs.<name>`. Under a matrix, "the output will be the output set by the last successful completing reusable workflow of the matrix which actually sets a value."

---

## Source 4: CMake official manual — cmake-presets(7)

- URL: https://cmake.org/cmake/help/latest/manual/cmake-presets.7.html
- Retrieved: 2026-06-10
- Publisher: Kitware / CMake official documentation

Extracted passages:

Purpose (CI named explicitly):

> "One problem that CMake users often face is sharing settings with other people for common ways to configure a project. This may be done to support CI builds, or for users who frequently use the same build. CMake supports two main files, `CMakePresets.json` and `CMakeUserPresets.json`... `CMakePresets.json` is meant to specify project-wide build details, while `CMakeUserPresets.json` is meant for developers to specify their own local build details. `CMakePresets.json` may be checked into a version control system, and `CMakeUserPresets.json` should NOT be checked in."

Preset kinds and schema versions: `configurePresets` (v1+), `buildPresets` and `testPresets` (v2+), `packagePresets` and `workflowPresets` (v6+). Files may `include` other preset files (v4+).

Inheritance and hidden bases:

> "`hidden`: An optional boolean specifying whether or not a preset should be hidden. If a preset is hidden, it cannot be used in the `--preset` argument... hidden presets are intended to be used as a base for other presets to inherit via the `inherits` field."
> "`inherits`: An optional array of strings representing the names of presets to inherit from... The preset will inherit all of the fields from the inherits presets by default (except name, hidden, inherits, description, and displayName), but can override them as desired."

Conditions (OS-gating presets, mirrors a CI OS matrix):

> Example configure preset `windows-only` with `"condition": {"type": "equals", "lhs": "${hostSystemName}", "rhs": "Windows"}`.

Test presets carry CI-grade strictness in the documented example: `"output": {"outputOnFailure": true}, "execution": {"noTestsAction": "error", "stopOnFailure": true}`.

Workflow presets chain the whole pipeline in one driver command:

> Example `workflowPresets` entry named `default` with ordered `steps`: configure → build → test → package. (Run via `cmake --workflow --preset <name>`; each step references a preset of that type bound to the same configure preset.)

Build/test/package presets are bound to a configure preset via `configurePreset`, so a named preset string is a complete, reproducible description of a CI job's configure+build+test behavior.

---

## Source 5: ClusterFuzzLite — Step 2: Running ClusterFuzzLite

- URL: https://google.github.io/clusterfuzzlite/running-clusterfuzzlite/
- Retrieved: 2026-06-10
- Publisher: Google (ClusterFuzzLite official documentation; CI-integrated ClusterFuzz for libFuzzer targets)

Extracted passages:

Modes:

> "ClusterFuzzLite offers two primary modes of fuzzing: code change fuzzing and batch fuzzing... also two helper modes... prune and coverage."

Code-change (PR) fuzzing:

> "The core way to use ClusterFuzzLite is to fuzz code changes that were introduced in a pull request/code review or commit. Code change fuzzing allows ClusterFuzzLite to find bugs before they are committed into your code and while they are easiest to fix. Code change fuzzing is designed to be fast so that it integrates easily into your development workcycle: It defaults to fuzzing for 10 minutes... It quits after finding a single crash."

Batch fuzzing (the nightly tier):

> "In batch fuzzing mode all fuzzers are run for a preset, longer, amount of time... Given the longer runtime, we suggest batch fuzzing should be run on a schedule such as once daily, rather than on code changes. By running for a longer amount of time, batch fuzzing serves two important purposes: It can find bugs that are missed or are not reported by code change fuzzing... It builds a corpus for each of your fuzz targets... This corpus will be used by code coverage report generation, code change fuzzing, and later runs of batch fuzzing. The corpus is saved using your CI system's feature for storing files."

Corpus pruning:

> "If you are using batch fuzzing, you should run corpus pruning once a day... Corpus pruning should be considered mandatory when you are using batch fuzzing but otherwise should not be used."

Coverage-directed PR fuzz selection:

> "The data from coverage reports is also used by code change fuzzing to determine which fuzzers are affected by a code change. If code change fuzzing can determine which fuzzers are affected, it will run only those fuzzers. Otherwise, it will run all of them."

Continuous builds (baseline triage):

> "The continuous builds task enables code change fuzzing to identify whether the cause of a crash was introduced by the code change. With the continuous builds task, if the cause of the crash was pre-existing, the crash is not reported by code change fuzzing. If code change fuzzing is run without the continuous builds task, all crashes will be reported."

Key config knobs: `fuzz-seconds` (default 600, "an appropriate starting point for code change fuzzing. You should increase this number to spend more time batch fuzzing"), `sanitizer` (address/undefined/memory/coverage, default address), `parallel-fuzzing`, `minimize-crashes`, `mode`. Supported CI systems: GitHub Actions, GitLab, Google Cloud Build, Prow.

---

## Source 6: Google Testing Blog — Flaky Tests at Google and How We Mitigate Them

- URL: https://testing.googleblog.com/2016/05/flaky-tests-at-google-and-how-we.html
- Retrieved: 2026-06-10
- Author: John Micco (Google), 2016-05-27. Canonical reference for gating policy at thousands-of-tests scale.

Extracted passages:

Two-tier gating model:

> "Tests are run before submission (pre-submit testing) which gates submission and verifies that changes are acceptable, and again after submission (post-submit testing) to decide whether the project is ready to be released. In both cases, all of the tests for a particular project must report a passing result."

Scale of flakiness:

> "Across our entire corpus of tests, we see a continual rate of about 1.5% of all test runs reporting a 'flaky' result. We define a 'flaky' test result as a test that exhibits both a passing and a failing result with the same code... Almost 16% of our tests have some level of flakiness associated with them."
> "About 84% of the transitions we observe from pass to fail involve a flaky test... It is quite common to ignore legitimate failures in flaky tests due to the high number of false-positives."

Cost at ~1000-test project scale:

> "The average project contains 1000 or so individual tests... If 1.5% of test results are flaky, 15 tests will likely fail, requiring expensive investigation... The same 15 or so failing tests block submission and introduce costly delays... Ignoring legitimate failures at this stage results in the submission of broken code."

Alarm fatigue:

> "It is human nature to ignore alarms when there is a history of false signals coming from a system."

Mitigations and their hazards:

> "We have several mitigation strategies for flaky tests during presubmit testing, including the ability to re-run only failing tests, and an option to re-run tests automatically when they fail. We even have a way to denote a test as flaky — causing it to report a failure only if it fails 3 times in a row. This reduces false positives, but encourages developers to ignore flakiness in their own tests."
> "A tool that monitors the flakiness of tests and if the flakiness is too high, it automatically quarantines the test. Quarantining removes the test from the critical path and files a bug for developers to reduce the flakiness. This prevents it from becoming a problem for developers, but could easily mask a real race condition or some other bug in the code being tested."

(Notable practitioner comment on the post, Wayne Roseberry: runs reliability suites of all CI tests per build to compute consistency rates, then moves tests below a consistency threshold out of the gating CI suite while keeping them running for coverage — an explicit mandatory-vs-non-gating tiering mechanism.)

---

## Sources considered and dropped

- oneuptime.com / kernelpanicllc.com / timesofcloud.com monorepo path-filter posts — SEO listicles; superseded by GitHub's official troubleshooting page (Source 2).
- github.com/orgs/community discussions #44490 and #26251 — primary evidence that the path-filter/required-check problem is unresolved at the platform level, but the official docs page states the same warning; not separately fetched.

No source blocked scrapling; all six fetched on the first attempt with `Fetcher.get`.
