## 1. Changed-paths classifier

- [ ] 1.1 Create `scripts/ci_changed_paths.py`: takes a base and head SHA (or `--all` to force run-everything), runs `git diff --name-only`, classifies each file against the family map (`core`, `pal`, `engine`, `ipc`, `tests`, `build`, `scripts`, `openspec`, `docs-architecture`, `workflows`, `docs-only` per design D5), emits one `<family>=true|false` line per family in `GITHUB_OUTPUT` format; any file matching no rule sets every family true; comment block cites `cmake/ModuleManifest.cmake:10-51` as the source of the boundaries.
- [ ] 1.2 Handle non-diffable inputs in the script: all-zeros or unreachable base SHA → emit all-true and exit 0 with a log line saying why.
- [ ] 1.3 Add unit tests for the classifier: one case per family, the unmapped-path fail-open case, the mixed docs+code case, the unusable-base case.

## 2. module-dag.yml

- [ ] 2.1 Remove the `paths:` lists from both `push` and `pull_request` triggers (`.github/workflows/module-dag.yml:21-30, 33-42`); keep `branches: [main, master, develop]`, schedule, and `workflow_dispatch`.
- [ ] 2.2 Add a `changed-paths` first job: checkout with `fetch-depth: 0` (or depth sufficient to reach the diff base), run `scripts/ci_changed_paths.py` with event-appropriate base/head (`github.event.pull_request.base.sha` for PRs, `github.event.before` for pushes, `--all` for schedule/dispatch), declare the family booleans as job outputs.
- [ ] 2.3 Gate `include-rules` and `cmake-dag` with `needs: [changed-paths]` and `if:` that skips only when the change is docs-only (design D5).
- [ ] 2.4 Update `summary` (`module-dag.yml:182-216`): add `changed-paths` to `needs`, accept `success` or `skipped` from `include-rules` and `cmake-dag`, keep failing on their failure and on failed-not-skipped optional builds; `Summary` remains `if: always()`.
- [ ] 2.5 Remove or rewrite the header comment block (`module-dag.yml:10-12`) so "block PRs immediately" reflects the new mechanism: jobs always report; enforcement comes from the ruleset.

## 3. sprint2-checks.yml

- [ ] 3.1 Remove the `paths:` lists from both triggers (`.github/workflows/sprint2-checks.yml:5-15, 17-27`); add `branches: [main, master, develop]` to `push` only; leave `pull_request` branch-unrestricted.
- [ ] 3.2 Add the same `changed-paths` first job as 2.2.
- [ ] 3.3 Gate `globals-registry` to run on `core`/`pal`/`engine`/`ipc`/`tests`/`build`/`scripts`/`openspec`/`docs-architecture`/`workflows` families — `openspec/**` now reaches `check_openspec_staleness.py` (`sprint2-checks.yml:62-63`) and `cmake/**` reaches the cmake-adjacent checks; skip only on docs-only changes.
- [ ] 3.4 Gate `multi-instance-tests` to run on code/build/tests families; skip on `openspec`-only, `docs-architecture`-only, and docs-only changes.

## 4. ci.yml

- [ ] 4.1 Add the `changed-paths` first job (same shape as 2.2) without touching the existing trigger block (`.github/workflows/ci.yml:18-27` stays unfiltered).
- [ ] 4.2 Gate `linux`, `linux-ipc`, `windows`, `coverage`, and `abi-check` with `needs: [changed-paths]` plus an `if:` that skips only when the change is docs-only; preserve each job's existing behavior on schedule/dispatch/tag events (the classifier's `--all` path makes those run everything).
- [ ] 4.3 Extend the existing `sanitizers` and `fuzz` event conditions (`ci.yml:333-337, 482-487`) with the same docs-only skip, AND-ed with their current event whitelist; do not otherwise alter their tiering.
- [ ] 4.4 Audit `needs:` chains after inserting `changed-paths` (e.g. `static-analysis`/`fuzz` need `linux`): confirm no job that must run on schedule/dispatch is silently skipped because an upstream job was skipped — add `always() &&` guards where a dependent must evaluate its own condition.

## 5. pal-ci.yml

- [ ] 5.1 Replace both `paths:` lists (`.github/workflows/pal-ci.yml:6-11, 15-21`) with exactly: `src/pal/**`, `include/pal/**`, `include/legends/**`, `src/legends/**`, `tests/unit/test_pal_*.cpp`, `.github/workflows/pal-ci.yml` — removing `cmake/**`, `CMakeLists.txt`, and the broad `include/**`.
- [ ] 5.2 Record in the workflow header comment that pal-ci stays workflow-level path-filtered and non-requirable pending consolidation (`consolidate-workflows-policy`), citing Recommendation Review G-3.

## 6. Verification

- [ ] 6.1 Open a docs-only probe PR (e.g. touch `audit-wiki/`): confirm via the checks UI / `gh pr checks` that `Summary`, `Globals Registry Validation`, `Multi-Instance Smoke Tests`, and the ci.yml build jobs all report a conclusion (skipped), with nothing Pending, and that pal-ci does not appear.
- [ ] 6.2 Open an `openspec/**`-only probe PR: confirm `globals-registry` runs and executes `check_openspec_staleness.py`; confirm `multi-instance-tests` reports skipped.
- [ ] 6.3 Open a `cmake/**`-only probe PR: confirm `cmake-dag` and `globals-registry` run; confirm pal-ci does not trigger; confirm ci.yml build jobs run.
- [ ] 6.4 Open a `src/**` probe PR: confirm every gate job runs; confirm `Summary` aggregates correctly by checking it fails when a gate is forced to fail on a scratch branch.
- [ ] 6.5 Confirm fail-open: a probe PR adding a file in an unmapped top-level directory runs every gate job.
- [ ] 6.6 Confirm schedule/dispatch still run everything: trigger `workflow_dispatch` on ci.yml and module-dag.yml and check no job skipped due to path classification.
- [ ] 6.7 Record the probe-PR evidence (run links, per-check conclusions) in the PR description as the eligibility demonstration required before `master-ruleset-required-checks` extends its required set; do not modify the ruleset in this change.
