## 1. Engine exclusion and diff gate (informational)

- [ ] 1.1 Add `'*/engine/*'` to the `lcov --remove` pattern list in the `coverage` job (.github/workflows/ci.yml:744-747). Verify: `coverage.filtered.info` from a dispatch run contains no `SF:` path under `engine/`; `lcov --list` totals drop accordingly.
- [ ] 1.2 Set `fetch-depth: 0` on the `coverage` job checkout (.github/workflows/ci.yml:715) and add a `git fetch origin master` step for pull-request events. Verify: `git merge-base origin/master HEAD` succeeds inside the job on a PR run.
- [ ] 1.3 Add `pip install diff-cover` to the job's dependency step and a pull-request-only step running `diff-cover coverage.filtered.info --compare-branch=origin/master --exclude 'engine/**'` in informational mode (no `--fail-under`). Verify: the step prints a per-file diff-coverage report on a PR touching `src/`.
- [ ] 1.4 Replace the report-only echo (.github/workflows/ci.yml:749) with policy text assembled from the diff-cover output (and later the floor-check output), keeping `coverage-policy.txt` in the uploaded artifact. Verify: the artifact's policy file contains the diff verdict and no report-only disclaimer.
- [ ] 1.5 Confirm diff-cover's path matching is live, not vacuous: on a test PR adding an uncovered first-party line, the informational report lists that file below 100%. A report showing no files on such a PR means `SF:` paths and diff paths diverge — fix before any enforcement.

## 2. Per-module ratchet floors

- [ ] 2.1 After task group 1 merges, record the first master run of the `coverage` job and extract per-module line percentages via `lcov --extract coverage.filtered.info "*/src/<module>/*"` + `lcov --summary` for `src/app`, `src/legends`, `src/legends_ipc`, `src/legends_proxy`, `src/engine_host`, `src/pal`, `src/libs` (shell pattern already demonstrated at .github/workflows/ci.yml:912-917).
- [ ] 2.2 Commit `.ci/coverage-floors.txt` seeding each module's floor at its measured value rounded down to one decimal; decide `src/libs` floor-vs-exemption from what the extract actually measures; header comment states the never-decrease rule and the tracked-issue requirement for lowering.
- [ ] 2.3 Add the floor-check loop to the `coverage` job: for each floor-file line, extract the module, compare measured vs floor with 0.5-point slack, fail naming module/floor/measured on breach, print raise-prompt when above floor; fail if any DAG module directory lacks a floor line. Verify: a dispatch run passes at seeded floors.
- [ ] 2.4 Prove the floor gate can fail: in a throwaway branch, lower one floor's measured side (or raise a floor above reality), confirm the job goes red with the named module, then discard. Verify: red run recorded, no change merged.

## 3. Diff gate enforcement

- [ ] 3.1 After one informational PR cycle, choose the `--fail-under` target from the observed diff-coverage values and flip the diff-cover step to enforcing. Verify: workflow file diff shows the target; CI green on a covered PR.
- [ ] 3.2 Prove the diff gate can fail: seed a PR with an uncovered new first-party line, confirm the `coverage` job fails, then fix or close the seed PR. Verify: red run recorded against the seed.

## 4. Release-validation rehearsal

- [ ] 4.1 Widen `release-validation`'s condition (.github/workflows/ci.yml:879) to tag pushes or `workflow_dispatch`, replacing default `needs` success propagation with explicit checks: `needs.linux.result == 'success'` always; `needs.packaging.result == 'success'` required only on tag refs (packaging is tag-only, .github/workflows/ci.yml:804, and would otherwise skip-cascade).
- [ ] 4.2 Guard the artifact download and verification steps (.github/workflows/ci.yml:923-929 and the steps following) with `if: startsWith(github.ref, 'refs/tags/v')` so dispatch runs exercise only build/test/threshold.
- [ ] 4.3 Run one `workflow_dispatch` rehearsal; record whether `src/app` clears the 80% threshold (.github/workflows/ci.yml:907-921). If it fails, file the gap issue — the rehearsal finding is the deliverable either way. Verify: a completed dispatch run of `release-validation` exists with the threshold step executed and artifact steps skipped.

## 5. Verification and record

- [ ] 5.1 End-to-end check on a dispatch run: `coverage.filtered.info` engine-free, floor loop green at seeded values, `coverage-policy.txt` states enforced verdicts; on a PR run: diff-cover enforcing. Grep `.github/workflows/ci.yml` for the report-only echo — zero hits.
- [ ] 5.2 Update audit-wiki Verification Lanes (Coverage section) and CI-THESIS.md R9 status to reflect the enforced lane, including the rehearsal outcome for the release threshold.
