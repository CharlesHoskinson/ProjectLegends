## 1. Ruleset configuration as code

- [ ] 1.1 Create `docs/ci/master-ruleset.json`: the literal `POST /repos/{owner}/{repo}/rulesets` payload — name `master-merge-gate`, `target: branch`, `enforcement: active`, condition `ref_name.include: ["refs/heads/master"]` (exact ref, no wildcard), rules: `pull_request`, `required_status_checks` with `strict_required_status_checks_policy: true` and the five contexts `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`, `non_fast_forward`, `deletion`; bypass actor: repository-admin role only.
- [ ] 1.2 Verify the five context names byte-match the expanded job names in `.github/workflows/ci.yml` (lines 37 matrix expansion, 96, 190, 407) and that none of these jobs is path-filtered at workflow or job level.

## 2. Policy document

- [ ] 2.1 Create `docs/ci/merge-policy.md`: required-check set and why these five (unconditional, exact-name, per design D3); up-to-date rule as the merge-queue substitute (D4); bypass discipline — admin-only, each use an audited incident (D6); merge-queue deferral with its re-entry condition (`merge_group` triggers plus job-level `if:` audits, observed concurrent-PR contention); name-sync rule — any `ci.yml` job rename updates `master-ruleset.json` and re-applies the ruleset in the same change; `master-ruleset.json` declared canonical over UI edits. Cite CI-THESIS.md R2 and audit-wiki/wiki/sources/Merge Queues & Required Checks (2026-06).md.
- [ ] 2.2 Document in `merge-policy.md` the apply command (`gh api -X POST repos/{owner}/{repo}/rulesets --input docs/ci/master-ruleset.json`), the update command (`PUT /repos/{owner}/{repo}/rulesets/{id}`), and the rollback command (PUT with `enforcement: disabled` — stage, don't delete).

## 3. R1 prerequisite gate

- [ ] 3.1 Confirm `ci-stabilize-mandatory-lanes` (R1) is merged/archived; do not proceed to section 4 otherwise.
- [ ] 3.2 Confirm all five required checks are green on the current `master` head (`gh run list --branch master --workflow ci.yml --limit 1` then `gh run view <id>` job statuses); record the run id in the PR description.

## 4. Apply the ruleset (server-side)

- [ ] 4.1 Apply: `gh api -X POST repos/{owner}/{repo}/rulesets --input docs/ci/master-ruleset.json`; record the returned ruleset id in `docs/ci/merge-policy.md`.
- [ ] 4.2 Verify rules active on the branch: `gh api repos/{owner}/{repo}/rules/branches/master` returns the pull_request, required_status_checks (strict, five contexts), non_fast_forward, and deletion rules — previously `[]` per audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md G-2.
- [ ] 4.3 Verify ruleset matches the committed file: `gh api repos/{owner}/{repo}/rulesets/<id>` diffed against `docs/ci/master-ruleset.json` (field-level: enforcement, conditions, rules, bypass actors).

## 5. Behavioral verification

- [ ] 5.1 Negative test, direct push: push a trivial commit to `master` from a branch clone without bypass; confirm rejection; remove the test commit attempt (it never lands).
- [ ] 5.2 Negative test, red/stale PR: confirm a PR with a failing or unreported required check shows merge blocked, and a PR behind `master` head demands update before merge.
- [ ] 5.3 Positive test: land one real PR through the gate with all five checks green and branch up to date.
