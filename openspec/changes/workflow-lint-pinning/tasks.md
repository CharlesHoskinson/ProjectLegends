## 1. Lint lane

- [ ] 1.1 Create `.github/workflows/lint.yml`: triggers `push` + `pull_request` with no path filters; top-level `permissions: contents: read`; `timeout-minutes: 5`; `concurrency: { group: ${{ github.workflow }}-${{ github.ref }}, cancel-in-progress: ${{ github.event_name == 'pull_request' }} }`.
- [ ] 1.2 Add the actionlint step: download a pinned actionlint release tarball, verify its SHA-256 against a checksum recorded in the workflow, run it over `.github/workflows/` with shellcheck integration enabled (shellcheck is preinstalled on ubuntu runners). No third-party wrapper action (design D2).
- [ ] 1.3 Run actionlint locally on the branch against all five workflow files; fix what it finds in this PR, or for findings owned by another change add a targeted `.github/actionlint.yaml` ignore with a link to that change — zero unexplained suppressions.
- [ ] 1.4 Add the permissions-presence check step: fail if any `.github/workflows/*.yml` lacks a top-level `permissions:` key, naming the file.
- [ ] 1.5 Add the pin check step: fail on any `uses:` reference whose owner is not `actions` and which is not a local `./` reference, unless it pins a 40-hex commit SHA. Test the classifier against fixtures for each `uses:` form: `actions/x@v4`, `owner/x@v2`, `owner/x@<40-hex>`, `./.github/workflows/x.yml`.

## 2. Permissions blocks (idempotent with consolidate-workflows-policy task 1.4)

- [ ] 2.1 Check `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml` for a top-level `permissions:` block; add `permissions: contents: read` to each file still lacking one. If `consolidate-workflows-policy`'s hygiene group already landed them, verify and skip — no edit, no conflict.
- [ ] 2.2 Confirm `ci.yml` retains its existing block (`ci.yml:29-30`) and the check from 1.4 passes on all five files.

## 3. Pinning + updater (one atomic PR with section 1)

- [ ] 3.1 Resolve the commit SHA that `codecov/codecov-action@v4` currently points to (`gh api repos/codecov/codecov-action/git/ref/tags/v4`); replace the tag reference at `ci.yml:761` with the full SHA plus a trailing `# v4.x.y` comment.
- [ ] 3.2 Create `.github/dependabot.yml`: `package-ecosystem: github-actions`, directory `/`, weekly schedule — in the same PR as 3.1 (pins never land without the updater, design D5).
- [ ] 3.3 Leave first-party `actions/*` references on their major tags (design Non-Goal); confirm the pin check from 1.5 passes on the full tree.

## 4. Verification

- [ ] 4.1 Negative test, lint: push a commit with a deliberate workflow defect (reference to an undefined `needs:` job); confirm the lint lane fails naming the file and line; revert.
- [ ] 4.2 Negative test, permissions: push a commit removing a `permissions:` block; confirm the lane fails; revert.
- [ ] 4.3 Negative test, pinning: push a commit adding a throwaway `uses: owner/action@v1` step; confirm the lane fails; revert.
- [ ] 4.4 Confirm the lane reports on a PR touching no workflow file (no path filter — never pending, requirable later under `master-ruleset-required-checks`).
- [ ] 4.5 Confirm dependabot is active: the repo's Insights → Dependency graph → Dependabot tab lists the `github-actions` ecosystem with a last-checked time (or trigger a check via the UI) and no configuration errors.
