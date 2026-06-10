## Context

No job lints or validates workflow YAML; the only effect of editing a workflow is re-running it (Gap Analysis — Maintainability finding 8). The cost is documented in the run history: the `Optional Linux SDL3 (${{ matrix.compiler }})` job recorded under its unexpanded template name without anyone noticing (CI Run History, "Nightly/manual-only lanes"). All 46 `uses:` references across the four workflows are mutable tags; the third-party inventory is exactly one — `codecov/codecov-action@v4` (`ci.yml:761`) — with the rest first-party `actions/*` (checkout@v4, setup-python@v5, upload-artifact@v4, cache@v4, setup-java@v4, download-artifact@v4). `permissions: contents: read` exists only in ci.yml (`ci.yml:29-30`). No dependabot config exists anywhere in the repo (Recommendation Review A-8).

Researched practice (CI Design for C++-CMake Monorepos, practice 4): workflows tested by the PRs that change them; third-party actions hash-pinned because release tags are mutable; read-only default permissions at the top of every file. Required-check selection is by exact expanded job name, so name drift is a merge-blocking hazard once checks become required — the names need machine checking first (Merge Queues & Required Checks, P4).

The A-8 adversarial binding constrains scope: land actionlint and permissions now; SHA-pin third-party actions **only together with** a dependabot config — pinning without an updater becomes stale-pin rot; versioned runner labels optional. A-3 feeds A-8: R14 (compiler caching) will introduce two new third-party actions, so the pin policy and updater must exist before they arrive.

## Goals / Non-Goals

**Goals:**
- A lint lane that fails on actionlint errors in any workflow file, on every push and PR, with no path filter — always reporting, hence requirable.
- Mechanical enforcement of two policies in the same lane: top-level `permissions:` present in every workflow; every third-party `uses:` pinned to a full-length commit SHA.
- `codecov/codecov-action` pinned to a SHA with a version comment, in the same PR as a `.github/dependabot.yml` covering `github-actions`.
- Permissions blocks present in all four workflows when this change completes, whether this change or `consolidate-workflows-policy` put them there.

**Non-Goals:**
- Versioned runner labels (`ubuntu-24.04` over `ubuntu-latest`) — A-8 marks them optional; actionlint validates label names either way; deferred.
- Pinning first-party `actions/*` to SHAs — they stay on major tags; dependabot bumps majors. The threat model A-8 cites (mutable release tags re-pointed by a compromised third party) applies to third-party owners.
- Adding the lint check to the master ruleset — `master-ruleset-required-checks` owns ruleset content; this change only makes the lane *eligible* (unconditional, stable name).
- The permissions *policy requirement* — owned by `consolidate-workflows-policy`'s `workflow-hygiene` capability. This change owns enforcement plus an idempotent edit (see D4).
- Timeouts/concurrency on the existing four workflows (consolidate-workflows-policy hygiene group), compiler caching (R14), gate-script consolidation (R3).

## Decisions

**D1 — New `lint.yml`, not a job in ci.yml.** A separate file keeps the 931-line ci.yml from growing, gives the lane its own trigger surface (push + PR on all branches, no path filters), and means a broken ci.yml cannot take the linter down with it — the lane that validates workflows should not live inside the largest workflow it validates. No path filter on the lane itself: linting is seconds-cheap, and an unconditional check is the only kind that can ever join the required set (P4 pend-forever hazard). The `.github/workflows/**`-scoped trigger suggested in the gap analysis is rejected for that reason. Alternative rejected: a job in ci.yml — inherits ci.yml's branch-restricted triggers and couples the linter to the file it lints.

**D2 — actionlint runs as a pinned, checksum-verified release binary, not via a third-party wrapper action.** The popular wrapper actions for actionlint are themselves third-party — bootstrapping the supply-chain lane through an unpinned third-party action is circular. Instead: download the actionlint release tarball at a pinned version, verify its SHA-256 against a checksum recorded in the workflow, run it with shellcheck integration on (shellcheck is preinstalled on ubuntu runners, and the inline `run:` blocks across 1,526 lines of YAML are exactly where the bugs live). Version bumps are a one-line PR (version + checksum). Alternative rejected: `docker run rhysd/actionlint` — pulls a mutable docker tag, same circularity.

**D3 — Policy checks are plain script steps in the lint job, not extra tools.** Two checks actionlint does not perform: (a) every `.github/workflows/*.yml` has a top-level `permissions:` key; (b) every `uses:` whose owner is not `actions` (and is not a local `./` reference) pins a 40-hex SHA. Both are a few lines of grep/python over the workflow files — no new dependency, no new third-party action. Alternative rejected: zizmor or ensure-sha-pinned-actions — capable tools, but each is another third-party action to pin and update, bought to replace ~20 lines of script.

**D4 — Permissions edit is idempotent across changes; enforcement lives here, policy lives in `consolidate-workflows-policy`.** Both changes touch the same three files (`pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml` lack `permissions:`). Division: `consolidate-workflows-policy`'s `workflow-hygiene` capability states the policy requirement ("Every workflow declares least-privilege permissions") and its task 1.4 makes the edit; this change's `workflow-lint` capability states only the enforcement requirement (lint fails when a block is missing) and its task makes the same edit *if still absent*. Whichever lands first, the second is a verified no-op; after both, regression is mechanically impossible. The requirement text is deliberately not duplicated into this change's spec — double ownership of one requirement across two pending changes would collide at archive time.

**D5 — Pins and updater are one atomic PR.** The A-8 binding is explicit: a SHA pin without an updater rots — the comment says `# v4.x.y` forever while CVEs accumulate in the pinned commit's future. So `.github/dependabot.yml` (`package-ecosystem: github-actions`, weekly, targeting the default branch) lands in the same PR as the codecov pin, and the lint lane's pin check lands in the same PR too — making it impossible to add a future third-party action unpinned (R14's cache actions arrive into an enforced policy). Dependabot bumps SHA-pinned actions natively, updating both the SHA and the trailing version comment. Alternative rejected: renovate — more configurable, but dependabot is zero-infrastructure and native to GitHub.

**D6 — Lint lane is born compliant with the hygiene policy.** `lint.yml` ships with `permissions: contents: read`, `timeout-minutes` (small — the lane is grep + a static binary over kilobytes of YAML), and `concurrency: group: ${{ github.workflow }}-${{ github.ref }}` with `cancel-in-progress` for PR events only, matching the D3 convention of `consolidate-workflows-policy`. A hygiene-enforcing lane that violates the hygiene policy would fail its own checks the moment consolidate-workflows-policy's requirements are enforced.

## Risks / Trade-offs

- [actionlint flags pre-existing issues in 1,526 lines of YAML on first run, blocking the lane's own PR] → first PR fixes what it finds or, for findings needing their own change, adds targeted `actionlint.yaml` ignores with an issue link each; the lane lands green with zero unexplained suppressions.
- [Permissions-block edit races `consolidate-workflows-policy` task 1.4 in flight] → the edit is textually identical (`permissions: contents: read` at top level) and the task here is check-then-edit; a merge conflict resolves to the same line.
- [SHA pin breaks codecov upload (pinned commit ≠ tag behavior)] → pin to the exact commit the `v4` tag currently resolves to; the codecov step is already conditional on `CODECOV_TOKEN` (`ci.yml:759-764`) and non-required, so a failure is visible, not blocking.
- [Dependabot PRs add noise] → weekly schedule and the `github-actions` ecosystem only; the action inventory is small (one third-party today), so volume is a few PRs a month at most.
- [Pin-check regex misclassifies a future `uses:` form (reusable workflow `./.github/workflows/x.yml`, docker `uses`)] → local references and `actions/*` are explicitly exempted; the check's test in tasks includes a fixture for each `uses:` form; consolidate-workflows-policy's `build-and-test.yml` will be a local reference and passes by construction.
- [Self-validation gap: lint.yml cannot gate the PR that introduces lint.yml] → run actionlint locally on the branch before pushing; the lane validates itself on every subsequent change.

## Migration Plan

1. One PR: `lint.yml` (actionlint + permissions check + pin check), permissions blocks where still missing, codecov SHA pin, `dependabot.yml`. Each piece is independently revertable; the pin and updater revert together if at all (D5).
2. Pre-existing actionlint findings fixed in the same PR or suppressed with issue-linked ignores.
3. Rollback: revert the PR. No server-side state, no ruleset interaction.

## Open Questions

- Whether the lint lane should later absorb the ten sprint2 gate scripts' YAML-step replacements is R3's question (`preflight-gate-entrypoint`), not this change's; the lane stays single-purpose until R3 decides.
