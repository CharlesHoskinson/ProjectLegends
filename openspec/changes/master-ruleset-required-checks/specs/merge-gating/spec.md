## ADDED Requirements

### Requirement: Master accepts changes only via pull request
An Active GitHub ruleset SHALL target exactly `refs/heads/master` (no wildcard) and SHALL require a pull request before merging. Direct pushes, force pushes, and branch deletion SHALL be blocked.

#### Scenario: Direct push rejected
- **WHEN** a commit is pushed directly to `master` by a non-bypass actor
- **THEN** the push is rejected by the ruleset

#### Scenario: Force push rejected
- **WHEN** a force push to `master` is attempted
- **THEN** the push is rejected regardless of check status

### Requirement: Merging requires the five exact-name checks
The ruleset SHALL require these status checks, matched by expanded job name byte-exactly: `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`. Each required check SHALL be a job that runs unconditionally on every pull request (no workflow- or job-level path filter).

#### Scenario: Red check blocks merge
- **WHEN** a pull request targets `master` and any required check fails or has not reported
- **THEN** the merge is blocked

#### Scenario: All required checks green
- **WHEN** all five required checks report success on the PR head and the branch is up to date with `master`
- **THEN** the merge is permitted

#### Scenario: Path-filtered gate proposed as required
- **WHEN** a change proposes adding a check produced by a path-filtered workflow to the required set
- **THEN** the proposal is rejected until the gate runs unconditionally (per `requirable-path-gates`), because a non-reporting required check blocks every merge

### Requirement: Branches must be up to date before merge
The ruleset SHALL enable the strict up-to-date policy: required checks MUST have passed against a PR head that contains the current tip of `master`.

#### Scenario: Master advances after checks pass
- **WHEN** `master` advances after a PR's checks passed
- **THEN** the merge is blocked until the PR is updated and the required checks pass again on the merged result

### Requirement: Ruleset configuration is tracked in the repository
The exact ruleset payload SHALL be committed at `docs/ci/master-ruleset.json` and SHALL be the canonical definition of the server-side ruleset. The file SHALL be accompanied by documented `gh api` commands to apply it and to verify the live state against it.

#### Scenario: Live ruleset diverges from the committed payload
- **WHEN** the verification read (`gh api repos/{owner}/{repo}/rulesets` and `gh api repos/{owner}/{repo}/rules/branches/master`) differs from `docs/ci/master-ruleset.json`
- **THEN** the live ruleset is re-applied from the committed file (or the file is changed via PR first)

### Requirement: Required-check names stay synchronized with workflow job names
Any change that renames a `ci.yml` job whose expanded name appears in the required set SHALL update `docs/ci/master-ruleset.json` and re-apply the ruleset in the same change.

#### Scenario: Workflow consolidation renames a required job
- **WHEN** a change (e.g. workflow consolidation under `consolidate-workflows-policy`) renames `Linux (gcc)` or any other required check
- **THEN** that change updates `docs/ci/master-ruleset.json` with the new expanded name and re-applies the ruleset before or with the rename landing on `master`

### Requirement: Bypass is admin-only and audited
The ruleset SHALL grant bypass to the repository-admin role only. The merge policy SHALL state that bypass use is exceptional and reviewed via the ruleset audit trail.

#### Scenario: Emergency bypass
- **WHEN** an admin bypasses the ruleset to push to `master`
- **THEN** the event is recorded in the ruleset audit trail and is treated as an incident per `docs/ci/merge-policy.md`

### Requirement: Activation is gated on stabilized lanes
The ruleset SHALL NOT be applied (enforcement `active`) until `ci-stabilize-mandatory-lanes` (R1) has landed and all five required checks are green on the current `master` head.

#### Scenario: Premature activation attempt
- **WHEN** application of the ruleset is attempted while any of the five checks is failing on `master` head or R1 is unmerged
- **THEN** the apply step is not executed; activating protection over red checks freezes all merging

### Requirement: Merge queue is deferred with a stated re-entry condition
The ruleset SHALL NOT enable a merge queue. The merge policy SHALL record the re-entry condition: adopt a queue only when concurrent-PR contention is observed, and only after every required-check workflow gains a `merge_group` trigger and its job-level event whitelists admit `merge_group`.

#### Scenario: Queue adoption proposed
- **WHEN** a merge queue is proposed for `master`
- **THEN** the proposal is accepted only if `ci.yml` declares `merge_group` in its `on:` block and no job-level `if:` event whitelist (e.g. the sanitizers/fuzz patterns at `ci.yml:333-337`, `:482-487`) silently skips on `merge_group`
