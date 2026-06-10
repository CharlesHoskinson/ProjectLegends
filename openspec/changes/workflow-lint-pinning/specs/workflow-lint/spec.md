## ADDED Requirements

### Requirement: Workflow YAML is linted on every change
A lint lane SHALL run actionlint, with shellcheck integration enabled, over every file in `.github/workflows/` on every push and pull request. The lane SHALL fail on any actionlint error. The lane SHALL NOT declare workflow-level path filters, so it reports on every PR and remains eligible to become a required check.

#### Scenario: Broken expression introduced
- **WHEN** a workflow change introduces an invalid `${{ }}` expression, a reference to an undefined `needs:` job, or a malformed `if:` condition
- **THEN** the lint lane fails on that push or PR, before the defect can surface as a confusing run on `master`

#### Scenario: Shell error in a run block
- **WHEN** a workflow `run:` step contains a shell construct shellcheck classifies as an error
- **THEN** the lint lane fails and reports the file, line, and shellcheck code

#### Scenario: Non-workflow PR still reports
- **WHEN** a pull request touches no file under `.github/workflows/`
- **THEN** the lint lane still runs and reports a verdict (it is cheap and unconditional, never pending-forever)

### Requirement: Lint findings are fixed or suppressed with a recorded reason
The lint lane SHALL run with zero unexplained suppressions. Any actionlint ignore entry SHALL carry a link to a tracked issue or change that owns the underlying fix.

#### Scenario: Pre-existing finding needs its own change
- **WHEN** actionlint reports a defect whose fix belongs to another change
- **THEN** a targeted ignore entry is added with a link to that change, and the lane lands green with the suppression visible in the config

### Requirement: Lint lane enforces the permissions-block policy
The lint lane SHALL fail when any workflow file under `.github/workflows/` lacks a top-level `permissions:` block. This requirement owns enforcement only; the policy requirement ("Every workflow declares least-privilege permissions") is owned by the `workflow-hygiene` capability (`consolidate-workflows-policy`) and is satisfied by whichever change lands the blocks first.

#### Scenario: New workflow without permissions
- **WHEN** a PR adds a workflow file with no top-level `permissions:` key
- **THEN** the lint lane fails, naming the file

#### Scenario: Hygiene change already landed the blocks
- **WHEN** `consolidate-workflows-policy` has already added `permissions: contents: read` to all workflows
- **THEN** the enforcement check passes with no further edit; the two changes compose without conflict

### Requirement: Lint lane complies with the policies it enforces
The lint lane's own workflow file SHALL declare a top-level `permissions: contents: read` block, an explicit `timeout-minutes`, a `concurrency:` group, and SHALL contain no unpinned third-party action reference.

#### Scenario: Lane validates itself
- **WHEN** the lint lane runs after any subsequent edit to its own workflow file
- **THEN** the edited file is within the lane's own lint and policy-check scope and a violation fails the lane
