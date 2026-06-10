## ADDED Requirements

### Requirement: Every job declares an explicit timeout
Every job in every workflow under `.github/workflows/` SHALL declare `timeout-minutes`. No job SHALL rely on GitHub's 360-minute default.

#### Scenario: Job without timeout introduced
- **WHEN** a workflow change adds or modifies a job with no `timeout-minutes` key
- **THEN** review rejects the change until the key is present

#### Scenario: Hung job bounded
- **WHEN** a job hangs (e.g. a wedged test or clone)
- **THEN** the runner terminates it at its declared `timeout-minutes`, not at 360 minutes

### Requirement: Every workflow declares least-privilege permissions
Every workflow file SHALL declare `permissions: contents: read` at the top level. A job needing more SHALL widen permissions at job level only, with the need stated in a comment.

#### Scenario: Workflow without permissions block
- **WHEN** a workflow file lacks a top-level `permissions:` block
- **THEN** the workflow is non-compliant and is fixed to `contents: read`

#### Scenario: Job needs write access
- **WHEN** a job requires a scope beyond `contents: read`
- **THEN** the widened scope is declared on that job only, never at workflow level

### Requirement: Every workflow declares a concurrency group
Every workflow SHALL declare `concurrency:` with `group: ${{ github.workflow }}-${{ github.ref }}`. `cancel-in-progress` SHALL be true only for `pull_request` events; push, schedule, and dispatch runs SHALL run to completion.

#### Scenario: Superseded PR run cancelled
- **WHEN** a new commit is pushed to a PR branch while that branch's run of the same workflow is in progress
- **THEN** the in-progress run is cancelled and only the newest run completes

#### Scenario: Master push run not cancelled
- **WHEN** a second push to `master` arrives while a `master` run is in progress
- **THEN** the in-progress run completes; its verdict remains available to merge gating
