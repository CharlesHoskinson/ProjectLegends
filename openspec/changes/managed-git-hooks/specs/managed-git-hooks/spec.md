# Managed Git Hooks

## ADDED Requirements

### Requirement: Committed Hook Configuration

The repository SHALL commit a hook-manager configuration (`.pre-commit-config.yaml` with `repo: local` hooks) that wires both the commit and push tiers, and a single documented install command SHALL install both hook types on a fresh clone.

#### Scenario: Fresh clone install

- **GIVEN** a fresh clone with dev dependencies installed from `requirements-dev.txt`
- **WHEN** the developer runs `pre-commit install`
- **THEN** `.git/hooks/pre-commit` and `.git/hooks/pre-push` are both installed
- **AND** no further configuration (no `core.hooksPath`, no manual copying) is required

#### Scenario: Hook logic lives in the repository

- **WHEN** the hook configuration is inspected
- **THEN** every hook entry invokes a script under `scripts/` with `language: system`
- **AND** no hook entry depends on a remote hook repository or per-hook managed environment

### Requirement: Commit Tier Runs Fast Staged-File-Triggered Checks

The commit-time hook tier SHALL run `check_includes.py`, `check_conflict_markers.py`, and `check_case_collisions.py`, triggered by staged files matching each entry's file filter, using the same script invocations CI uses (no staged-file-list variants).

#### Scenario: Include violation blocks the commit

- **GIVEN** a staged source change that violates module-boundary include rules
- **WHEN** the developer runs `git commit`
- **THEN** the commit is rejected with the check's failure output

#### Scenario: Conflict marker blocks the commit

- **GIVEN** a staged file containing an unresolved merge-conflict marker
- **WHEN** the developer runs `git commit`
- **THEN** the commit is rejected

#### Scenario: Unrelated commit is not slowed

- **GIVEN** a commit whose staged files match no commit-tier file filter
- **WHEN** the developer runs `git commit`
- **THEN** the filtered commit-tier checks are skipped

### Requirement: Push Tier Runs the Script Suite Only

The pre-push hook SHALL invoke the preflight script-suite tier (the check scripts CI runs, via `scripts/preflight.py` from `preflight-gate-entrypoint`) and SHALL NOT run any configure, build, or test step.

#### Scenario: Failing gate blocks the push

- **GIVEN** the working tree fails one of the CI-run check scripts
- **WHEN** the developer runs `git push`
- **THEN** the push is rejected with that script's failure output

#### Scenario: No build at push

- **WHEN** the pre-push hook runs
- **THEN** no `cmake` configure, build, or `ctest` invocation is executed by the hook

#### Scenario: Coverage follows preflight

- **GIVEN** a check script is added to the preflight script-suite tier
- **WHEN** the pre-push hook next runs
- **THEN** the new check runs without any hook-configuration change

### Requirement: CI Executes the Identical Hook Configuration

CI SHALL run the committed hook configuration itself (`pre-commit run --all-files` for the commit tier and `pre-commit run --all-files --hook-stage pre-push` for the push tier) rather than a separate transcription of the same checks.

#### Scenario: Skipped hooks fail in CI

- **GIVEN** a developer commits and pushes with `--no-verify` while a gate fails
- **WHEN** CI runs on the pushed ref
- **THEN** the pre-commit CI step fails on the same gate with the same script invocation

#### Scenario: Single source of hook truth

- **GIVEN** a hook entry is changed in `.pre-commit-config.yaml`
- **WHEN** CI next runs
- **THEN** CI executes the changed entry without any workflow edit

### Requirement: Documented Setup and Legacy Hook Retirement

`CONTRIBUTING.md` SHALL document the hook setup (dependency install, `pre-commit install`, on-demand preflight) and the migration from the retired `.githooks/` mechanism; `.githooks/pre-commit` SHALL be removed.

#### Scenario: Setup is discoverable

- **WHEN** a contributor reads `CONTRIBUTING.md`
- **THEN** it states the dependency install command, the hook install one-liner, and how to run the full preflight on demand

#### Scenario: Legacy hooksPath migration

- **GIVEN** a developer has `core.hooksPath` set to `.githooks` from the old instruction
- **WHEN** they follow the `CONTRIBUTING.md` setup section
- **THEN** it instructs `git config --unset core.hooksPath` before `pre-commit install`

#### Scenario: Installation is verified, not trusted

- **GIVEN** a developer clone where the hooks are not installed
- **WHEN** `scripts/preflight.py` runs
- **THEN** it warns that hooks are missing and prints the install command
- **AND** the warning does not fail the preflight
