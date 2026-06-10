# Tasks

## 1. Prerequisite Check

- [ ] 1.1 Confirm `preflight-gate-entrypoint` (R3) is merged and note the exact `scripts/preflight.py` subcommand for the script-suite tier.

## 2. Hook Configuration

- [ ] 2.1 Add `pre-commit` (pinned) to `requirements-dev.txt`.
- [ ] 2.2 Create `.pre-commit-config.yaml` with `default_install_hook_types: [pre-commit, pre-push]` and a single `repo: local` block.
- [ ] 2.3 Add commit-tier entries (`language: system`, `pass_filenames: false`, `files:` globs): `python scripts/check_includes.py --path .`, `python scripts/check_conflict_markers.py --path .`, `python scripts/check_case_collisions.py`.
- [ ] 2.4 Add the pre-push entry (`stages: [pre-push]`, `always_run: true`, `pass_filenames: false`) invoking the preflight script-suite subcommand from 1.1.
- [ ] 2.5 Verify locally on Windows and Linux: `pre-commit install` wires both hooks; a staged include violation blocks commit; a failing check script blocks push; a commit touching no filtered files skips the commit tier.
- [ ] 2.6 Verify no `cmake`/`ctest` invocation occurs in any hook tier (inspect config and observe a push run).

## 3. Legacy Hook Retirement

- [ ] 3.1 Delete `.githooks/pre-commit` (and `.githooks/` if empty).
- [ ] 3.2 Add the installation probe to `scripts/preflight.py`: warn and print the install one-liner when `.git/hooks/pre-commit` or `.git/hooks/pre-push` is absent; never fail on it.

## 4. Documentation

- [ ] 4.1 Add a Setup section to `CONTRIBUTING.md`: `pip install -r requirements-dev.txt`, `pre-commit install`, on-demand full preflight command, and what each tier runs.
- [ ] 4.2 Add the migration note: `git config --unset core.hooksPath` before `pre-commit install` for clones using the retired `.githooks/` instruction.
- [ ] 4.3 Remove or update any references to `.githooks` elsewhere in repo docs (`grep -r githooks` excluding `llm-wiki/` and `audit-wiki/`).

## 5. CI Parity

- [ ] 5.1 In the R3-rewired script-gate workflow, replace the preflight script-suite step with `pre-commit run --all-files --hook-stage pre-push` and add `pre-commit run --all-files`, after the dev-dependency install step.
- [ ] 5.2 Confirm gate coverage is unchanged: every check script that ran before the swap still runs in the new steps (compare against the inventory in audit-wiki Quality Gate Scripts & Hooks).
- [ ] 5.3 Push a branch with a deliberate gate failure and `--no-verify`; verify the CI pre-commit step fails on the same gate; revert.

## 6. Validation

- [ ] 6.1 Run `pre-commit run --all-files` and `pre-commit run --all-files --hook-stage pre-push` clean at HEAD.
- [ ] 6.2 Run `python scripts/check_conflict_markers.py --path .` and `git diff --check`.
- [ ] 6.3 Run `openspec validate managed-git-hooks --strict`.
