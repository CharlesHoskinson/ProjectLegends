# Design: Managed Git Hooks

## Context

`.githooks/pre-commit` is a 14-line bash script running exactly one of the eleven `scripts/check_*.py` gates (`check_includes.py`), opt-in via `git config core.hooksPath .githooks`, with the install instruction only a comment in the hook file; `CONTRIBUTING.md`, `README.md`, and `AGENTS.md` mention no hook and no check script (Quality Gate Scripts & Hooks, audit-wiki). The remaining ten checks run only as inline YAML steps in `sprint2-checks.yml` and `module-dag.yml`. The bash-only hook depends on Git-for-Windows' bundled sh and a `python` (not `py`) launcher on PATH (Local Preflight Design, practice 5). The team develops on Windows (MSVC, no WSL) and Linux.

`preflight-gate-entrypoint` (R3) creates `scripts/preflight.py` wrapping the ten CI-run check scripts, the ABI compile, and the OS-reachable build/test configurations, and rewires the workflows to invoke it. This change supplies the local trigger layer on top of it; it defines no gate logic.

Binding modification from Recommendation Review A-6: the pre-push tier runs the script suite only — no "one workflow preset at push" stage, because a full configure+build per push is heavy and strict-tier `-Werror` currently breaks local Windows builds.

## Goals / Non-Goals

**Goals:**
- One committed hook config that wires commit-time and push-time gates on a fresh clone with one documented install command.
- Tiers are prefixes of the same command set, never variant flags or variant scripts (Local Preflight Design, practice 4 reconciliation).
- CI runs the identical committed config, so bypassing hooks locally only moves the failure to CI.
- Retire the `.githooks/` + `core.hooksPath` mechanism with a documented migration step.

**Non-Goals:**
- Gate logic, preflight CLI, or check-script changes (R3).
- Any configure/build/test execution in a hook tier (A-6 modification).
- CMake presets (R5), branch protection (R2), workflow consolidation (R8).
- Hook-managed formatters/linters not already in `scripts/`.

## Decisions

### D1: pre-commit with `repo: local` hooks, not lefthook

Both are Windows-native and both fix the two defects of the current setup — single-check coverage and undocumented opt-in install (Recommendation Review G-12; Local Preflight Design, practice 3). pre-commit wins here:

- Every gate is already a Python script in `scripts/`, and CI already pip-installs the dev dependency set (`sprint2-checks.yml:41-42`); pre-commit is itself a pip package, so `requirements-dev.txt` remains the single dependency channel. Lefthook requires a separate binary install (winget/scoop/brew) per developer and per CI job.
- pre-commit being Python makes a working `python` on PATH a precondition of the manager itself, which defuses the `python`-vs-`py` launcher trap that breaks bare hooks on Windows (Recommendation Review M-7; Local Preflight Design, practice 5).
- Lefthook's distinguishing advantage is parallel execution for build-heavy pre-push tiers (Local Preflight Design, practice 3 conflict note). A-6 removes builds from the push tier, so that advantage is moot; the push tier is one serial preflight invocation either way.
- `repo: local` with `language: system` runs the repo's own scripts directly — no remote hook repos, no per-hook environments, no network on install (pre-commit.com, "Repository-local hooks").

### D2: Tier layout

| Tier | Trigger | Runs | Bound |
|---|---|---|---|
| commit | `pre-commit` hook, fires when staged files match `files:` globs | `check_includes.py`, `check_conflict_markers.py`, `check_case_collisions.py` | seconds |
| push | `pre-push` hook, `always_run: true` | the preflight script-suite tier (all ten CI-run check scripts, enrich-then-check ordering owned by preflight) | minutes |
| on demand | developer runs preflight directly | full preflight: script suite + ABI check + OS-reachable build/test configurations | minutes, documented |

- Commit-tier entries set `pass_filenames: false`: the check scripts take `--path .`, not file lists, and are repo-wide fast; the `files:` glob only gates whether the hook fires. This keeps tiers byte-identical to CI invocations rather than introducing staged-file-list variants of the scripts.
- The push tier is a single hook entry invoking the script-suite subcommand of `scripts/preflight.py` (exact CLI per R3). Hooks never enumerate scripts themselves — coverage updates land in preflight once and every tier inherits them.
- On demand is not a hook stage; it is the R3 preflight command, documented in `CONTRIBUTING.md`.
- `default_install_hook_types: [pre-commit, pre-push]` in the config so a single `pre-commit install` wires both hooks (pre-commit.com).

### D3: CI runs the committed config

The R3-rewired script-gate workflow step becomes `pre-commit run --all-files --hook-stage pre-push` (executes the same preflight script-suite entry the local pre-push hook runs) plus `pre-commit run --all-files` (exercises the commit-tier entries). CI thereby executes the config file itself, not a parallel transcription of it — local/CI divergence in the hook layer becomes structurally impossible (Local Preflight Design, practice 1; pre-commit.com "adding pre-commit run --all-files as a CI step"). `git commit --no-verify` and `git push --no-verify` remain possible and merely defer the identical failure to CI.

### D4: Retire `.githooks/`, verify installation

- Delete `.githooks/pre-commit`; its one check is covered by the commit tier.
- `pre-commit install` refuses to run while `core.hooksPath` is set, so the migration note in `CONTRIBUTING.md` leads with `git config --unset core.hooksPath`.
- Installation is verified, not trusted (Local Preflight Design, practice 6): `scripts/preflight.py` probes `.git/hooks/pre-commit` / `.git/hooks/pre-push` and prints the install one-liner when absent (warning, not failure — CI checkouts have no hooks installed). Coordinate this small extension with R3.

## Risks / Trade-offs

- [R3 not landed: push tier has no entry point] → Sequence strictly after `preflight-gate-entrypoint` per CI-THESIS adoption order (R5 → R3 → R4); no interim script enumeration in the hook config.
- [Hook-stage names vs CI step drift if R8 consolidates workflows] → CI calls `pre-commit run`, never the scripts; workflow consolidation can move the step but cannot fork its content.
- [pre-commit adds a YAML config dialect beside CMakePresets.json and the workflows] → Accepted; the config is declarative trigger wiring only, all logic stays in `scripts/`.
- [Push-tier latency discourages pushing] → Script suite only (A-6); builds are excluded by design and run on demand or in CI.
- [Developers skip hooks with `--no-verify`] → D3: CI runs the identical config; R2's ruleset makes that CI verdict binding.
- [`check_graphify_enrichment.py` requires the enrich step first (G-5)] → Ordering lives inside preflight's script-suite tier (R3), not in hook entries.

## Migration Plan

1. Land config + docs + dependency pin in one commit after R3 merges.
2. CI step swap in the same change: inline script steps removed only where the pre-commit step replaces them, keeping gate coverage continuous.
3. Developers: `git config --unset core.hooksPath` (if set), `pip install -r requirements-dev.txt`, `pre-commit install`.
4. Rollback: revert the commit; `.githooks/pre-commit` restores with it. No server-side state involved.

## Open Questions

- Exact preflight script-suite subcommand name is owned by R3; the hook entry tracks whatever `scripts/preflight.py` exposes.
