# Proposal: Managed Git Hooks

## Why

Local gate enforcement is one opt-in bash hook running one of eleven check scripts, installable only via a `git config core.hooksPath .githooks` instruction that exists solely as a comment inside the hook itself; no contributor document mentions hooks or any `scripts/check_*.py` (Quality Gate Scripts & Hooks; `.githooks/pre-commit:3,7`). The other ten checks run only as inline CI YAML steps after push, so a developer first learns of a mandatory-gate failure from a red remote run. CI-THESIS R4 (A-6, G-12) directs replacing this with a committed hook-manager config, tiered, documented, and mirrored in CI.

## What Changes

- Add a committed `.pre-commit-config.yaml` using `repo: local` hooks (manager choice justified in design.md) covering the check scripts that today run only in CI.
- Tier the hooks: staged-file-triggered fast checks at commit; the full check-script suite at push via the preflight entry point from `preflight-gate-entrypoint` (R3). Per Recommendation Review A-6, the push tier runs the script suite only — no configure/build step at push. Full preflight stays an on-demand command.
- **BREAKING (local workflow):** retire `.githooks/pre-commit` and the `core.hooksPath` mechanism; developers who set `core.hooksPath` must unset it and run the documented install command.
- Document setup in `CONTRIBUTING.md`: bootstrap, hook install one-liner, on-demand preflight, and the unset-`core.hooksPath` migration note.
- Run the identical committed hook config as a CI step, so skipping hooks locally only delays the same failure.

## Capabilities

### New Capabilities

- `managed-git-hooks`: committed, tiered hook-manager configuration; hook installation documented and verifiable; CI executes the identical config.

### Modified Capabilities

None. No existing spec under `openspec/specs/` covers hooks or local gate enforcement.

## Impact

- `.pre-commit-config.yaml` — new, committed hook config (commit and push tiers).
- `.githooks/pre-commit` — removed.
- `CONTRIBUTING.md` — setup section: bootstrap, hook install, preflight, migration note.
- `requirements-dev.txt` — add the hook manager as a pinned dev dependency.
- `.github/workflows/sprint2-checks.yml` (or its R3-rewired successor) — replace inline script steps with one step running the committed hook config.
- Depends on `preflight-gate-entrypoint` (R3): the push tier invokes the preflight script-suite tier; this change does not define gate logic, only when it runs locally.

## Out of Scope

- Gate logic and the preflight CLI itself (R3, `preflight-gate-entrypoint`).
- CMake preset work (R5, `presets-single-source`); no build/test configuration runs in any hook tier.
- Branch protection (R2) and workflow consolidation (R8).
