# Preflight Gate Entry Point

## Why

No single command reproduces the mandatory CI tier locally: the documented loop covers 3 of 14 mandatory gates, the opt-in hook adds one more, and the other gates run for the first time after push (`audit-wiki/wiki/entities/Local Dev Loop.md`). Gate logic lives only in workflow YAML (`.github/workflows/sprint2-checks.yml:44-85`, `module-dag.yml:64-66`, `ci.yml:414-419`), so nothing local can call it and local/CI divergence is unbounded — CI-THESIS.md R3.

## What Changes

- Add `scripts/preflight.py`: one entry point wrapping the ten CI-run check scripts (`check_includes`, `check_current_context`, `check_migration_status`, `check_globals`, `check_gsl_lite_usage`, `check_conflict_markers`, `check_case_collisions`, `check_openspec_staleness`, `check_capability_matrix`, graphify enrich + strict check), the C11 ABI compile of `include/legends/legends_embed.h`, and the OS-reachable build/test configurations.
- OS-gate the ABI compile: detect a C11 compiler and use it; on gcc-less MSVC-only Windows machines report the gap explicitly instead of hard-failing or silently skipping (Recommendation Review rows A-5, G-5).
- Run the graphify enrich-then-check pair in order, enrich before check (row G-5).
- Invoke gate scripts via `sys.executable`, never a bare `python` shell-out, so the Windows `py` launcher case works (row M-7).
- Rewire CI to consume the entry point — `sprint2-checks.yml`'s script steps, `module-dag.yml`'s include-rules step, and `ci.yml`'s abi-check body each become a thin `preflight` invocation. Gate logic leaves YAML; CI running the same command developers run is the point of the change — an entry point CI does not consume is the documented failure mode (`audit-wiki/wiki/sources/Local Preflight Design (2026-06).md`, practice 1).

## Capabilities

### New Capabilities

- `preflight-gate`: single committed gate entry point — script-gate coverage, OS-gated ABI compile, ordered graphify pair, OS-reachable build/test legs with explicitly named residue, launcher portability, and CI consumption of the same commands.

### Modified Capabilities

None. Existing specs under `openspec/specs/` (build-hygiene, ci-stabilization, etc.) gain no requirement changes; this change adds gate infrastructure around the existing scripts without altering what any script checks.

## Impact

- New: `scripts/preflight.py`.
- Modified: `.github/workflows/sprint2-checks.yml` (script steps collapse into preflight invocations), `.github/workflows/module-dag.yml` (include-rules step), `.github/workflows/ci.yml` (abi-check job body).
- Unchanged: the eleven `scripts/check_*.py` themselves; `check_compiler.py` stays un-wired (orphan, `audit-wiki/wiki/entities/Quality Gate Scripts & Hooks.md`).
- Dependencies: `pyyaml` (already pip-installed in CI, `sprint2-checks.yml:41-42`). Build/test legs consume CMake presets; preset coverage itself is the `presets-single-source` change (R5) — preflight degrades to raw configure commands until that lands.
- Downstream: `managed-git-hooks` (R4) tiers its hooks over this entry point.
