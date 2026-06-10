---
type: entity
entity_kind: system
aliases: ["check scripts", "scripts/check_*.py", ".githooks/pre-commit"]
tags: [entity, type/entity, topic/audit, topic/ci, topic/quality-gates]
created: 2026-06-10
updated: 2026-06-10
status: draft
related:
  - "[[CI Gate Coverage Map]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[CI Workflows (GitHub Actions)]]"
  - "[[Local Dev Loop]]"
---

# Quality Gate Scripts & Hooks

Inventory of the Python quality-gate scripts under `scripts/`, the single git hook under `.githooks/`, the openspec and graphify gates, and the baseline file they enforce against. Current state only; where each gate fires is cross-mapped in [[CI Gate Coverage Map]], and the workflows themselves are described in [[CI Workflows (GitHub Actions)]] and [[Build & CI System (Project Legends)]]. The developer-side view (what runs locally vs in CI) is [[Local Dev Loop]].

## Check-script inventory

Eleven `check_*.py` scripts exist under `scripts/` (directory listing of `scripts/`). Ten run in CI; one (`check_compiler.py`) is invoked by no workflow and no hook.

| Script | What it checks | CI invocation (workflow → job → line) | Pre-commit hook? |
|---|---|---|---|
| `scripts/check_includes.py` | Module-boundary include rules: public headers may not include `../src/`, no `../../` cross-module traversal, `dosbox/`/`aibox/` path convention for engine public API (`scripts/check_includes.py:2-12`) | `module-dag.yml` → `include-rules` → run `python scripts/check_includes.py --path . --verbose` (`.github/workflows/module-dag.yml:64-66`) | **Yes** — the only script the hook runs (`.githooks/pre-commit:7`) |
| `scripts/check_globals.py` | Validates `engine/globals_registry.yaml`: statistics section matches actual counts, comparison against baseline to prevent regressions and unapproved additions, migration-progress report (`scripts/check_globals.py:2-12`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:50-51` | No |
| `scripts/check_current_context.py` | Forbids `current_context()` in production code; allowed only in tests, `*_compat.cpp`, `dosbox_context.cpp`, `machine_context.cpp`, `error_model.cpp`; headers may declare but never use it inline (`scripts/check_current_context.py:2-13, 23-40`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:44-45` | No |
| `scripts/check_migration_status.py` | Migration status in `globals_registry.yaml` may only improve vs baseline, never regress (e.g. migrated → pending) (`scripts/check_migration_status.py:2-9`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:47-48` | No |
| `scripts/check_gsl_lite_usage.py` | Seven gsl-lite contract rules: no legacy `<gsl/gsl-lite.hpp>` header, no compatibility mode, no gsl-lite types in the public C ABI header, no bare `gsl_lite::` namespace, no bare `assert()` in modern aibox code, no `gsl_lite::span`/`gsl_lite::byte` in C++23 code (`scripts/check_gsl_lite_usage.py:2-14`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:53-54` | No |
| `scripts/check_conflict_markers.py` | Recursive scan for unresolved git merge-conflict markers in source, config, and build files (`scripts/check_conflict_markers.py:2-9`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:56-57` | No |
| `scripts/check_case_collisions.py` | Case-insensitive filename collisions among git-tracked paths (Windows/macOS checkout hazard) (`scripts/check_case_collisions.py:2-7`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:59-60` | No |
| `scripts/check_openspec_staleness.py` | Flags completed OpenSpec changes (all tasks checked, none unchecked) that remain active under `openspec/changes/` instead of being archived; four `PROTECTED_ACTIVE_PREFIXES` change families are exempt by directive (`scripts/check_openspec_staleness.py:2, 11-16, 81-94`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:62-63` | No |
| `scripts/check_capability_matrix.py` | Public C API capability truth matrix: every `LEGENDS_API` export has a manifest entry, the Markdown table stays in sync with the JSON source of truth, proxy-supported APIs are backed by an engine-host dispatcher case (`scripts/check_capability_matrix.py:2-9`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:65-66` | No |
| `scripts/check_graphify_enrichment.py` | Validates the Graphify enrichment overlay (`graphify-out/projectlegends-enrichment.json`) against repo sources: schema, graph integrity, API inventory, capability sync, IPC parity/schema, test evidence, CMake, RuntimeHost adoption, merged graph — selectable via `--gate` (`scripts/check_graphify_enrichment.py:42, 673-687`) | `sprint2-checks.yml` → `globals-registry` → `.github/workflows/sprint2-checks.yml:78-85` | No |
| `scripts/check_compiler.py` | Detects installed compilers and probes C++23 feature support; outputs JSON with discovered compilers, compile probes, and upgrade hints (`scripts/check_compiler.py:2-7`) | **Not invoked by any workflow.** Grep across `.github/workflows/` finds no reference; the only repo mention is a process doc (`docs/superpowers/plans/2026-06-08-end-to-end-review-plan.md:58`) | No |

All ten CI-invoked steps above sit in path-filtered workflows: `sprint2-checks.yml` fires only on changes to `CMakeLists.txt`, `CMakePresets.json`, `docs/architecture/**`, `engine/**`, `src/**`, `include/**`, `scripts/**`, `tests/**`, itself, or `.github/baseline_globals.yaml` (`.github/workflows/sprint2-checks.yml:3-27`); `module-dag.yml` fires on `include/**`, `engine/include/**`, `src/**`, `engine/src/**`, `cmake/**`, the CMakeLists files, `scripts/check_includes.py`, or itself (`.github/workflows/module-dag.yml:18-45`). Path-family consequences (e.g. `openspec/**` never triggers the staleness check) are tabulated in [[CI Gate Coverage Map]].

## The pre-commit hook

`.githooks/pre-commit` is a 14-line bash script. It runs exactly one command — `python scripts/check_includes.py --path .` with stdout/stderr discarded — and rejects the commit with a pointer to re-run the script verbosely if it fails (`.githooks/pre-commit:7-11`). It runs none of the other ten check scripts, no tests, and no build.

The hook is opt-in: it lives in `.githooks/`, not `.git/hooks/`, and only takes effect after a developer runs `git config core.hooksPath .githooks`. That requirement is stated solely in a comment inside the hook itself ("Install: git config core.hooksPath .githooks", `.githooks/pre-commit:3`).

**Documentation status:** a search of `README.md`, `CONTRIBUTING.md`, `AGENTS.md`, and `docs/` for `hooksPath`, `pre-commit`, and `githooks` finds no developer-facing documentation of hook installation. The only matches outside the hook file are this audit's own planning documents (`docs/superpowers/plans/2026-06-10-cicd-audit.md:62, 179`; `docs/superpowers/specs/2026-06-10-cicd-audit-design.md:24, 69`). `CONTRIBUTING.md` contains no occurrence of `check_`, `scripts/`, or hook setup (grep over `CONTRIBUTING.md`). Hook installation is therefore undocumented for contributors.

## The openspec validation gate

No workflow runs the `openspec` CLI. Grep for `openspec` across `.github/workflows/` matches only the staleness step (`.github/workflows/sprint2-checks.yml:62-63`), which is a Python scan of `openspec/changes/*/tasks.md` checkbox counts — it validates archival hygiene, not spec content (`scripts/check_openspec_staleness.py:36-60`). `openspec validate --strict` exists in the repo only as an agent-process convention: in superpowers process docs and in OpenSpec change task lists (`docs/superpowers/specs/2026-06-10-cicd-audit-design.md:42`; `openspec/changes/runtimehost-adoption-next-slice/tasks.md:36`). The README architecture diagram lists "OpenSpec" among the "Quality and architecture gates" (`README.md:91`). Additionally, `openspec/**` appears in no workflow's `paths:` filter, so changes under `openspec/` never trigger even the staleness check by themselves (`.github/workflows/sprint2-checks.yml:3-27`; see [[CI Gate Coverage Map]]).

## The graphify enrichment gate (sprint2-checks.yml)

Two consecutive steps in the `globals-registry` job:

1. **Enrich (build) step** — `scripts/enrich_graphify_projectlegends.py` builds the enrichment overlay, merged graph, and Markdown report (`.github/workflows/sprint2-checks.yml:68-76`). It passes `--allow-missing-graphify` (`.github/workflows/sprint2-checks.yml:76`), which "use[s] an empty base graph when graphify-out/graph.json is unavailable, intended for CI source-only validation" (`scripts/enrich_graphify_projectlegends.py:1457-1461`).
2. **Check step** — `scripts/check_graphify_enrichment.py` validates the overlay with `--strict --strict-tests fail --allow-missing-graphify` (`.github/workflows/sprint2-checks.yml:78-85`; flags at lines 83, 84, 85). `--strict` runs "all strict source consistency gates" and promotes warnings to failure (`scripts/check_graphify_enrichment.py:660, 630`); `--strict-tests fail` makes missing static test evidence a failure rather than a warning (`scripts/check_graphify_enrichment.py:666-671`); `--allow-missing-graphify` again permits "source-only validation when Graphify graph/manifest are unavailable" (`scripts/check_graphify_enrichment.py:661-665`).

Net behavior: both steps tolerate the absence of a checked-in Graphify graph (the `graphify-out/` artifacts are not required to exist in CI); strict enforcement applies to the source-derived overlay — API inventory vs `legends_embed.h`, capability-matrix sync, IPC dispatcher parity, and test-evidence presence (`scripts/check_graphify_enrichment.py:673-687` gate list).

## baseline_globals.yaml

`.github/baseline_globals.yaml` is the frozen baseline of the DOSBox-X global-state registry: it tracks ~70 global/static variables pending migration to `DOSBoxContext` for library-mode multi-instance support, with a stated CI contract of "no new entries without review", "migration_status only improves", and "no regressions" (`.github/baseline_globals.yaml:1-18`).

Consumers:
- `scripts/check_globals.py` — compares the live `engine/globals_registry.yaml` against it to block regressions and unapproved additions; default lookup paths `.github/baseline_globals.yaml` then `baseline_globals.yaml` (`scripts/check_globals.py:86, 152-153`); on failure it instructs "Update .github/baseline_globals.yaml after review" (`scripts/check_globals.py:242`).
- `scripts/check_migration_status.py` — reads the same file as the per-entry migration-status baseline (`scripts/check_migration_status.py:47-55, 92`).
- `sprint2-checks.yml` — lists the file in both `push` and `pull_request` path filters, so editing the baseline itself re-triggers the validating workflow (`.github/workflows/sprint2-checks.yml:15, 27`).

## Related

- [[CI Gate Coverage Map]] — which path families these gates do and do not fire on
- [[CI Workflows (GitHub Actions)]] — the four workflows hosting the gate steps
- [[Build & CI System (Project Legends)]] — parent subsystem assessment
- [[Local Dev Loop]] — which of these gates a developer ever sees before push
