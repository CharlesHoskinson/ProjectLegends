## Context

Gate logic lives only in workflow YAML. Ten check-script invocations sit as inline steps in `.github/workflows/sprint2-checks.yml:44-85`; the include-rules check runs in `.github/workflows/module-dag.yml:64-66`; the C11 ABI compile is inlined in the `abi-check` job at `.github/workflows/ci.yml:414-419` (`gcc -std=c11 -Werror` on `include/legends/legends_embed.h`). Locally, the documented loop is bare cmake/ctest and the opt-in hook runs one script (`.githooks/pre-commit:7`). Inventory: `audit-wiki/wiki/entities/Quality Gate Scripts & Hooks.md`; developer-side view: `audit-wiki/wiki/entities/Local Dev Loop.md`. Researched practice: `audit-wiki/wiki/sources/Local Preflight Design (2026-06).md`. Adversarial modifications binding on this change: Recommendation Review rows M-7, A-5, G-5.

Constraints: dev machines are Windows (MSVC, no WSL, possibly no gcc, possibly `py`-launcher-only) and Linux; Python is already the gate-script language and the repo's hard dev dependency; `pyyaml` is the one pip dependency (`sprint2-checks.yml:41-42`).

## Goals / Non-Goals

**Goals:**

- One committed entry point, `scripts/preflight.py`, that runs the same gate commands CI runs.
- CI consumes the entry point: `sprint2-checks.yml`, `module-dag.yml`'s include step, and `ci.yml`'s abi-check body become thin invocations. Local/CI divergence becomes structurally impossible.
- Every gate that can run on the current OS runs; the OS-unreachable residue is named in output, never silently skipped.

**Non-Goals:**

- Changing what any `check_*.py` script checks.
- Wiring the orphaned `check_compiler.py` into the gate set.
- Hook management and tiering (R4, `managed-git-hooks`).
- Preset authoring (R5, `presets-single-source`) — preflight's build/test legs consume presets once they exist; until then they mirror CI's raw configure flags.
- Branch protection (R2) and path-filter redesign (R6).

## Decisions

**D1 — Python script, not a task runner.** The eleven existing gates are Python; CI already runs Python; a justfile/Makefile adds a dialect and a Windows shell problem (`Local Preflight Design (2026-06).md`, practice 5). `scripts/preflight.py` is stdlib + `pyyaml`-transitive only.

**D2 — Subcommand structure mirroring the CI steps.** `preflight scripts` (the ten check-script gates), `preflight abi`, `preflight build [--config NAME]`, `preflight all`. CI jobs call the subcommand matching their current scope, so the rewiring is step-for-step and each workflow keeps its trigger/path semantics. Alternative — one monolithic run — rejected: sprint2 must not start compiling, and abi-check must not run the script suite.

**D3 — Gate registry inside the script, not config.** Each gate entry: name, command, OS-reachability predicate, ordering constraints. The ten CI-run scripts are the registry's fixed core; `check_compiler.py` is deliberately excluded (orphan; wiring it is out of scope). Order constraint encoded explicitly: graphify enrich runs before graphify check, always as a pair (row G-5) — the enrich step builds `graphify-out/projectlegends-enrichment.json` that the check validates, both with `--allow-missing-graphify` exactly as `sprint2-checks.yml:68-85` passes today.

**D4 — ABI gate is detect-and-skip-with-report, not hard-fail (rows A-5, G-5).** Probe for a C11 compiler in order: `gcc`, `clang`, `cl` (MSVC `/TC`). Found: compile `include/legends/legends_embed.h` mirroring `ci.yml:414-419` semantics; the MSVC path is flagged in output as an approximation of CI's gcc invocation. Not found: emit a named SKIPPED line stating CI will run this gate, and exit success for that gate. In CI the gate must hard-fail if no compiler is found — a `--require` flag (used by the `ci.yml` abi-check rewiring) turns skip into failure, so CI can never green on a silent skip.

**D5 — Interpreter via `sys.executable` (row M-7).** Child gate scripts launch with `[sys.executable, "scripts/check_*.py", ...]`, never a bare `python` string, so Windows machines with only the `py` launcher work and venvs propagate.

**D6 — Build/test legs are OS-gated configurations.** Each configuration declares reachability (Linux-toolchain lanes unreachable on Windows and vice versa); `preflight all` runs the reachable set and prints the unreachable residue by name with the reason ("requires gcc-13/clang-18: runs in CI"). The honest-scope contract from `Local Preflight Design (2026-06).md`, practice 2: a Windows developer can never mirror the full four-configuration tier, and pretending otherwise produces silent gaps.

**D7 — Exit-code contract.** Non-zero iff any attempted gate fails. OS-skipped gates do not fail (except under `--require`). All gates run to completion before exit so one run reports all failures; per-gate PASS/FAIL/SKIPPED lines plus a summary table.

**D8 — CI rewiring keeps job names and triggers.** `sprint2-checks.yml`'s ten script steps collapse to one `python scripts/preflight.py scripts` step; `module-dag.yml`'s include step becomes `python scripts/preflight.py scripts --only check_includes`; `ci.yml` abi-check body becomes `python scripts/preflight.py abi --require`. No job renames — R2's required-check names and R8's consolidation are separate changes. The build/test jobs of `ci.yml` are not rewired here; that is R5/R8 territory.

## Risks / Trade-offs

- [Preflight wraps scripts but CI rewiring stalls] → the rewiring tasks are in this change's task list, not deferred; the change is not done until the three workflow files invoke the script. An unconsumed entry point is the documented failure mode (`Local Preflight Design (2026-06).md`, practice 1).
- [`--only` filter reintroduces divergence by letting CI run subsets] → subsets select from the same registry commands; flags and arguments per gate are defined once in the registry, so a subset never varies a command, only scope.
- [MSVC `/TC` accepts code gcc `-std=c11 -Werror` rejects, or vice versa] → the MSVC path is labeled an approximation in output; CI's gcc run remains authoritative; `--require` in CI pins the authoritative compiler.
- [sprint2's per-step granularity in the Actions UI is lost] → preflight prints per-gate PASS/FAIL lines and exits after running all gates, so a single red step still names every failing gate.
- [Preset drift until R5 lands] → build legs carry the raw CI flag sets verbatim with a comment pointing at R5; when `presets-single-source` lands, the legs switch to `cmake --workflow --preset` in that change.

## Migration Plan

1. Land `scripts/preflight.py` with registry, ABI probe, and OS gating; CI untouched (no behavior change).
2. Rewire `sprint2-checks.yml`, `module-dag.yml`, `ci.yml` abi-check in one commit; green run on the same tree proves command equivalence.
3. Rollback: revert the workflow commit; the script is inert without consumers.

## Open Questions

- Whether `preflight build` should fail or warn when CMake presets it expects are absent before R5 lands (current answer: run the raw-flag fallback, print the pointer to R5).
