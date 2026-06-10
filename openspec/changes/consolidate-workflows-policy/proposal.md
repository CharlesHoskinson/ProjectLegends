## Why

The four workflows share a verbatim checkout→configure→build→test skeleton with no `workflow_call` reusable workflow (`ci.yml:63-77` ≈ `pal-ci.yml:38-51` ≈ `module-dag.yml:138-151`); one push to `master` touching `include/**` builds the same tree four ways on Linux and two ways on Windows, with zero `concurrency:` groups anywhere, `permissions:` and `timeout-minutes` only in ci.yml, and 15 jobs running at GitHub's 360-minute default timeout (CI-THESIS.md R8; audit-wiki/wiki/entities/CI Workflows (GitHub Actions).md; Recommendation Review M-1, A-2, M-8, A-4). Skeleton drift is live: pal-ci's `abi-c-compile` runs the `legends_abi_test` binary that ci.yml's `abi-check` lacks, while both compile the same C11 surface.

## What Changes

- **Hygiene first, zero prerequisites** (Recommendation Review A-4, M-8): `timeout-minutes` on every job in `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`; `permissions: contents: read` at workflow top in the three files that lack it; a `concurrency:` group with `cancel-in-progress` for PR refs in all four workflows.
- **Reusable build workflow**: factor the shared skeleton into `.github/workflows/build-and-test.yml` (`on: workflow_call`, typed inputs: runner image, preset/configuration, ctest arguments); thin callers declare one matrix cell per distinct configuration. Deliberate config deltas are preserved as distinct cells, never collapsed: PAL backends (`PAL_BACKEND_HEADLESS`, SDL2, SDL3), `LEGENDS_LIBRARY_MODE=ON` (sprint2), `LEGENDS_USE_IPC=ON` (linux-ipc) (Recommendation Review A-2 binding).
- **Duplicate build jobs retired**: the per-push four-way-Linux/two-way-Windows duplication collapses to one cell per configuration; module-dag's `build-linux`/`build-windows` are nightly-only and fold into the same reusable workflow at their existing tier (Recommendation Review A-2).
- **ABI fold**: pal-ci's `abi-c-compile` folds into ci.yml's `abi-check`, keeping the superset — the runtime `legends_abi_test` run plus the `test_legends_abi.c` compile (`pal-ci.yml:237-245`) that `ci.yml:414-419` lacks, alongside the existing `gcc -std=c11 -fsyntax-only` header check (Recommendation Review M-1).
- **Required-check name sync**: any job rename produced by consolidation updates `docs/ci/master-ruleset.json` and re-applies the ruleset in the same change, per the merge-gating name-sync rule (`master-ruleset-required-checks`, CI-THESIS.md R2/R8).
- Sequencing: the hygiene group lands immediately and independently (adoption order step 1); the reusable-workflow consolidation lands after `presets-single-source` (R5) so cells are preset-named, and after `master-ruleset-required-checks` (R2) so the name-sync rule has a ruleset to update (adoption order step 6).

## Capabilities

### New Capabilities
- `workflow-hygiene`: every job carries an explicit timeout; every workflow declares least-privilege permissions and a concurrency group — independent of consolidation, lands first.
- `workflow-consolidation`: one reusable `workflow_call` build skeleton; one matrix cell per distinct configuration with config deltas preserved; the ABI check as a single superset job; required-check names synchronized with the ruleset on rename.

### Modified Capabilities

(none — `openspec/specs/ci-stabilization` defines which lanes are primary vs optional; consolidation re-plumbs how jobs are defined without changing which validations run at which tier. The `merge-gating` name-sync requirement from `master-ruleset-required-checks` is complied with, not modified.)

## Impact

- `.github/workflows/ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml` — hygiene keys added; build jobs rewritten as reusable-workflow calls.
- `.github/workflows/build-and-test.yml` — new reusable workflow (must live directly in `.github/workflows/`; subdirectories unsupported for `workflow_call`).
- `docs/ci/master-ruleset.json` + live ruleset — updated in the same change if consolidation renames any of the five required checks.
- Sequencing: hygiene group has zero prerequisites; consolidation group depends on `presets-single-source` (R5) and `master-ruleset-required-checks` (R2).
