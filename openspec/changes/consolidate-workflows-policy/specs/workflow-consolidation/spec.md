## ADDED Requirements

### Requirement: The build skeleton lives in one reusable workflow
A reusable workflow `.github/workflows/build-and-test.yml` SHALL declare `on: workflow_call` with typed inputs (at minimum: runner image, build configuration, ctest arguments) and SHALL own the checkout→configure→build→test sequence. Build jobs in `ci.yml`, `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` SHALL invoke it via `uses: ./.github/workflows/build-and-test.yml` instead of carrying inline copies of the skeleton.

#### Scenario: Skeleton change
- **WHEN** the build sequence needs a change (e.g. a new cache step or configure flag plumbing)
- **THEN** the change is made once in `build-and-test.yml` and applies to every calling job

#### Scenario: Inline skeleton reintroduced
- **WHEN** a workflow change adds a job that hand-rolls checkout→configure→build→test instead of calling the reusable workflow
- **THEN** review rejects it unless the job documents why the reusable workflow cannot express it

### Requirement: One matrix cell per distinct configuration; deltas are never dropped
Each distinct build configuration SHALL be exactly one matrix cell calling the reusable workflow. Deliberate configuration deltas SHALL each survive as a distinct cell: PAL backend selection (headless, SDL2, SDL3), `LEGENDS_LIBRARY_MODE=ON`, `LEGENDS_USE_IPC=ON`. Jobs that duplicate an existing cell with no configuration delta SHALL be retired.

#### Scenario: Per-push duplication collapsed
- **WHEN** a push triggers the consolidated workflows
- **THEN** each distinct configuration builds once — the prior four-way Linux and two-way Windows rebuilds of identical configurations do not recur

#### Scenario: Delta cell preserved
- **WHEN** consolidation maps the old jobs onto matrix cells
- **THEN** the IPC, library-mode, and each PAL-backend configuration each appear as a cell, verified by a before/after configuration matrix in the change

#### Scenario: No-delta duplicate retired
- **WHEN** an old job (e.g. pal-ci `windows-build`) builds the same configuration as a surviving cell with no flag difference
- **THEN** the old job is removed and the surviving cell is the single source of that verdict

### Requirement: Job tiers are unchanged by consolidation
A job's trigger tier (every-push, PR, nightly/dispatch, tag) SHALL be the same before and after its conversion to a reusable-workflow call. Nightly-only build jobs (module-dag `build-linux`/`build-windows`, SDL3 and macOS lanes) SHALL remain nightly/dispatch-gated.

#### Scenario: Nightly job stays nightly
- **WHEN** module-dag's build jobs are converted to reusable-workflow calls
- **THEN** they still run only on schedule or `workflow_dispatch`, never on plain pushes or PRs

### Requirement: A single ABI job carries the superset of both prior checks
The `C ABI Verification` job in `ci.yml` SHALL (1) build and run the `legends_abi_test` binary, (2) compile `test_legends_abi.c`, and (3) run the `gcc -std=c11 -fsyntax-only` header check. The pal-ci `abi-c-compile` job SHALL be removed. The surviving job SHALL run unconditionally on every PR (no workflow- or job-level path filter), because it is a required check.

#### Scenario: ABI regression caught at runtime
- **WHEN** a change breaks the C ABI in a way only the runtime `legends_abi_test` detects
- **THEN** `C ABI Verification` fails — the runtime check formerly exclusive to pal-ci is part of the required job

#### Scenario: Fold does not narrow coverage
- **WHEN** `abi-c-compile` is removed
- **THEN** every check it performed (runtime test, C test-file compile) exists in `C ABI Verification`, verified step-for-step in the removing PR

### Requirement: Required-check names stay synchronized through consolidation
If consolidation changes the reported check context of any required check (`Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`), the same change SHALL update `docs/ci/master-ruleset.json` and re-apply the ruleset per the `merge-gating` name-sync rule. The actually reported context string (including any `caller / callee` nesting from reusable-workflow calls) SHALL be read from a live PR run before the ruleset is updated.

#### Scenario: Rename with ruleset sync
- **WHEN** a consolidated job reports under a new context string
- **THEN** `docs/ci/master-ruleset.json` carries the new string and the ruleset is re-applied in the same change, so no merge window has a never-reporting required check

#### Scenario: Name preserved
- **WHEN** a consolidated job can keep its prior expanded name via the job `name:` key
- **THEN** it does, and the ruleset is untouched

### Requirement: Consolidation is sequenced after presets and the ruleset
The reusable-workflow conversion SHALL NOT land before `presets-single-source` (R5) — matrix cells are named by preset, not raw flag lists — and SHALL NOT land before `master-ruleset-required-checks` (R2), so the name-sync rule has a live ruleset to update. The hygiene requirements (`workflow-hygiene`) are exempt and land independently first.

#### Scenario: Premature consolidation attempt
- **WHEN** the reusable-workflow conversion is proposed while R5 or R2 is unmerged
- **THEN** the proposal is deferred; only the hygiene group may land
