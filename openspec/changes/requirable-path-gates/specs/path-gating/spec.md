## ADDED Requirements

### Requirement: Gate workflows trigger without workflow-level path filters
`module-dag.yml` and `sprint2-checks.yml` SHALL declare no `paths:` (or `paths-ignore:`) key on their `push` or `pull_request` triggers. Path scoping SHALL be expressed only at job level.

#### Scenario: PR not touching any gate-relevant path still reports
- **WHEN** a pull request to `master` changes only `docs/README-extras.md`
- **THEN** `module-dag.yml` and `sprint2-checks.yml` both trigger, and each gate job reports a conclusion (skipped), leaving no check Pending

#### Scenario: Required check on a non-matching PR
- **WHEN** a gate job from these workflows is registered as a required status check and a PR changes none of its relevant paths
- **THEN** the job's skipped conclusion satisfies the required check and the PR is mergeable on its other checks

### Requirement: Changed paths are classified by a first job that gates downstream jobs
Each workflow that scopes work by path (`ci.yml`, `module-dag.yml`, `sprint2-checks.yml`) SHALL run a `changed-paths` job first, which SHALL invoke `scripts/ci_changed_paths.py` to classify the changed files into named path families and SHALL expose one boolean output per family. Downstream jobs SHALL skip via `if:` conditions on those outputs combined with `needs: [changed-paths]`. The classification logic SHALL live in the script, not in workflow YAML.

#### Scenario: Matching change runs the gate
- **WHEN** a PR changes `src/legends_ipc/transport.cpp`
- **THEN** `changed-paths` sets the `ipc` family true and the downstream gate jobs run

#### Scenario: Non-matching change skips the gate with a reported conclusion
- **WHEN** a PR changes only `openspec/changes/foo/proposal.md`
- **THEN** `multi-instance-tests` is skipped via its `if:` condition and reports skipped rather than not appearing

#### Scenario: Classifier failure fails closed
- **WHEN** the `changed-paths` job errors
- **THEN** the workflow run fails visibly; no downstream gate silently passes

### Requirement: Unrecognized paths default to run-everything
Any changed file that matches no entry in the path-family map SHALL set every family output true. Events without a usable diff base — `schedule`, `workflow_dispatch`, tag pushes, and pushes whose `before` SHA is unusable (all-zeros or unreachable) — SHALL also set every output true.

#### Scenario: New unmapped directory
- **WHEN** a PR adds `third_party/newlib/foo.c` and the family map has no rule for `third_party/**`
- **THEN** every gate job in the triggered workflows runs

#### Scenario: Force push with unusable before-SHA
- **WHEN** a push event's `github.event.before` cannot be diffed against
- **THEN** classification is bypassed and every gate job runs

### Requirement: Path families align with the module manifest
The family map in `scripts/ci_changed_paths.py` SHALL be derived by hand from the module boundaries in `cmake/ModuleManifest.cmake` and SHALL cite it. In particular: `openspec/**` SHALL trigger the sprint2 `globals-registry` job (owner of `scripts/check_openspec_staleness.py`), and `cmake/**` SHALL trigger both `globals-registry` and module-dag's `cmake-dag` job.

#### Scenario: openspec-only change reaches its staleness gate
- **WHEN** a PR changes only files under `openspec/`
- **THEN** `globals-registry` runs (and `check_openspec_staleness.py` executes), where previously no workflow triggered on `openspec/**`

#### Scenario: cmake-only change reaches the sprint2 checks
- **WHEN** a PR changes only `cmake/ModuleDAG.cmake`
- **THEN** `cmake-dag` and `globals-registry` both run

### Requirement: ci.yml build jobs skip only on docs-only changes
The `ci.yml` jobs in the required set (`linux`, `linux-ipc`, `windows`, `coverage`, `abi-check`) and the conditional `sanitizers`/`fuzz` jobs SHALL skip only when every changed file is in the docs-only family (`docs/**` outside `docs/architecture/**`, `audit-wiki/**`, `llm-wiki/**`, root-level `*.md`). Any other family SHALL run them.

#### Scenario: Wiki-only PR skips builds
- **WHEN** a PR changes only `audit-wiki/wiki/maps/CI Gate Coverage Map.md`
- **THEN** the ci.yml build jobs report skipped and the required checks are satisfied without a build

#### Scenario: Mixed docs-and-code PR builds
- **WHEN** a PR changes `docs/notes.md` and `src/legends/context.cpp`
- **THEN** all ci.yml build jobs run

### Requirement: Module DAG Summary is a requirable aggregate
The module-dag `summary` job SHALL run on every triggering event (`if: always()`) and SHALL succeed when `include-rules` and `cmake-dag` each conclude success or skipped, and fail when either fails. The nightly-only `build-linux`/`build-windows` results SHALL continue to fail it only on failure (not on skipped).

#### Scenario: Gates skipped on a docs-only PR
- **WHEN** `include-rules` and `cmake-dag` are skipped by the changed-paths condition
- **THEN** `Summary` succeeds, so it can serve as the single required check for the workflow

#### Scenario: A gate fails
- **WHEN** `cmake-dag` fails on a PR
- **THEN** `Summary` fails

### Requirement: sprint2 pushes are restricted to protected branches
`sprint2-checks.yml` SHALL filter its `push` trigger to `main`, `master`, and `develop`, matching the other workflows. Its `pull_request` trigger SHALL remain branch-unrestricted, and neither trigger SHALL carry a `paths:` key.

#### Scenario: Feature-branch push
- **WHEN** a commit is pushed to a feature branch with no open PR
- **THEN** `sprint2-checks.yml` does not run

#### Scenario: PR from a feature branch
- **WHEN** a PR from that branch targets `master`
- **THEN** `sprint2-checks.yml` runs on the PR event

### Requirement: pal-ci filter narrows to its module boundary
`pal-ci.yml` SHALL keep workflow-level `paths:` (its restructuring is deferred to workflow consolidation) but the filter SHALL be exactly: `src/pal/**`, `include/pal/**`, `include/legends/**`, `src/legends/**`, `tests/unit/test_pal_*.cpp`, `.github/workflows/pal-ci.yml`. `cmake/**`, `CMakeLists.txt`, and the rest of `include/**` SHALL be removed. No pal-ci job SHALL be registered as a required check while the workflow remains path-filtered.

#### Scenario: cmake change no longer triggers PAL builds
- **WHEN** a PR changes only `cmake/dependencies.cmake`
- **THEN** `pal-ci.yml` does not trigger; the change is still built by the unfiltered `ci.yml` and checked by module-dag's `cmake-dag`

#### Scenario: legends core change still reaches contract gates
- **WHEN** a PR changes `src/legends/embed_api.cpp`
- **THEN** `pal-ci.yml` triggers and `contract-gates` runs its symbol checks against `liblegends_core.a`

### Requirement: Required-check eligibility is verified before the required set grows
Before any gate job from `module-dag.yml` or `sprint2-checks.yml` is added to the master ruleset's required checks, it SHALL be demonstrated on real PRs that the job reports a conclusion on both a matching and a non-matching change. Extending the required set SHALL follow the name-sync rule of the `merge-gating` capability and is not part of this change.

#### Scenario: Eligibility probe
- **WHEN** a docs-only probe PR and a `src/**` probe PR are opened after the workflow changes land
- **THEN** every required-set candidate (`Summary`, `Globals Registry Validation`, `Multi-Instance Smoke Tests`) reports a conclusion on both PRs — skipped on the first, success or failure on the second
