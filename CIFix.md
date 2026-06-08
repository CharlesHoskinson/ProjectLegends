# CI Fix OpenSpec Instructions

## Change Metadata

- Change ID: `ci-stabilization-and-coverage-control`
- Proposed OpenSpec path: `openspec/changes/ci-stabilization-and-coverage-control`
- Status: Implemented locally, pending remote GitHub Actions validation after the next commit/push.
- Auditor: Codex
- Implementer: Gemini Flash
- Primary goal: restore trustworthy, low-noise CI by fixing current remote failures, separating real product regressions from duplicated workflow noise, and making coverage actionable.

## Why

The current remote CI baseline is failing across multiple workflows on `origin/master`. The failures are not one class of issue:

- SDL backend jobs fail at compile time because PAL sources include raw `gsl-lite` and call `gsl::...` instead of using the project bridge namespace.
- Windows jobs fail because MSVC warning-as-error policy applies to test targets, exposing ignored `[[nodiscard]]` returns across many unit and integration tests.
- Linux headless jobs fail one determinism test: `DeterminismTest.SaveLoadWithLongerExecution`.
- GitHub checkout cleanup logs show tracked `.claude/worktrees/*` gitlink entries without matching `.gitmodules` mappings.
- Coverage does not currently provide signal because the coverage job depends on the broad Linux matrix and is skipped when Linux fails.
- CI is duplicated across `CI`, `PAL CI`, `Module DAG`, and `Sprint 2 Checks`, causing the same root cause to appear as several failures.

## Current Baseline To Reconfirm Before Editing

Before implementing, verify the active branch and commit state:

```powershell
git status -sb
git rev-parse HEAD
git rev-parse origin/master
gh run list --limit 20 --json databaseId,name,status,conclusion,headSha,headBranch,createdAt,url
```

Record whether the Flash sprint has completed and whether new CI runs exist for commits after `757255e`.

## Post RuntimeHost App-Service Audit Baseline

Codex audited the completed `runtimehost-app-service-adoption` sprint before starting CI cleanup.

Corrections applied during audit:

- Refreshed stale Graphify source hashes with `python scripts/graphify_projectlegends.py update --repo . --source-only`.
- Fixed new `RuntimeHost` string forwarding methods so `std::string_view` inputs are copied into null-terminated `std::string` values before passing to C ABI functions.
- Corrected the OpenSpec design note for `legends_get_cursor`; the ABI takes `uint8_t* x_out`, `uint8_t* y_out`, and `int* visible_out`.

Audited local verification now passes:

- `openspec.cmd validate runtimehost-app-service-adoption --strict --json`
- `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- `python scripts/check_capability_matrix.py --repo .`
- `python scripts/check_conflict_markers.py --path .`
- `git diff --check`
- `cmake --preset dev`
- `cmake --build --preset dev`
- `build/dev/legends_abi_test.exe`
- `build/dev/legends_unit_tests.exe` with `2680` passed and `18` skipped.

Current RuntimeHost facts CI cleanup must preserve:

- Graphify reports exactly two application-layer direct bypasses: `Application::init -> legends_create` and `Application::shutdown -> legends_destroy`.
- The RuntimeHost app-service adoption removed the application bypass debt but did not implement IPC parity for every newly routed service method; several proxy C ABI functions still return `LEGENDS_ERR_NOT_SUPPORTED`.
- The local tree is ahead of `origin/master` and contains uncommitted RuntimeHost/OpenSpec/Graphify changes. Remote CI failures from `757255e` are stale until the next push, but they remain valid evidence for the SDL, MSVC, determinism, checkout hygiene, and coverage cleanup tracks.
- Several RuntimeHost sprint files have large blank-line formatting churn. Treat this as review debt unless it blocks a quality gate.

## Implementation Progress After First CI Cleanup Pass

Codex applied and locally verified the first low-risk CI stabilization set on 2026-06-08.

Completed locally:

- Replaced raw PAL SDL `gsl-lite` includes/usages with the project bridge in SDL2 and SDL3 implementation files.
- Added `libxss-dev` to Linux SDL3/X11 dependency installs in `ci.yml` and `pal-ci.yml`.
- Removed tracked `.claude/worktrees/*` gitlinks from the repository index and ignored `.claude/worktrees/`.
- Added a documented, MSVC-only `/wd4834` containment policy to test targets while keeping production warning policy intact.
- Re-ran Graphify after the RuntimeHost audit corrections; app-layer RuntimeHost bypasses remain exactly two and allowlisted.

Verified locally:

- `rg -n -P "<gsl-lite/gsl-lite\\.hpp>|(?<!legends::)\\bgsl::" src/pal` returned no matches.
- `git submodule status` exits cleanly.
- `git diff --check`
- `python scripts/check_conflict_markers.py --path .`
- `python scripts/check_capability_matrix.py --repo .`
- `python scripts/graphify_projectlegends.py update --repo . --source-only`
- `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- `openspec.cmd validate runtimehost-app-service-adoption --strict --json`
- `cmake --preset dev`
- `cmake --build --preset dev`
- `build/dev/legends_abi_test.exe`
- `build/dev/legends_unit_tests.exe` with `2680` passed and `18` skipped.

Remote-only validation still pending:

- Remote CI has not rerun against this local dirty tree; latest audited remote failures are still from stale `757255e`.
- GitHub Actions checkout cleanup, Linux primary, Windows primary, and coverage artifact publication require a pushed commit before they can be proven remotely.
- SDL2/SDL3 backend fixes also need scheduled/manual/tag-oriented remote validation after push.

## Resolved Implementation After CI Stabilization Pass

Codex resolved the CIFix implementation locally on 2026-06-08.

Resolved locally:

- Added the OpenSpec change at `openspec/changes/ci-stabilization-and-coverage-control` and validated it with `openspec.cmd validate ci-stabilization-and-coverage-control --strict --json`.
- Fixed the Linux determinism failure by serializing/restoring hash-relevant context metadata, synchronizing CPU bridge globals with context CPU state, and resetting CPU control globals deterministically during init/reset.
- Enhanced the determinism harness with immediate post-load hash checks and component-level hash diffs.
- Re-ran the full local CTest suite: `4497` tests passed, `43` skipped, `0` failed.
- Split ordinary CI from optional validation: primary push/PR checks remain focused, while SDL/PAL, macOS, sanitizer, fuzz, TLA+, dependency scan, and duplicate Module DAG build lanes are scheduled/manual/tag/path oriented.
- Made coverage report-only, independent from optional backend lanes, and configured it to upload `coverage.filtered.info` plus policy text artifacts.
- Preserved production warning strictness while containing MSVC ignored-`[[nodiscard]]` noise to test targets with documented `/wd4834`.

## Scope

This change SHALL address CI system stabilization only. It SHALL NOT refactor RuntimeHost adoption, application service routing, or other active architecture work except where required to avoid CI conflicts.

In scope:

- Fix SDL PAL GSL bridge usage.
- Fix or contain MSVC `[[nodiscard]]` warning failures in test targets.
- Triage and fix the deterministic save/load failure or temporarily quarantine it with an explicit tracked reason if a product fix is larger than this sprint.
- Remove tracked `.claude/worktrees/*` gitlink entries and add ignore rules for local agent artifacts.
- Consolidate or path-gate duplicated CI lanes so normal pushes produce one clear primary signal.
- Make coverage run independently enough to be useful and make the threshold explicit.

Out of scope:

- RuntimeHost feature migration.
- Graphify RuntimeHost bypass reduction, except ensuring the existing Graphify CI gate remains intact.
- Packaging/release artifact redesign beyond preventing unrelated failures on normal pushes.
- Full sanitizer cleanup unless needed to unblock the primary gate.

## Proposed Requirements

### Requirement: Primary CI Signal

The repository SHALL have one primary push/PR quality signal that compiles and tests the headless product path on Linux and Windows.

#### Scenario: Normal source push

- GIVEN a push modifies `src/**`, `include/**`, `engine/**`, `tests/**`, `scripts/**`, `cmake/**`, `CMakeLists.txt`, or workflow files
- WHEN GitHub Actions runs
- THEN the primary required signal SHALL run
- AND duplicated workflows SHALL NOT report the same headless test failure as separate unrelated failures.

### Requirement: SDL Backend Build Health

SDL2 and SDL3 PAL sources SHALL use the project GSL bridge consistently.

#### Scenario: SDL backend compile

- GIVEN `PAL_BACKEND_SDL2=ON` or `PAL_BACKEND_SDL3=ON`
- WHEN the PAL target is compiled on Linux
- THEN no source under `src/pal/**` SHALL include raw `<gsl-lite/gsl-lite.hpp>` directly
- AND calls SHALL use `legends::gsl::...` after including `<legends/gsl.hpp>`.

### Requirement: Windows Test Build Health

Windows test targets SHALL compile without failing on intentional ignored results.

#### Scenario: MSVC test compile

- GIVEN tests are built with MSVC
- WHEN test code intentionally ignores a `[[nodiscard]]` result
- THEN the code SHALL explicitly consume or assert the result
- OR the test target SHALL have a narrowly scoped, documented MSVC test-only warning policy.

### Requirement: Determinism Regression Triage

The determinism failure SHALL be treated as a product/test correctness issue, not hidden by workflow consolidation.

#### Scenario: Save/load long execution determinism

- GIVEN `DeterminismTest.SaveLoadWithLongerExecution`
- WHEN the test fails with `State hashes differ after save/load round-trip`
- THEN the implementation SHALL identify the non-serialized or nondeterministic state source
- AND either fix the state preservation defect
- OR quarantine the test behind a named label with a linked TODO and an explicit follow-up task.

### Requirement: Repository Hygiene

Local agent worktrees SHALL NOT be tracked as repository content.

#### Scenario: Checkout cleanup

- GIVEN GitHub Actions runs `actions/checkout`
- WHEN post-job cleanup executes
- THEN there SHALL be no `fatal: no submodule mapping found in .gitmodules for path '.claude/worktrees/...'` warning.

### Requirement: Coverage Signal

Coverage SHALL be able to produce useful output even while optional backend lanes are red.

#### Scenario: Coverage job

- GIVEN the primary Linux headless build and tests pass
- WHEN the coverage job runs
- THEN it SHALL generate `coverage.filtered.info`
- AND upload it as an artifact
- AND either enforce the agreed threshold or explicitly document that coverage is report-only.

## Design Notes

### Workflow Strategy

Keep these as primary required checks:

- Sprint 2 checks: globals, migration, conflict markers, capability matrix, Graphify enrichment.
- Linux headless build/test.
- Windows headless build/test.
- ABI verification.
- Coverage, once independent and stable.

Move these to path-gated, scheduled, or non-blocking until green:

- SDL2 backend matrix.
- SDL3 backend matrix.
- Full PAL CI duplicates.
- Sanitizers.
- Fuzzing.
- TLA+.
- Packaging and release validation except for tag pushes.

Avoid deleting useful workflows unless the replacement is already active. Prefer path filters, `workflow_dispatch`, and clear names.

### GSL Bridge Fix

For PAL files that currently include raw gsl-lite:

- Replace `#include <gsl-lite/gsl-lite.hpp>` with `#include <legends/gsl.hpp>`.
- Replace `gsl::narrow` and `gsl::narrow_cast` with `legends::gsl::narrow` and `legends::gsl::narrow_cast`.
- Keep this scoped to implementation files, not public headers.

Audit likely files:

- `src/pal/sdl2/window_sdl2.cpp`
- `src/pal/sdl2/context_sdl2.cpp`
- `src/pal/sdl2/audio_sink_sdl2.cpp`
- `src/pal/sdl2/input_source_sdl2.cpp`
- `src/pal/sdl3/window_sdl3.cpp`
- `src/pal/sdl3/context_sdl3.cpp`
- `src/pal/sdl3/audio_sink_sdl3.cpp`
- `src/pal/sdl3/input_source_sdl3.cpp`

### MSVC Warning Policy

Preferred fix:

- Replace ignored `[[nodiscard]]` calls in tests with `ASSERT_EQ`, `EXPECT_EQ`, `ASSERT_TRUE`, or explicit `(void)` only when the result is intentionally irrelevant.

Acceptable temporary containment:

- Add a narrowly scoped MSVC-only test target option such as `/wd4834` for test targets only.
- Do not disable `/WX` for production targets.
- Document this as temporary debt in the OpenSpec tasks.

### Determinism Failure

Known failing test:

- `engine/tests/determinism/test_determinism.cpp`
- `DeterminismTest.SaveLoadWithLongerExecution`
- Failure text: `State hashes differ after save/load round-trip`

Investigation path:

- Run the failing test alone.
- Compare the shorter passing `SaveLoadRoundTripPreservesDeterminism` path against the longer failing path.
- Inspect state hash inputs and save/load serialization coverage for timing, scheduler, frame, input, audio, and per-instance state.
- Add focused diagnostics or a regression test around the missing state once identified.

### Tracked Agent Artifact Cleanup

Current issue:

- `.claude/worktrees/*` are tracked as mode `160000` gitlinks.
- `.gitmodules` has no mapping.

Required cleanup:

- Remove `.claude/worktrees/*` from the index.
- Consider removing `.claude/settings.local.json` from tracking if it is machine-local.
- Add `.claude/` or at least `.claude/worktrees/` to `.gitignore`.
- Verify `git submodule status` no longer fails.

### Coverage

Current issue:

- `.github/workflows/ci.yml` coverage has `needs: [linux]`, which depends on a broad matrix and therefore often skips.
- `coverage-check` in `CMakeLists.txt` reports coverage but does not enforce the documented 80% threshold.

Required cleanup:

- Make coverage depend on a narrow Linux headless job or run as a separate headless coverage job.
- Decide whether `src/app` coverage is blocking or report-only.
- If blocking, enforce the threshold in CI with a deterministic script.
- Upload `coverage.filtered.info` as an artifact regardless of Codecov availability.

## Task List

### 1. Audit Baseline

- [x] 1.1 Confirm latest remote CI runs and commit SHAs.
- [x] 1.2 Record failing workflows, job IDs, and first root-cause failure per job.
- [x] 1.3 Confirm whether local branch is ahead of `origin/master`.
- [x] 1.4 Confirm whether active Flash sprint changes are complete before editing shared files.

### 2. SDL Backend Compile Fix

- [x] 2.1 Replace raw gsl-lite includes in SDL2 PAL implementation files with `<legends/gsl.hpp>`.
- [x] 2.2 Replace raw `gsl::` usages with `legends::gsl::`.
- [x] 2.3 Run a search proving no raw gsl-lite includes remain under `src/pal/**`.
- [x] 2.4 SDL2/SDL3 PAL fixes are implemented and moved behind optional scheduled/manual/tag-oriented validation for remote proof after push.

### 3. MSVC Test Warning Fix

- [x] 3.1 Identify all MSVC `C4834` failures from the latest Windows CI log.
- [x] 3.2 Accepted temporary containment path for this sprint: documented MSVC test-target-only `/wd4834` policy.
- [x] 3.3 If the edit set is too large for this sprint, add temporary `/wd4834` only to test targets and document follow-up cleanup.
- [x] 3.4 Verified Windows headless build/test locally with `cmake --build --preset dev`, `legends_abi_test.exe`, `legends_unit_tests.exe`, and full `ctest`.

### 4. Determinism Failure

- [x] 4.1 Reproduce `DeterminismTest.SaveLoadWithLongerExecution` alone.
- [x] 4.2 Identify state included in `get_state_hash` but missing from save/load, or state restored nondeterministically.
- [x] 4.3 Fix the missing serialization/restoration path.
- [x] 4.4 Add or update focused regression diagnostics in the determinism harness.
- [x] 4.5 No quarantine needed; the determinism binary and full local CTest suite pass.

### 5. Repository Hygiene

- [x] 5.1 Remove tracked `.claude/worktrees/*` gitlinks from the repository index.
- [x] 5.2 Add ignore rules for local agent worktrees.
- [x] 5.3 Verify `git submodule status` succeeds or exits cleanly.
- [x] 5.4 Local repository hygiene is fixed; remote checkout cleanup proof is pending the next pushed run.

### 6. CI Consolidation

- [x] 6.1 Decide required checks for normal PR/push.
- [x] 6.2 Path-gate or schedule duplicated backend, sanitizer, fuzz, TLA+, and packaging jobs.
- [x] 6.3 Ensure `Sprint 2 Checks` remains active for code, docs architecture, scripts, and tests.
- [x] 6.4 Ensure `Module DAG` does not duplicate full test responsibility unless intentionally required.
- [x] 6.5 Add clear workflow names that indicate primary, optional, scheduled, or release-only status.

### 7. Coverage Control

- [x] 7.1 Make coverage run from a narrow, stable Linux headless configuration.
- [x] 7.2 Upload coverage artifact even if Codecov token is absent.
- [x] 7.3 Decide and implement threshold behavior.
- [x] 7.4 Coverage no longer depends on optional backend failures; remote artifact proof is pending after push.

### 8. Final Verification

- [x] 8.1 `python scripts/check_conflict_markers.py --path .`
- [x] 8.2 `python scripts/check_capability_matrix.py --repo .`
- [x] 8.3 `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- [x] 8.4 `cmake --preset dev`
- [x] 8.5 `cmake --build --preset dev`
- [x] 8.6 `build/dev/legends_abi_test.exe`
- [x] 8.7 `build/dev/legends_unit_tests.exe`
- [x] 8.8 Linux primary gate is configured for remote proof after push; local equivalent full CTest passes.
- [x] 8.9 Windows primary gate is configured for remote proof after push; local Windows build/test passes.
- [x] 8.10 Coverage artifact publication is configured for remote proof after push.

## Codex Audit Gates

Codex SHALL audit the Flash implementation gate by gate.

### Gate 1: Baseline Evidence

Pass criteria:

- QA artifact lists exact commit SHA, workflow run IDs, and job IDs audited.
- New runs after the Flash sprint are considered, not only stale `757255e` runs.

### Gate 2: SDL GSL Bridge

Pass criteria:

- No raw gsl-lite includes remain under `src/pal/**`.
- SDL2 and SDL3 builds do not fail on undeclared `gsl`.
- Public headers do not expose gsl-lite types.

### Gate 3: Windows Build Policy

Pass criteria:

- Production targets retain strict warning policy.
- Test policy is explicit and scoped.
- Any temporary `/wd4834` containment is documented with follow-up tasks.

### Gate 4: Determinism

Pass criteria:

- The determinism failure is fixed, or quarantine is explicit and justified.
- The CI system still preserves a visible determinism signal.

### Gate 5: CI Topology

Pass criteria:

- Normal pushes produce a small required set of high-signal checks.
- Optional and scheduled checks are clearly labeled.
- Duplicated headless full-test failures are reduced.

### Gate 6: Coverage

Pass criteria:

- Coverage job can run after primary Linux success.
- Coverage artifact is uploaded.
- Threshold behavior is explicit and reproducible.

### Gate 7: Repository Hygiene

Pass criteria:

- `.claude/worktrees/*` gitlinks are gone.
- `.gitignore` prevents recurrence.
- `git submodule status` does not fail because of missing `.gitmodules` entries.

## QA Artifact Required From Implementer

The implementation SHALL produce a QA artifact under:

`docs/superpowers/reviews/YYYY-MM-DD-gemini-35-flash-openspec-ci-stabilization-qa.md`

The QA artifact SHALL include:

- OpenSpec change path.
- Exact before/after CI status table.
- Files changed.
- Commands passed.
- Commands failed or blocked.
- Local test coverage result or reason coverage was remote-only.
- Remote GitHub Actions run URLs.
- Explicit list of remaining CI debt.
- Top five Codex audit targets.

## Commands To Prefer

Use these commands where applicable:

```powershell
gh run list --limit 20 --json databaseId,name,status,conclusion,headSha,headBranch,createdAt,url
gh run view <run-id> --json name,conclusion,status,url,event,headBranch,headSha,jobs
gh run view <run-id> --job <job-id> --log
rg -n "gsl-lite|gsl::" src/pal include
git ls-files -s .claude
git submodule status
cmake --preset dev
cmake --build --preset dev
build/dev/legends_abi_test.exe
build/dev/legends_unit_tests.exe
python scripts/check_conflict_markers.py --path .
python scripts/check_capability_matrix.py --repo .
python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify
git diff --check
```

## Deferred Decision For Codex After Flash Completes

After the active Flash sprint ends, Codex SHALL:

1. Audit the Flash RuntimeHost/app-service changes first.
2. Update this `CIFix.md` based on the new tree and latest remote CI runs.
3. Convert this file into an OpenSpec change directory if it still matches the current state.
4. Start fixing CI in the safest order: SDL bridge, repository hygiene, Windows test policy, determinism, workflow consolidation, coverage.
