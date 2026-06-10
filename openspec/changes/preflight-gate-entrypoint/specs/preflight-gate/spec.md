## ADDED Requirements

### Requirement: Single Gate Entry Point
The project SHALL provide `scripts/preflight.py` as the single committed entry point for the mandatory gate suite. Its gate registry SHALL include exactly the ten CI-run check-script gates (`check_includes`, `check_current_context`, `check_migration_status`, `check_globals`, `check_gsl_lite_usage`, `check_conflict_markers`, `check_case_collisions`, `check_openspec_staleness`, `check_capability_matrix`, graphify enrich+check), the C11 ABI compile of `include/legends/legends_embed.h`, and the OS-reachable build/test configurations. Each gate's command, flags, and arguments SHALL be defined once in the registry; subset selection SHALL never vary a gate's command, only which gates run.

#### Scenario: Full run executes every reachable gate
- **WHEN** a developer runs `scripts/preflight.py all`
- **THEN** every registry gate reachable on the current OS SHALL execute
- **AND** the process SHALL exit non-zero iff any attempted gate fails
- **AND** all gates SHALL run to completion before exit, with a per-gate PASS/FAIL/SKIPPED summary

#### Scenario: Script-gate subset matches CI's sprint2 commands
- **WHEN** `scripts/preflight.py scripts` runs
- **THEN** it SHALL invoke the ten check-script gates with the same arguments the corresponding `.github/workflows/sprint2-checks.yml` and `.github/workflows/module-dag.yml` steps used (including `--strict --strict-tests fail --allow-missing-graphify` for the graphify check)

#### Scenario: Orphan script stays excluded
- **WHEN** the registry is enumerated
- **THEN** `scripts/check_compiler.py` SHALL NOT be a gate

### Requirement: Ordered Graphify Pair
The graphify gate SHALL run as an ordered pair: the enrichment build (`scripts/enrich_graphify_projectlegends.py`) SHALL complete successfully before the check (`scripts/check_graphify_enrichment.py`) runs, and the pair SHALL never be separable in the registry.

#### Scenario: Enrich precedes check
- **WHEN** any preflight invocation selects the graphify gate
- **THEN** the enrich step SHALL run first
- **AND** the check step SHALL run only after the enrich step succeeds

#### Scenario: Enrich failure fails the gate
- **WHEN** the enrich step exits non-zero
- **THEN** the graphify gate SHALL report FAIL without running the check step

### Requirement: OS-Gated ABI Compile
The ABI gate SHALL probe for a C11-capable compiler (`gcc`, then `clang`, then MSVC `cl`) and compile `include/legends/legends_embed.h` mirroring the `ci.yml` abi-check semantics. On machines with no such compiler the gate SHALL report a named SKIPPED result stating that CI runs this gate, and SHALL NOT hard-fail. A `--require` flag SHALL convert SKIPPED into FAIL.

#### Scenario: gcc-less MSVC-only Windows machine
- **WHEN** the ABI gate runs on a machine where only `cl` is available
- **THEN** the gate SHALL compile the header via the MSVC C-mode path
- **AND** SHALL label the result an approximation of CI's gcc invocation

#### Scenario: No C11 compiler present
- **WHEN** the ABI gate runs and no probe succeeds
- **THEN** the gate SHALL print a SKIPPED line naming the gate and the CI lane that covers it
- **AND** the preflight exit code SHALL NOT fail on account of this gate

#### Scenario: CI requires the compile
- **WHEN** the ABI gate runs with `--require` and no probe succeeds
- **THEN** the gate SHALL FAIL

### Requirement: Named OS Residue
Build/test configurations in the registry SHALL declare OS reachability. A preflight run SHALL execute the reachable configurations and SHALL print each unreachable configuration by name with the reason it cannot run locally. Silent skipping SHALL NOT occur.

#### Scenario: Windows developer runs the full preflight
- **WHEN** `scripts/preflight.py all` runs on Windows without the Linux toolchains
- **THEN** the Linux-toolchain configurations SHALL be listed as unreachable with their reason
- **AND** the reachable configurations SHALL build and test

### Requirement: Interpreter Portability
Preflight SHALL launch child gate scripts via `sys.executable`, never a bare `python` shell string, so machines exposing only the Windows `py` launcher run the suite.

#### Scenario: py-launcher-only Windows machine
- **WHEN** preflight is started with `py scripts/preflight.py all`
- **THEN** every child gate script SHALL run under the same interpreter
- **AND** no gate SHALL fail due to `python` being absent from PATH

### Requirement: CI Consumes the Entry Point
The CI workflows SHALL invoke `scripts/preflight.py` instead of inlining gate commands: `sprint2-checks.yml`'s check-script steps SHALL be replaced by a `preflight scripts` invocation, `module-dag.yml`'s include-rules step SHALL invoke preflight's `check_includes` gate, and `ci.yml`'s abi-check job body SHALL invoke `preflight abi --require`. No gate command SHALL exist inline in these workflow steps after rewiring.

#### Scenario: sprint2 runs the script suite through preflight
- **WHEN** `sprint2-checks.yml`'s gate job runs
- **THEN** it SHALL execute `scripts/preflight.py scripts`
- **AND** no `python scripts/check_*.py` step SHALL remain inline in the workflow

#### Scenario: abi-check cannot green on a skip
- **WHEN** `ci.yml`'s abi-check job runs on a runner without a C11 compiler
- **THEN** the `--require` flag SHALL make the job FAIL rather than skip

#### Scenario: Local and CI commands are identical
- **WHEN** a gate fails in CI
- **THEN** running the same preflight subcommand locally on the same tree SHALL fail with the same gate named
