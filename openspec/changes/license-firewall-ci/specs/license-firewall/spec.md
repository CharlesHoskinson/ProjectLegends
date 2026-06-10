## ADDED Requirements

### Requirement: License-Critical Targets Are DAG-Verified at Configure Time
`legends_verify_all_dags()` SHALL verify `legends_ipc`, `legends_proxy`, and `legends_engine_host` (guarded by `if(TARGET ...)`, since the latter two exist only when `LEGENDS_USE_IPC=ON`), and `legends_detect_cycles()` SHALL include all three in its module list. A link from a license-critical target to an internal target not authorized by `cmake/ModuleManifest.cmake` SHALL fail configure with `FATAL_ERROR`. For the MIT targets `legends_ipc` and `legends_proxy`, the verification SHALL additionally reject any `aibox_core`, `legends_core`, or engine-prefixed dependency reached transitively via `INTERFACE_LINK_LIBRARIES`.

#### Scenario: MIT target acquires a GPL link
- **GIVEN** a change adds `legends_core` to `legends_proxy`'s `target_link_libraries`
- **WHEN** CMake configures with `LEGENDS_USE_IPC=ON`
- **THEN** configure SHALL terminate with `FATAL_ERROR` naming the unauthorized dependency

#### Scenario: Laundered transitive GPL dependency
- **GIVEN** an intermediate target whose `INTERFACE_LINK_LIBRARIES` includes `aibox_core`
- **WHEN** `legends_ipc` or `legends_proxy` links that intermediate target and CMake configures
- **THEN** configure SHALL terminate with `FATAL_ERROR`

#### Scenario: Clean IPC configure verifies all six modules
- **WHEN** CMake configures a clean tree with `LEGENDS_USE_IPC=ON`
- **THEN** the DAG verification output SHALL report `legends_ipc`, `legends_proxy`, and `legends_engine_host` as verified alongside the existing three modules

### Requirement: GPL Isolation Is Verified on the Built Artifact, Fail-Closed in CI
The IPC build SHALL include `cmake/VerifyGPLIsolation.cmake`, which scans the shell binary's linker map for GPL symbols post-build via `scripts/verify_gpl_isolation.py` and fails the build on any finding. A `LEGENDS_REQUIRE_GPL_VERIFICATION` option SHALL exist; when ON, every prerequisite-missing path (no Python3 interpreter, missing verifier script, unsupported compiler) SHALL be `FATAL_ERROR` instead of a warning. Every CI job that configures with `LEGENDS_USE_IPC=ON` SHALL set `LEGENDS_REQUIRE_GPL_VERIFICATION=ON`.

#### Scenario: GPL symbol in the shell map fails the build
- **GIVEN** a shell binary whose linker map contains a symbol matching the GPL pattern set and not the allowlist
- **WHEN** the post-build verification step runs
- **THEN** the build SHALL fail with the violating symbols reported

#### Scenario: Missing prerequisite fails closed in CI
- **GIVEN** `LEGENDS_REQUIRE_GPL_VERIFICATION=ON` and no Python3 interpreter on the runner
- **WHEN** CMake configures
- **THEN** configure SHALL terminate with `FATAL_ERROR` rather than disabling verification with a warning

#### Scenario: CI IPC jobs run the verification
- **WHEN** the `linux-ipc` or `windows-ipc` job builds
- **THEN** the build log SHALL contain the verifier's PASS line for the shell map, and the job SHALL fail if the verification step fails or is absent

### Requirement: The Isolation Verifier Is Itself Tested in CI
`tests/scripts/test_verify_gpl_isolation.py` SHALL run in CI at the mandatory tier, in the same workflow whose verdict the verifier gates, and SHALL fail its job on any test failure.

#### Scenario: Verifier regression is caught
- **GIVEN** a change to `scripts/verify_gpl_isolation.py` that makes a known-bad map fixture pass
- **WHEN** the CI verifier-test step runs
- **THEN** the step SHALL exit nonzero and the job SHALL fail

#### Scenario: Verifier tests gate pattern changes
- **WHEN** a pull request modifies `GPL_PATTERNS` or `ALLOWLIST_PATTERNS`
- **THEN** the verifier test suite SHALL execute on that pull request

### Requirement: REUSE Compliance Gates at the Mandatory Tier
The repository SHALL be REUSE-compliant (REUSE specification 3.3): every covered file has licensing information, every SPDX identifier in use has a license text in `LICENSES/`, and the vendored `engine/` tree is covered by `REUSE.toml` `[[annotations]]` with `precedence = "closest"` so upstream in-file headers take precedence and upstream files are not edited. A CI job SHALL run `reuse lint` on every push and pull request, without a path filter, and SHALL fail on any noncompliance. Annotations SHALL record currently documented license status only; the job SHALL NOT be the mechanism by which any file's license is changed.

#### Scenario: Untagged new file fails the lint
- **GIVEN** a pull request adding a source file with no SPDX identifier and no covering annotation
- **WHEN** the REUSE job runs
- **THEN** the job SHALL fail naming the file

#### Scenario: Vendor drop stays compliant without header edits
- **GIVEN** an `engine/` vendor drop whose new files carry no SPDX headers
- **WHEN** the REUSE job runs with the existing `engine/` annotations
- **THEN** the job SHALL pass without any upstream file having been modified

#### Scenario: The job is requirable
- **WHEN** any pull request opens, regardless of which paths it touches
- **THEN** the REUSE job SHALL be triggered and report a conclusion

### Requirement: MIT Trees Are Free of Engine-Internal Headers
No file under `src/legends_ipc/`, `include/legends_ipc/`, or `src/legends_proxy/` SHALL include an engine-internal header (`engine/include/**`, `engine/src/**`, or `dosbox/`- and `aibox/`-prefixed includes) or a private `src/legends/**` header. The rule SHALL be enforced by a CI-run check at the mandatory tier. The shared-memory semantics question itself (FSF FAQ treatment of shared-memory communication) is recorded as a counsel item and SHALL NOT be adjudicated by CI.

#### Scenario: Engine header crossing the boundary fails the check
- **GIVEN** a change adding `#include <dosbox/dosbox.h>` to a file in `src/legends_ipc/`
- **WHEN** the include check runs in CI
- **THEN** the check SHALL fail naming the file and the forbidden include

#### Scenario: Current tree passes
- **WHEN** the include check runs on a tree where the MIT trees include only IPC headers, standard headers, and the public C ABI header
- **THEN** the check SHALL pass

### Requirement: The IPC Architecture Builds on Two Operating Systems at the Mandatory Tier
A `windows-ipc` CI job SHALL configure with `LEGENDS_USE_IPC=ON` and `LEGENDS_REQUIRE_GPL_VERIFICATION=ON` on a Windows runner, build `legends_proxy` and `legends_engine_host`, run the post-build GPL isolation scan through the MSVC `/MAP` path, and run the test suite. Once brought to deterministic green via dispatch rehearsal, the job SHALL run on pull requests and pushes without a path filter.

#### Scenario: Windows IPC artifacts exist
- **WHEN** the `windows-ipc` job builds
- **THEN** `legends_engine_host` SHALL exist in the build tree and the Windows IPC platform sources SHALL have compiled

#### Scenario: MSVC map path is exercised
- **WHEN** the `windows-ipc` job's post-build verification runs
- **THEN** the verifier SHALL parse the MSVC-format map and report PASS or fail the build

#### Scenario: Promotion only after rehearsal
- **WHEN** the job is added to the pull-request tier
- **THEN** a prior `workflow_dispatch` run of the job SHALL have concluded success
