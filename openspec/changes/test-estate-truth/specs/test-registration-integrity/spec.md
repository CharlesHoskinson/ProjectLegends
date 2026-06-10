# test-registration-integrity

## ADDED Requirements

### Requirement: Every Test Source Compiles or Is Consciously Removed
Every test source file under `tests/` SHALL be compiled into a CTest-visible target, or removed with the removal recorded (commit message naming the file and the reason). No test source SHALL sit on disk uncompiled.

#### Scenario: No orphaned test sources
- **WHEN** the test source lists in the CMake trees are compared against `tests/**/*.cpp` on disk
- **THEN** every file SHALL appear in exactly one target's source list (or be a shared fixture header/util)

#### Scenario: Removal leaves a record
- **GIVEN** a test source is deleted instead of repaired
- **WHEN** the deletion lands
- **THEN** the commit SHALL record the file name and the reason for removal

### Requirement: test_dual_ffi.cpp Joins the Integration Target
`tests/integration/test_dual_ffi.cpp` SHALL be added to the `legends_integration_tests` source list and SHALL compile and register through `gtest_discover_tests`.

#### Scenario: Dual-FFI tests are registered
- **GIVEN** a configured build with `LEGENDS_BUILD_TESTS=ON`
- **WHEN** `ctest -N` enumerates tests
- **THEN** the dual-FFI tests SHALL appear as registered CTest entries

### Requirement: Bit-Rotted Orphans Are Rewritten or Deleted
`tests/integration/test_context_synchronization.cpp` and `tests/integration/test_error_propagation.cpp` — which call a nonexistent `legends_init(handle)` and pass three arguments to the four-parameter `legends_get_last_error` (include/legends/legends_embed.h:644-649) — SHALL each be either rewritten against the current embed API preserving the original scenario intent, or deleted with the removal recorded. A rewrite SHALL NOT pass vacuously: it SHALL assert the original scenario (cross-context synchronization; error-code propagation across the FFI boundary).

#### Scenario: Rewritten orphan compiles and tests its scenario
- **GIVEN** an orphan is rewritten rather than deleted
- **WHEN** the integration target builds and runs
- **THEN** the rewritten file SHALL compile against the current API and its tests SHALL assert the original scenario's behavior

#### Scenario: Neither outcome leaves the file orphaned
- **WHEN** this change is complete
- **THEN** neither file SHALL exist on disk outside a target's source list
