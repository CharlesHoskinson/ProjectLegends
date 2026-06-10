## ADDED Requirements

### Requirement: Single timing config source
`g_cycles_per_ms` SHALL be removed from `dosbox_library.cpp`. All timing helpers SHALL
read cycle rate from `g_config.cpu_cycles` via the `cycles_per_ms()` function.

#### Scenario: g_cycles_per_ms eliminated
- **WHEN** `dosbox_library.cpp` is inspected
- **THEN** `g_cycles_per_ms` SHALL NOT exist as a global variable

#### Scenario: Timing helpers use config
- **WHEN** `cycles_to_us()` or `ms_to_cycles()` compute timing
- **THEN** they SHALL read from `g_config.cpu_cycles`, not a separate global

### Requirement: Both context TLS pointers set during legends step
`legends_step_cycles()` SHALL set both `dosbox::g_current_context` and
`aibox::g_current_context` for the entire step scope, including input draining.

#### Scenario: dosbox context set during step
- **WHEN** `legends_step_cycles()` is executing
- **THEN** `dosbox::current_context()` SHALL return a valid non-null context

#### Scenario: Compat shims work during input drain
- **WHEN** compat shims are called during `drain_input_to_engine()`
- **THEN** they SHALL receive the correct non-null dosbox context

### Requirement: CPU globals sync convention
The save/restore pattern for `CPU_Cycles` SHALL be documented in `cpu_bridge.h`.
Debug assertions SHALL verify the restore postcondition.

#### Scenario: Documented convention
- **WHEN** `cpu_bridge.h` is inspected
- **THEN** the sync convention SHALL be documented in comments before `execute_cycles`

#### Scenario: Debug assertion present
- **WHEN** `cpu_bridge.cpp` executes in debug build
- **THEN** `assert(CPU_Cycles == saved)` SHALL fire after restore

### Requirement: Determinism hashes unchanged
Context unification SHALL NOT change any determinism test hash values.

#### Scenario: Hash stability
- **WHEN** all determinism tests run after unification
- **THEN** hash values SHALL match pre-unification values exactly
