## ADDED Requirements

### Requirement: Reentrancy guard enforcement
`legends_step_ms` and `legends_step_cycles` SHALL check `inst->in_step` at entry and return `LEGENDS_ERR_REENTRANT_CALL` (-5) if already set. The flag SHALL be cleared via RAII on exit (including exceptional paths).

#### Scenario: Reentrant call rejected
- **WHEN** a log callback calls `legends_step_ms` during an active step
- **THEN** the call SHALL return `LEGENDS_ERR_REENTRANT_CALL`

#### Scenario: Normal exit clears flag
- **WHEN** `legends_step_ms` completes normally
- **THEN** `inst->in_step` SHALL be false

#### Scenario: Exceptional exit clears flag
- **WHEN** `legends_step_ms` throws an exception
- **THEN** `inst->in_step` SHALL be false (RAII cleanup)

### Requirement: Config string deep-copy
`dosbox_library.cpp` SHALL deep-copy all config string pointers during `dosbox_lib_create`. The caller's string buffers MAY be freed after create returns.

#### Scenario: Caller frees strings after create
- **WHEN** config strings are allocated on the stack and `dosbox_lib_create` returns
- **THEN** the instance SHALL hold valid copies of all config strings

### Requirement: Headless stub globals wrapped
The 7 process-global variables in `headless_stub.cpp` SHALL be wrapped in a struct with a `reset()` method. `dosbox_lib_destroy` SHALL call `reset()`.

#### Scenario: Globals reset on destroy
- **WHEN** `dosbox_lib_destroy` is called
- **THEN** all headless stub globals (including `g_virtual_ticks`) SHALL be reset to initial values

#### Scenario: Second create sees clean state
- **WHEN** an instance is destroyed and a new one created
- **THEN** headless stub state SHALL match a fresh process
