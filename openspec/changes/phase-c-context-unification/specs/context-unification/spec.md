## ADDED Requirements

### Requirement: Single timing source of truth
`g_time_state` SHALL be removed from `dosbox_library.cpp`. All timing queries SHALL route through `ctx->timing`. `emu_time_us` SHALL be computed from context directly.

#### Scenario: g_time_state eliminated
- **WHEN** `dosbox_library.cpp` is inspected
- **THEN** `g_time_state` SHALL NOT exist

#### Scenario: Timing queries use context
- **WHEN** any code queries emulation time
- **THEN** it SHALL read from `ctx->timing`, not a separate global

### Requirement: Unified context guards
`aibox::ContextGuard` SHALL also set `dosbox::g_current_context` (since MachineContext wraps DOSBoxContext). All 33 compat shim calls SHALL resolve through either context pointer.

#### Scenario: Both contexts agree
- **WHEN** `aibox::ContextGuard` is active
- **THEN** `dosbox::current_context()` and `aibox::current_context()` SHALL return pointers to the same underlying DOSBoxContext

#### Scenario: Compat shims work
- **WHEN** a compat shim (pic_compat, memory_compat, dma_compat) calls `dosbox::current_context()`
- **THEN** it SHALL receive the correct non-null context

### Requirement: CPU globals sync convention
Context fields SHALL be copied to CPU globals before every bridge call. CPU globals SHALL be copied back to context after every bridge call. This convention SHALL be documented in `cpu_bridge.h`.

#### Scenario: Documented convention
- **WHEN** `cpu_bridge.h` is inspected
- **THEN** the sync convention SHALL be documented in comments

#### Scenario: Assertions at bridge boundaries
- **WHEN** a bridge call begins or ends
- **THEN** debug assertions SHALL verify globals match context

### Requirement: Determinism hashes unchanged
Context unification SHALL NOT change any determinism test hash values.

#### Scenario: Hash stability
- **WHEN** all determinism tests run after unification
- **THEN** hash values SHALL match pre-unification values exactly
