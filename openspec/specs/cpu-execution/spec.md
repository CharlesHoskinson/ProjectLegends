## ADDED Requirements

### Requirement: Real x86 instruction execution
`cpu_bridge.cpp` SHALL execute real x86 instructions through the DOSBox-X core by calling `PIC_RunQueue()`, `CPU_Check_NMI()`, and `(*cpudecoder)()` in the Normal_Loop pattern.

#### Scenario: HLT instruction halts
- **WHEN** 0xF4 (HLT) is written to memory at CS:IP and `execute_cycles()` is called
- **THEN** the CPU SHALL halt and the bridge SHALL return

#### Scenario: Counter loop executes
- **WHEN** a COM program that increments a memory location N times is loaded and run
- **THEN** the memory location SHALL contain the expected count after execution

### Requirement: CPU globals synchronization
Context fields SHALL be copied to CPU globals before each bridge call. CPU globals SHALL be copied back to context after each bridge call.

#### Scenario: Context reflects execution
- **WHEN** `execute_cycles(1000)` completes
- **THEN** `ctx->timing.total_cycles` SHALL reflect the actual cycles executed

#### Scenario: Globals don't drift
- **WHEN** multiple bridge calls are made in sequence
- **THEN** CPU_Cycles/CPU_CycleLeft SHALL match context state at every entry and exit

### Requirement: Callback handling
Positive return values from `(*cpudecoder)()` SHALL be dispatched through `CallBack_Handlers[]`.

#### Scenario: Callback dispatched
- **WHEN** cpudecoder returns a positive value N
- **THEN** `CallBack_Handlers[N]` SHALL be invoked

### Requirement: Page fault handling
`execute_cycles()` SHALL catch `GuestPageFaultException` and handle `dosbox_allow_nonrecursive_page_fault` correctly.

#### Scenario: Page fault caught
- **WHEN** a guest page fault occurs during execution
- **THEN** the bridge SHALL catch the exception and not crash

### Requirement: cpudecoder initialization
`init_cpu_bridge()` SHALL verify `cpudecoder` is non-null. If null, it SHALL call `CPU_Core_Normal_Init()`.

#### Scenario: Null cpudecoder handled
- **WHEN** `init_cpu_bridge()` is called before CPU core initialization
- **THEN** `cpudecoder` SHALL be initialized to `CPU_Core_Normal_Run`
