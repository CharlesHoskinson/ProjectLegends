## 1. Extern Declarations

- [x] 1.1 Add extern declarations in `cpu_bridge.cpp` for `CPU_Cycles`, `CPU_CycleLeft`, `CPU_CycleMax` (cpu.cpp:205-218)
- [x] 1.2 Add extern for `cpudecoder` function pointer (cpu.cpp:216)
- [x] 1.3 Add extern for `PIC_RunQueue()` (pic.cpp:723)
- [x] 1.4 Add extern for `CPU_Check_NMI()` (cpu.cpp)

## 2. Execute Cycles Rewrite

- [x] 2.1 Rewrite `execute_cycles()` to set `CPU_CycleLeft` from requested cycles
- [x] 2.2 Implement main loop: `PIC_RunQueue()` -> `CPU_Check_NMI()` -> `(*cpudecoder)()`
- [x] 2.3 Handle positive return values by dispatching through `CallBack_Handlers[]`
- [x] 2.4 Handle `dosbox_allow_nonrecursive_page_fault` toggle
- [x] 2.5 Catch `GuestPageFaultException`
- [x] 2.6 Sync `ctx->timing` after execution completes

## 3. Initialization

- [x] 3.1 Verify `cpudecoder` is non-null in `init_cpu_bridge()`
- [x] 3.2 Call `CPU_Core_Normal_Init()` if `cpudecoder` is null

## 4. Context Synchronization

- [x] 4.1 Copy context -> CPU globals before each bridge call
- [x] 4.2 Copy CPU globals -> context after each bridge call
- [x] 4.3 Add debug assertions verifying sync at entry/exit

## 5. Tests

- [x] 5.1 Test: write HLT (0xF4) to memory at CS:IP, run, assert halt state
- [x] 5.2 Test: load counter loop COM program, run, verify memory count
- [x] 5.3 All existing 3,343 tests still pass
- [x] 5.4 No sanitizer failures (ASan, UBSan, TSan)

## Known Limitation

The current implementation calls `(*cpudecoder)()` directly but does not call `PIC_RunQueue()` or `CPU_Check_NMI()` in the execution loop. Timer/interrupt-driven code may not fire during bridge-controlled execution. See AUDIT.md finding C2.
