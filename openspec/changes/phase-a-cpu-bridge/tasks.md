## 1. Extern Declarations

- [ ] 1.1 Add extern declarations in `cpu_bridge.cpp` for `CPU_Cycles`, `CPU_CycleLeft`, `CPU_CycleMax` (cpu.cpp:205-218)
- [ ] 1.2 Add extern for `cpudecoder` function pointer (cpu.cpp:216)
- [ ] 1.3 Add extern for `PIC_RunQueue()` (pic.cpp:723)
- [ ] 1.4 Add extern for `CPU_Check_NMI()` (cpu.cpp)

## 2. Execute Cycles Rewrite

- [ ] 2.1 Rewrite `execute_cycles()` to set `CPU_CycleLeft` from requested cycles
- [ ] 2.2 Implement main loop: `PIC_RunQueue()` -> `CPU_Check_NMI()` -> `(*cpudecoder)()`
- [ ] 2.3 Handle positive return values by dispatching through `CallBack_Handlers[]`
- [ ] 2.4 Handle `dosbox_allow_nonrecursive_page_fault` toggle
- [ ] 2.5 Catch `GuestPageFaultException`
- [ ] 2.6 Sync `ctx->timing` after execution completes

## 3. Initialization

- [ ] 3.1 Verify `cpudecoder` is non-null in `init_cpu_bridge()`
- [ ] 3.2 Call `CPU_Core_Normal_Init()` if `cpudecoder` is null

## 4. Context Synchronization

- [ ] 4.1 Copy context -> CPU globals before each bridge call
- [ ] 4.2 Copy CPU globals -> context after each bridge call
- [ ] 4.3 Add debug assertions verifying sync at entry/exit

## 5. Tests

- [ ] 5.1 Test: write HLT (0xF4) to memory at CS:IP, run, assert halt state
- [ ] 5.2 Test: load counter loop COM program, run, verify memory count
- [ ] 5.3 All existing 3,343 tests still pass
- [ ] 5.4 No sanitizer failures (ASan, UBSan, TSan)
