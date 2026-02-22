## Context

`cpu_bridge.cpp` is the most critical stub in the codebase. It declares the CPU execution interface but increments counters in a loop. The real DOSBox-X execution path runs through `Normal_Loop()` -> `PIC_RunQueue()` -> `(*cpudecoder)()`, none of which the bridge calls.

## Goals / Non-Goals

**Goals:**
- Execute real x86 instructions through the library API
- Follow the existing Normal_Loop pattern (proven, battle-tested)
- Sync CPU globals <-> context at bridge boundaries
- Handle callbacks, page faults, and cpudecoder initialization
- Prove execution with HLT and counter loop tests

**Non-Goals:**
- Supporting multiple CPU cores (dynamic_core, simple_core, etc.) -- Normal core only for now
- Multi-threading the execution path
- Changing the DOSBox-X core itself

## Decisions

**Follow Normal_Loop exactly:** The real execution path is `Normal_Loop()` at dosbox.cpp:427-519. Rather than inventing a new pattern, replicate its structure: loop while `PIC_RunQueue()` returns true, call `CPU_Check_NMI()`, call `(*cpudecoder)()`, dispatch callbacks. This minimizes divergence from the proven engine behavior.

**Extern declarations vs header inclusion:** Use extern declarations in cpu_bridge.cpp for the specific globals needed (`CPU_Cycles`, `CPU_CycleLeft`, `CPU_CycleMax`, `cpudecoder`, `PIC_RunQueue`, `CPU_Check_NMI`). Including full DOSBox-X headers would pull in massive dependency chains.

**Sync convention (copy-in/copy-out):** Before each bridge call: copy `ctx->cpu.*` fields to the CPU globals. After each bridge call: copy globals back to context. This is the simplest correct approach -- no shared-memory aliasing, no risk of partial updates.

**Page fault handling:** Catch `GuestPageFaultException` in the execution loop. Check `dosbox_allow_nonrecursive_page_fault` flag. On fault, break the execution loop and report cycles consumed so far.

## Risks / Trade-offs

- [Extern declarations may drift from actual globals] → Mitigate with static_assert on types where possible
- [Copy-in/copy-out adds overhead per bridge call] → Negligible; the CPU globals are ~20 fields, memcpy is trivial vs instruction execution cost
- [Normal core only limits performance] → Acceptable for correctness-first approach; dynamic core can be added later
- [Callback handling complexity] → Follow the exact CallBack_Handlers pattern from Normal_Loop; don't innovate

## Key Files

| File | Role |
|------|------|
| `engine/src/misc/cpu_bridge.cpp` | Rewrite target |
| `engine/include/dosbox/cpu_bridge.h` | Interface (may need updates) |
| `engine/src/cpu/cpu.cpp:205-218` | CPU globals source |
| `engine/src/hardware/pic.cpp:723-792` | PIC_RunQueue reference |
| `engine/src/dosbox.cpp:427-519` | Normal_Loop reference |
| `engine/src/cpu/core_normal.cpp:160-223` | cpudecoder reference |
