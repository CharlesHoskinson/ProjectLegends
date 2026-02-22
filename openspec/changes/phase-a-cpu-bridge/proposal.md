## Why

The CPU bridge is the most critical gap in the codebase. `cpu_bridge.cpp` declares the execution interface but increments counters in a loop instead of running real x86 instructions. Without this, the emulator cannot execute guest code through the library API. Every downstream feature (determinism, replay, serialization validation) is blocked.

## What Changes

- Rewrite `cpu_bridge.cpp` to call through the real DOSBox-X execution path: `Normal_Loop()` -> `PIC_RunQueue()` -> `(*cpudecoder)()`
- Add extern declarations for CPU globals (`CPU_Cycles`, `CPU_CycleLeft`, `cpudecoder`, etc.)
- Implement context <-> globals synchronization at bridge entry/exit
- Handle callbacks, page faults, and cpudecoder initialization
- Add tests: single HLT instruction, counter loop COM program

## Capabilities

### New Capabilities
- `cpu-execution`: Wire cpu_bridge.cpp to real DOSBox-X CPU core for actual x86 instruction execution

### Modified Capabilities

(none)

## Impact

- `engine/src/misc/cpu_bridge.cpp` -- full rewrite
- `engine/include/dosbox/cpu_bridge.h` -- possible interface changes
- References: `engine/src/cpu/cpu.cpp`, `engine/src/hardware/pic.cpp`, `engine/src/dosbox.cpp`, `engine/src/cpu/core_normal.cpp`
- Unblocks: Phase C (context unification), Phase E (determinism at scale), Sprint 4 (replay)
