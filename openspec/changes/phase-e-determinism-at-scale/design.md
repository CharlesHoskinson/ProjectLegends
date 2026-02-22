## Context

Existing determinism tests run <200K cycles in text mode. The roadmap goal is 1M+ cycles in text and graphics modes. Phases A (CPU bridge), B (serialization), and C (context unification) must be complete before this phase can produce meaningful results.

## Goals / Non-Goals

**Goals:**
- Minimal COM test binaries checked into repo
- Prove correctness at 1K cycles (memory value check)
- Prove determinism at 1M cycles (hash comparison)
- Prove save/load midpoint equivalence
- Prove graphics mode (Mode 13h) determinism
- Prove input replay determinism
- Nightly soak test for long-running confidence

**Non-Goals:**
- Testing protected mode or DPMI programs
- Testing disk I/O or file system determinism
- Performance benchmarking (that's Sprint 4)
- Testing multi-instance concurrency

## Decisions

**COM binary creation:** Hand-assemble minimal COM programs (raw x86 machine code, no linker). Check the binary files directly into `tests/fixtures/`. Each is <100 bytes. No assembler tool dependency needed.

**counter.com:** `MOV CX, N; MOV DI, 0x8000; loop: INC BYTE [DI]; LOOP loop; HLT`. Increments memory at 0x8000 N times then halts.

**graphics.com:** `MOV AX, 0x13; INT 10h; MOV DI, 0xA000; draw pattern; HLT`. Switches to Mode 13h (320x200x256), writes a deterministic pattern to video memory.

**input.com:** `MOV AH, 0; INT 16h; MOV [0x8000], AL; HLT`. Waits for a keystroke via BIOS, stores scancode, halts.

**Hash comparison strategy:** Use the existing `legends_state_hash` function which produces a deterministic hash over the full serialized state. Compare hashes rather than byte-for-byte state comparison (hashes are sufficient and simpler to work with).

**Nightly soak test:** Separate CI workflow triggered on schedule (cron). Runs 10 iterations with different COM programs. Failure notifies via CI status, doesn't block PRs.

## Risks / Trade-offs

- [Hand-assembled COM binaries are fragile] → They're trivially small (5-20 instructions each); include disassembly comments
- [1M cycles takes real wall time] → Estimate ~2-5 seconds per run; acceptable for CI
- [Mode 13h requires VGA subsystem working] → If VGA init fails, test is skipped with clear message, not a false pass
- [Nightly soak adds CI cost] → Schedule-triggered, doesn't affect PR latency
