## Context

Three separate accounting problems create divergence risks. `g_time_state` duplicates `ctx->timing`. Two `g_current_context` thread-locals (dosbox/aibox) can disagree. CPU globals can drift from CpuState between bridge calls.

## Goals / Non-Goals

**Goals:**
- Single source of truth for every field
- Remove `g_time_state` entirely
- Both context pointers always agree
- CPU globals sync convention documented and enforced with assertions
- Zero change to determinism test hashes

**Non-Goals:**
- Merging DOSBoxContext and MachineContext into one struct (too invasive)
- Removing thread-local context entirely (compat shims need it)
- Migrating the remaining 30-40 untracked globals (Sprint 5)

## Decisions

**Eliminate g_time_state:** Remove the struct from dosbox_library.cpp (lines 79-98). Route `emu_time_us` computation through `ctx->timing.total_cycles * cycle_duration_us`. Any code currently reading `g_time_state` gets rewritten to read from context.

**ContextGuard unification:** Modify `aibox::ContextGuard` constructor to also call `dosbox::set_current_context(ctx->dosbox_ctx())`. This is a one-line change. The destructor already clears the aibox pointer; add clearing the dosbox pointer too. Both layers always see the same context.

**CPU globals sync convention:** Document in `cpu_bridge.h`: "Before bridge call: copy context -> globals. After bridge call: copy globals -> context." Add `ASSERT(CPU_Cycles == ctx->cpu.cycles)` style checks at bridge entry/exit in debug builds.

**state_hash_compat.cpp cleanup:** This file uses `current_context()` and is ripe for explicit context passing. Pass context as a parameter instead of relying on thread-local lookup.

## Risks / Trade-offs

- [Removing g_time_state touches timing-sensitive code] → Run full determinism suite before/after; hashes must match
- [ContextGuard change affects all compat shims] → This is the desired effect; verify all 33 calls resolve
- [Debug assertions add overhead] → Debug-only; zero cost in release builds
