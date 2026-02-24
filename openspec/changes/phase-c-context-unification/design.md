## Context

Two context management issues and one documentation gap create divergence risk.
`MachineContext` and `DOSBoxContext` are independent types; `legends_instance` holds both
(machine at line 57, engine_handle at line 60) but neither references the other.
The aibox ContextGuard cannot directly set the dosbox pointer.

## Goals / Non-Goals

**Goals:**
- Both dosbox and aibox TLS context pointers set during entire `legends_step_cycles` scope
- Eliminate `g_cycles_per_ms` global; single timing config source via `g_config.cpu_cycles`
- CPU globals sync convention documented and enforced with debug assertions
- Zero change to determinism test hashes

**Non-Goals:**
- Merging DOSBoxContext and MachineContext into one struct (too invasive)
- Removing thread-local context entirely (compat shims need it)
- Modifying aibox::ContextGuard to set dosbox pointer (architectural boundary)

## Decisions

**Context guard fix lives in legends_step_cycles:** Since MachineContext and DOSBoxContext
are independent types, the fix adds a `dosbox::ContextGuard` in `legends_step_cycles()`,
obtained via a new `dosbox_lib_get_context_ptr()` C API. This keeps the aibox layer
unaware of dosbox internals. The existing `dosbox::ContextGuard` inside
`dosbox_lib_step_cycles()` is kept for standalone engine API usage (nesting is safe).

**Eliminate g_cycles_per_ms:** Replace the file-scope global with an inline `cycles_per_ms()`
function that reads `g_config.cpu_cycles`. Single config source, no duplication.

**CPU sync convention:** Document the save/restore pattern in `cpu_bridge.h`. Add
`assert(CPU_Cycles == saved)` after restore in debug builds.

## Risks / Trade-offs

- [Context pointer obtained via void* cast] -> type-safe cast in legends layer, verified by tests
- [g_cycles_per_ms removal touches timing math] -> values identical, verified by existing tests
- [Debug assertions add overhead] -> debug-only; zero cost in release builds
