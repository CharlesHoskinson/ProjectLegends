## Why

Three separate accounting problems create divergence risks: dual `total_cycles` tracking (`ctx->timing` vs `g_time_state`), two unsynchronized `g_current_context` thread-locals (dosbox vs aibox), and CPU globals that can drift from CpuState. Any code path that updates one without the other creates non-determinism.

## What Changes

- Eliminate `g_time_state` from dosbox_library.cpp; make `ctx->timing` the single source of truth
- Unify context guards: `aibox::ContextGuard` also sets `dosbox::g_current_context`
- Define and enforce CPU globals <-> context sync convention at bridge entry/exit
- Add assertions to verify invariants

## Capabilities

### New Capabilities
- `context-unification`: Single source of truth for every field across dosbox/aibox layers

### Modified Capabilities

(none)

## Impact

- `engine/src/misc/dosbox_library.cpp` -- remove g_time_state (lines 79-98)
- `engine/src/misc/dosbox_context.cpp` -- dosbox g_current_context
- `engine/src/aibox/machine_context.cpp` -- aibox g_current_context
- `engine/src/misc/cpu_bridge.cpp` -- sync convention
- All 33 compat shim calls must resolve correctly after unification
