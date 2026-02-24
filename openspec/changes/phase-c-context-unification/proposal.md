## Why

Three state management issues create divergence risk between engine and legends layers:

1. **Dual context pointers** -- `dosbox::g_current_context` and `aibox::g_current_context`
   are independent thread-locals. The legends-layer `CompatContextGuard` does not set the
   dosbox pointer. Compat shims (pic, memory, dma, vga, int10, state_hash) read
   `dosbox::current_context()`. Currently safe because `dosbox_lib_step_cycles()` creates
   its own `dosbox::ContextGuard`, but calling compat shims outside the engine step scope
   (e.g. during input draining in `legends_step_cycles()`) would fault.

2. **`g_cycles_per_ms` global** -- file-scope global in dosbox_library.cpp duplicating
   `g_config.cpu_cycles`. Used only by `cycles_to_us()` and `ms_to_cycles()` helpers.

3. **CPU sync convention undocumented** -- cpu_bridge.cpp correctly saves/restores
   `CPU_Cycles` around bridge calls and updates `ctx->timing`, but the convention
   lacks documentation and debug assertions.

## What Changes

- Add `dosbox::ContextGuard` in `legends_step_cycles()` so both TLS pointers are set
  for the entire step scope (including input draining before engine step)
- Eliminate `g_cycles_per_ms`; replace with `cycles_per_ms()` helper reading `g_config.cpu_cycles`
- Document CPU sync convention and add debug assertions

## Capabilities

### New Capabilities
- `context-unification`: Both dosbox and aibox context TLS pointers set during legends step

### Modified Capabilities

(none)

## Impact

- `engine/include/dosbox/dosbox_library.h` -- new `dosbox_lib_get_context_ptr()` API
- `engine/src/misc/dosbox_library.cpp` -- implement get_context_ptr, eliminate g_cycles_per_ms
- `src/legends/legends_embed_api.cpp` -- add dosbox::ContextGuard in legends_step_cycles
- `engine/include/dosbox/cpu_bridge.h` -- sync convention documentation
- `engine/src/misc/cpu_bridge.cpp` -- debug assertions
