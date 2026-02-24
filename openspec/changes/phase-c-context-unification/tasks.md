## 1. Context Guard Unification

- [ ] 1.1 Add `dosbox_lib_get_context_ptr()` to `dosbox_library.h`
- [ ] 1.2 Implement `dosbox_lib_get_context_ptr()` in `dosbox_library.cpp`
- [ ] 1.3 Add `dosbox::ContextGuard` in `legends_step_cycles()` before compat guard
- [ ] 1.4 Add `#include "dosbox/dosbox_context.h"` to `legends_embed_api.cpp`
- [ ] 1.5 Verify compat shims have valid context during entire step scope

## 2. Eliminate g_cycles_per_ms

- [ ] 2.1 Replace `g_cycles_per_ms` global with `cycles_per_ms()` inline function
- [ ] 2.2 Update `cycles_to_us()` and `ms_to_cycles()` to call `cycles_per_ms()`
- [ ] 2.3 Remove `g_cycles_per_ms = ...` assignment in `dosbox_lib_create()`
- [ ] 2.4 Remove `g_cycles_per_ms = 3000` reset in `dosbox_lib_destroy()`
- [ ] 2.5 Verify no remaining references to `g_cycles_per_ms`

## 3. CPU Globals Sync Convention

- [ ] 3.1 Document sync convention in `cpu_bridge.h` comments
- [ ] 3.2 Add debug assertion in `cpu_bridge.cpp` after CPU_Cycles restore

## 4. Tests

- [ ] 4.1 Write test: both context TLS pointers set during legends step
- [ ] 4.2 Write test: cycles_per_ms matches config
- [ ] 4.3 Write test: different rates produce correct timing

## 5. Verification

- [ ] 5.1 All new tests pass
- [ ] 5.2 Full suite: no new failures beyond pre-existing 12
- [ ] 5.3 g_cycles_per_ms grep returns zero hits
