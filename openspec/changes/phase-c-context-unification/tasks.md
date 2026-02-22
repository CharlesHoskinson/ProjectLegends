## 1. Eliminate g_time_state

- [ ] 1.1 Remove `g_time_state` struct from `dosbox_library.cpp` (lines 79-98)
- [ ] 1.2 Route all timing queries through `ctx->timing`
- [ ] 1.3 Compute `emu_time_us` from `ctx->timing.total_cycles * cycle_duration_us`
- [ ] 1.4 Verify no remaining references to `g_time_state`

## 2. Unify Context Guards

- [ ] 2.1 Modify `aibox::ContextGuard` constructor to also call `dosbox::set_current_context()`
- [ ] 2.2 Modify `aibox::ContextGuard` destructor to also clear `dosbox::g_current_context`
- [ ] 2.3 Verify all 33 compat shim calls resolve correctly
- [ ] 2.4 Add assertion test: both context pointers always agree when guard is active

## 3. CPU Globals Sync Convention

- [ ] 3.1 Document sync convention in `cpu_bridge.h` comments
- [ ] 3.2 Add `ASSERT` checks at bridge entry (globals match context)
- [ ] 3.3 Add `ASSERT` checks at bridge exit (context updated from globals)

## 4. Cleanup

- [ ] 4.1 Refactor `state_hash_compat.cpp` to use explicit context passing instead of thread-local lookup

## 5. Verification

- [ ] 5.1 All tests pass
- [ ] 5.2 Determinism test hashes unchanged (compare before/after)
- [ ] 5.3 No sanitizer failures
