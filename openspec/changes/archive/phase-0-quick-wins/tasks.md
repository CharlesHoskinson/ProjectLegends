## 1. Dead Code Removal

- [x] 1.1 Delete `engine/src/aibox/dosboxx_embed_api.cpp`
- [x] 1.2 Verify no CMakeLists.txt or source file references `dosboxx_embed_api`
- [x] 1.3 Build on all platforms and confirm success

## 2. Build Hygiene

- [x] 2.1 Change `target_link_libraries(aibox_core PUBLIC gsl::gsl-lite-v1)` to `PRIVATE` in `engine/CMakeLists.txt`
- [x] 2.2 Remove `/wd4244` suppression from `engine/CMakeLists.txt` — N/A, no such suppression exists; per-file `#pragma warning(disable:4244)` in legacy HW emulation code left intentionally
- [x] 2.3 Fix all resulting C4244 narrowing warnings with explicit `static_cast<>` (expect 20-50 sites) — N/A, see 2.2
- [x] 2.4 Build clean on MSVC with zero C4244 warnings — N/A, see 2.2

## 3. Runtime Safety

- [x] 3.1 Add RAII reentrancy guard struct to `legends_embed_api.cpp`
- [x] 3.2 Check `inst->in_step` at top of `legends_step_ms` and `legends_step_cycles`; return `LEGENDS_ERR_REENTRANT_CALL` if set
- [x] 3.3 Add reentrancy test (log callback re-enters step, verify error code returned)
- [x] 3.4 Deep-copy config string pointers in `dosbox_library.cpp` (line 222) using `strdup()`; free in destroy
- [x] 3.5 Wrap 7 headless_stub.cpp globals in `HeadlessState` struct with `reset()` method
- [x] 3.6 Call `HeadlessState::reset()` from `dosbox_lib_destroy`

## 4. Documentation

- [x] 4.1 Fix README: SaveStateHeader is 64 bytes (not 96)
- [x] 4.2 Document 7 missing API functions in README: `legends_get_api_version`, `legends_get_config`, `legends_key_event_ext`, `legends_is_frame_dirty`, `legends_get_cursor`, `legends_get_last_error`, `legends_set_log_callback`

## 5. Verification

- [x] 5.1 All 3,343 tests pass
- [x] 5.2 Build green on Linux, Windows, macOS
- [x] 5.3 No sanitizer failures
