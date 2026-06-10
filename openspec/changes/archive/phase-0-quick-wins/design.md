## Status: COMPLETE

All tasks completed. Dead code removed, gsl-lite linkage fixed, reentrancy guard enforced, config strings deep-copied, headless globals wrapped, README updated.

## Context

Post-audit codebase with 3,343 tests passing and CI green. Several Critical/High findings are trivially fixable but add noise. Clearing them before larger phases prevents compounding debt.

## Goals / Non-Goals

**Goals:**
- Delete dead code (dosboxx_embed_api.cpp)
- Fix gsl-lite transitive linkage leak
- Remove /wd4244 and fix all narrowing warnings with explicit casts
- Enforce the declared-but-unchecked reentrancy guard
- Deep-copy config strings to prevent dangling pointers
- Wrap headless_stub globals for clean instance lifecycle
- Fix README inaccuracies

**Non-Goals:**
- Refactoring the API surface
- Changing serialization format
- Modifying CPU bridge
- Adding new features

## Decisions

**Delete vs deprecate dosboxx_embed_api.cpp:** Delete. It's 2,016 lines never compiled, explicitly marked `@deprecated`, and fully superseded by `legends_embed_api.cpp`.

**Narrowing warning fixes:** Use explicit `static_cast<>` at each site rather than introducing helper functions. The cast documents intent and the compiler verifies the source/target types. Expect 20-50 sites, mostly in register operations (e.g., `static_cast<uint8_t>(value & 0xFF)`).

**Reentrancy guard pattern:** RAII guard struct that sets `in_step = true` in constructor and `false` in destructor. Check at function entry, return error code immediately if already set. No mutex needed (single-threaded contract).

**Config string deep-copy:** Use `strdup()` for each string pointer in the config struct at line 222 of dosbox_library.cpp. Free in destroy. Simple and sufficient.

**Headless stub globals:** Wrap in `struct HeadlessState` with 7 members and a `reset()` method. Single file-scoped instance. Call `reset()` from `dosbox_lib_destroy`.

## Risks / Trade-offs

- [/wd4244 removal may surface latent bugs] → This is actually the point; narrowing in an x86 emulator is a correctness risk
- [20-50 files touched for casts] → Large diff but each change is mechanical and reviewable
- [strdup uses malloc] → Acceptable; config strings are small and allocated once per instance lifetime
