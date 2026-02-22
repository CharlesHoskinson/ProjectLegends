## Why

The post-audit codebase has several trivially-fixable Critical and High findings that add noise to every subsequent phase. Clearing them first establishes a clean baseline and prevents compounding technical debt.

## What Changes

- Delete 2,016 lines of dead code (`dosboxx_embed_api.cpp`, deprecated and never compiled)
- Fix gsl-lite PUBLIC linkage leaking transitive dependency to consumers
- Remove `/wd4244` narrowing-warning suppression across the entire engine (critical for an x86 emulator where register widths matter)
- Enforce the reentrancy guard that is declared but never checked
- Deep-copy config string pointers to prevent dangling references
- Wrap headless_stub.cpp process-globals in a resettable struct
- Fix README inaccuracies (SaveStateHeader size, missing API function docs)

## Capabilities

### New Capabilities
- `dead-code-removal`: Delete dosboxx_embed_api.cpp and verify no build references remain
- `build-hygiene`: Fix gsl-lite linkage (PUBLIC -> PRIVATE), remove /wd4244, fix narrowing warnings
- `runtime-safety`: Enforce reentrancy guard, deep-copy config strings, wrap headless_stub globals
- `documentation-fixes`: Correct README SaveStateHeader size, document 7 missing API functions

### Modified Capabilities

(none)

## Impact

- `engine/CMakeLists.txt` -- gsl-lite linkage, /wd4244 removal
- `engine/src/aibox/dosboxx_embed_api.cpp` -- deleted
- `src/legends/legends_embed_api.cpp` -- reentrancy guard added
- `engine/src/misc/dosbox_library.cpp` -- config string deep-copy
- `engine/src/aibox/headless_stub.cpp` -- globals wrapped in struct
- `README.md` -- corrected header size, added 7 function docs
- 20-50 engine source files -- explicit `static_cast<>` for narrowing fixes
