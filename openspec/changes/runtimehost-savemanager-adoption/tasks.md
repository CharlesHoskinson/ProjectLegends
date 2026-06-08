## 1. Interface Declarations

- [x] 1.1 Declare new `RuntimeHost&` overloads for `saveToSlot`, `loadFromSlot`, and `recoverAutosave` in `save_manager.h`.
- [x] 1.2 Add `#include <legends/runtime_host.h>` in `save_manager.cpp` (or forward declare in `save_manager.h`).

## 2. Implementation Updates

- [x] 2.1 Implement `RuntimeHost&` overloads in `save_manager.cpp`, replacing direct FFI calls with `runtime.save_state` and `runtime.load_state`.
- [x] 2.2 Re-route transitional `legends_handle` overloads to wrap the handle in `InProcessEngineRuntime` and delegate.
- [x] 2.3 Preserve autosave slot 0 as valid storage for save, load, and recovery paths.

## 3. Application Integration

- [x] 3.1 Update `Application::init()` crash recovery to use `*runtime_`.
- [x] 3.2 Update `Application::registerActionHandlers()` SaveState and LoadState handlers to use `*runtime_`.

## 4. Allowlist & Validation

- [x] 4.1 Remove 3 retired SaveManager entries from `docs/architecture/runtimehost-bypass-allowlist.json`.
- [x] 4.2 Run `graphify_projectlegends.py update` to rebuild code graph.
- [x] 4.3 Verify bypass count drops to 35.

## 5. Verification

- [x] 5.1 ABI tests pass cleanly.
- [x] 5.2 Unit tests pass cleanly.
- [x] 5.3 Strict Graphify validations pass.
- [x] 5.4 SaveManager unit tests cover autosave slot 0 path and occupancy semantics.
