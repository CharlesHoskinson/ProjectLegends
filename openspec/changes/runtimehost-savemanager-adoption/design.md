## Status: COMPLETE

The design has been applied. Overloads for `SaveManager` accepting `RuntimeHost&` are added. Transitional handle paths delegate using `InProcessEngineRuntime`. Application uses `runtime_` for saving/loading, and autosave slot 0 remains valid for crash recovery.

## Context

`SaveManager` currently uses raw FFI calls to save and load state. This sprint migrates it behind `RuntimeHost`.

## Decisions

### 1. SaveManager Interface & Overloads

We introduce the following overloads in `SaveManager`:
```cpp
    [[nodiscard]] bool saveToSlot(RuntimeHost& runtime, int slot,
                    const uint8_t* rgb_thumb, uint16_t w, uint16_t h);
    [[nodiscard]] bool loadFromSlot(RuntimeHost& runtime, int slot);
    [[nodiscard]] bool recoverAutosave(RuntimeHost& runtime);
```

The existing `legends_handle` signatures are preserved for transitional callers and tests:
```cpp
    [[nodiscard]] bool saveToSlot(legends_handle engine, int slot,
                    const uint8_t* rgb_thumb, uint16_t w, uint16_t h);
    [[nodiscard]] bool loadFromSlot(legends_handle engine, int slot);
    [[nodiscard]] bool recoverAutosave(legends_handle engine);
```
These will instantiate a temporary `InProcessEngineRuntime(engine, false)` and delegate to the `RuntimeHost` overloads.

Slot validation must continue to allow `SaveManager::kAutosaveSlot` (`0`) through `SaveManager::kMaxSlots`. User-visible save slots are 1 through 9, but crash recovery uses slot 0.

### 2. Application Integration

In `Application::init()`:
```cpp
    if (save_manager_.hasAutosave()) {
        if (save_manager_.recoverAutosave(*runtime_)) { ... }
    }
```

In `Application::registerActionHandlers()`:
```cpp
    // Save state
    if (save_manager_.saveToSlot(*runtime_, slot, thumb.empty() ? nullptr : thumb.data(), w, h)) { ... }

    // Load state
    if (save_manager_.loadFromSlot(*runtime_, slot)) { ... }
```

### 3. Verification & Metrics

- **Gating**: The count of direct bypasses will drop from 38 to 35.
- **Verification**: Run Graphify update and check enrichment using strict validation checks.

## Risks / Trade-offs

- State serialization signatures match exactly.
- Slot 0 must not be treated as an invalid user slot in the storage layer, because crash autosave recovery depends on it.

## Verification Commands

- `cmake --preset dev`
- `cmake --build --preset dev`
- `build/dev/legends_unit_tests.exe`
- `build/dev/legends_abi_test.exe`
- `python scripts/graphify_projectlegends.py update --repo . --source-only`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
