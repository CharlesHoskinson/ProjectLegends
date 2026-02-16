# Project Legends — Development Roadmap

## Current Status

**Sprint 1** — Library Foundation: Complete
**Sprint 2** — Instance Reality: Complete
**Sprint 3** — Module Graph: Complete

### Global Migration Summary

| Category | Count | % |
|----------|-------|---|
| Migrated | 61 | 87% |
| Partial | 0 | 0% |
| Deferred | 9 | 13% |
| Pending | 0 | 0% |
| **Total tracked** | **70** | |

---

## Tier 1 — Sprint 2 Completion (DONE)

All 3 partial global migrations are complete. Multi-instance support validated.

### 1. ~~Complete PIC register state migration~~ DONE

- `PicController` struct in `pic_types.h`, embedded as `PicState.controllers[2]`
- Full 14-field register state per controller + `controller_index`
- `enable_slave_pic`, `enable_pc_xt_nmi_mask` global flags added
- Compat shims expanded in `pic_compat.cpp`

### 2. ~~Complete VGA register state migration~~ DONE

- `VGA_Type_t* hw` opaque pointer in `VgaState`
- Per-instance allocation via `allocate_hw()`/`free_hw()`
- `extern VGA_Type vga` → `#define vga (vga_get_hw())` macro redirect
- Hash includes DAC, CRTC, Seq, Attr, Gfx, Config register subsets

### 3. ~~Complete keyboard buffer state migration~~ DONE

- Buffer expanded from 16 → 96 (matches KEYBUFSIZE=32*3)
- `Ps2MouseState` sub-struct (13 fields: type, mode, samplerate, buttons, etc.)
- `enable_aux`, `reset_state`, `aux_command` flags added

### 4. Eliminate thread-local current_context() accessors

- Remove all thread-local `current_context()` usage from production code
- Accessor macros in headers (e.g., `vga.h` redirects via `current_context()`) still exist
- Tracked by `scripts/check_current_context.py`
- All subsystem access should use explicit context parameter passing

### 5. ~~Multi-instance smoke test~~ DONE

- `engine/tests/unit/test_multi_instance_smoke.cpp` (8 tests)
- Keyboard/PIC/VGA isolation, independent hashes, clean destruction

### 6. CI enforcement preventing new globals

- Verify `.github/workflows/sprint2-checks.yml` fully prevents new globals
- Ensure `baseline_globals.yaml` is up to date
- Confirm `scripts/check_globals.py` catches regressions
- Lock down globals registry once Sprint 2 completes

### 7. Remove compat shim files after full migration

- Once multi-instance is verified in production, simplify or
  remove the compatibility shim files:
  - `dma_compat.cpp`, `memory_compat.cpp`, `pic_compat.cpp`, `vga_compat.cpp`
  - `int10_compat.cpp`, `state_hash_compat.cpp`
  - `cpu_bridge.h` / `cpu_bridge.cpp`

---

## Tier 2 — Immediate Priorities (Parallelizable)

### 8. Cross-platform build verification

- [ ] Linux GCC
- [ ] Windows MSVC/MinGW
- [ ] macOS Clang
- `module-dag.yml` has Linux/Windows jobs but needs end-to-end verification
- macOS Clang not yet covered in CI

### 9. GUI assessment and decision

- [ ] Assess DOSBox-X GUI survival (`src/gui/` menu, mapper)
- [ ] SDL2 backend test (window, rendering, input, fullscreen)
- [ ] SDL3 backend test (texture rendering, audio stream)
- [ ] Decision: keep DOSBox-X GUI, strip for headless-only, or replace
- Feeds into Sprint 6 frontend convergence

### 10. LLM integration end-to-end testing

- [ ] Frame capture test (create → step → capture text)
- [ ] Token estimation accuracy validation
- [ ] Action batch execution (`aibox_llm_execute_batch`)
- [ ] End-to-end agent test (boot DOS, run DIR, verify replay)
- [ ] Game targets: Oregon Trail, Zork, Commander Keen, DOOM

### 11. Dead code removal

- [ ] Networking code (unused in library mode)
- [ ] Printer/parallel port drivers
- [ ] Other legacy DOSBox-X subsystems unreachable in library/headless mode
- Reduces attack surface, build times, and maintenance burden

### 12. Machine context subsystem initialization (8 stubs)

- `engine/src/aibox/machine_context.cpp` has 8 placeholder TODOs:
  - [ ] PIC controller (line 381)
  - [ ] PIT timer (line 386)
  - [ ] VGA context (line 396)
  - [ ] Keyboard controller (line 401)
  - [ ] Mouse controller (line 402)
  - [ ] Sound subsystem (line 407)
  - [ ] DOS kernel (line 412)
  - [ ] Actual emulation logic (line 228)

---

## Tier 3 — Sprints 4–6 (Sequential)

### Sprint 4 — Deterministic Replay as Product

**Blocked by:** Sprint 2 completion (multi-instance smoke test)

- [ ] First-class state hash API with stability guarantees
- [ ] Versioned snapshot schema (portable, forward-compatible)
- [ ] Trace format specification
- [ ] Differential debugging runner
- [ ] Fast CI trace corpus
- [ ] Nightly soak suite

### Sprint 5 — True Embeddability

**Blocked by:** Sprint 4

- [ ] In-memory configuration only
- [ ] Abstracted filesystem access
- [ ] No implicit environment access
- [ ] Interactive behavior extraction
- [ ] Sandbox compatibility verification

### Sprint 6 — Frontend Convergence

**Blocked by:** GUI decision (task 9)

- [ ] SDL2 deprecation
- [ ] SDL3 performance tuning
- [ ] SDL2 removal
- [ ] Blessed configuration documentation
- [ ] Optional remote control station
- [ ] Product-quality packaging

---

## Tier 4 — Medium-Term Goals

### API Refinement

- [ ] Unify `legends_embed.h` and `aibox/ffi_*.h` APIs
- [ ] Rust bindings (`legends-rs` crate) — blocked by API unification
- [ ] Python bindings (`pylegends` package) — blocked by API unification

### Testing Infrastructure

- [ ] Golden file tests for determinism
- [ ] Expand fuzzing harness for save/load (LibFuzzer infra exists)
- [ ] Performance regression tests
- [ ] Memory leak detection (Valgrind/ASan systematic coverage)

### Documentation

- [ ] API reference (Doxygen)
- [ ] Integration guide for Rust/Python
- [ ] Game compatibility database
- [ ] Troubleshooting guide

---

## Future Possibilities

- GPU acceleration (OpenGL/Vulkan backends)
- Extended platforms (WebAssembly, iOS/Android, embedded)
- Advanced LLM features (semantic region detection, OCR, reward signals)

---

## Dependency Graph

```
Tasks 1,2,3 (partial globals)
    ├──→ Task 5 (multi-instance smoke test)
    │       ├──→ Task 7 (remove compat shims)
    │       └──→ Sprint 4 (deterministic replay)
    │               └──→ Sprint 5 (true embeddability)
    │
Task 4 (eliminate current_context)
Task 6 (CI globals enforcement)

Task 9 (GUI decision) ──→ Sprint 6 (frontend convergence)
Task 14 (API unification) ──→ Task 15 (language bindings)
```

---

## Constraints

| Constraint | Description |
|------------|-------------|
| V1 Instance | Multi-instance capable (all partial globals migrated) |
| Threading | Core spawns no threads; host owns threading |
| Determinism | All randomness seedable; same inputs = same outputs |
| ABI Stability | Breaking changes require major version bump |
