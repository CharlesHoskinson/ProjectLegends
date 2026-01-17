# Project Legends — Development Roadmap

## Current Status

**Sprint 1** — Library Foundation: Complete
**Sprint 2** — Instance Reality: In Progress (Phase 2 save/load complete)
**Sprint 3** — Module Graph: Complete

---

## Immediate Priorities

### 1. Build Integration

- [x] Wire engine to top-level CMakeLists.txt
- [x] Headless build compiles (`-DAIBOX_HEADLESS=ON -DAIBOX_LIBRARY_MODE=ON`)
- [ ] Cross-platform verification (Linux GCC, Windows MSVC/MinGW, macOS Clang)

### 2. GUI Testing

- [ ] Assess DOSBox-X GUI survival (`src/gui/` menu, mapper)
- [ ] SDL2 backend test (window, rendering, input, fullscreen)
- [ ] SDL3 backend test (texture rendering, audio stream)
- [ ] GUI decision: keep DOSBox-X GUI, strip for headless-only, or replace

### 3. LLM Integration

- [ ] Frame capture test (create → step → capture text)
- [ ] Token estimation accuracy validation
- [ ] Action batch execution (`aibox_llm_execute_batch`)
- [ ] End-to-end agent test (boot DOS, run DIR, verify replay)
- [ ] Game targets: Oregon Trail, Zork, Commander Keen, DOOM

### 4. Engine Refactoring

- [ ] Complete global migration (17 remaining per `globals_registry.yaml`)
- [ ] Multi-instance support (requires 100% global migration)
- [ ] Remove dead code (networking, printer/parallel if unused)
- [ ] Performance profiling of CPU emulation hot paths

---

## Sprint 1 — Library Foundation (Complete)

- [x] Stable C API boundary (`legends_embed.h`)
- [x] Platform Abstraction Layer (headless, SDL2, SDL3)
- [x] Contract gate enforcement (23 invariants)
- [x] Determinism tests passing
- [x] Single-instance constraint documented

---

## Sprint 2 — Instance Reality (In Progress)

### Phase 1 — CPU Bridge (Complete)

- [x] `dosbox_lib_step_cycles()` wired to CPU bridge
- [x] `execute_cycles()` implemented (stub for library mode)
- [x] Timing state synchronization between layers
- [x] Rounding-error fix for deterministic time computation

### Phase 2 — Save/Load State (Complete)

- [x] Engine state serialization format (`engine_state.h`)
- [x] `dosbox_lib_save_state()` serializes timing, PIC, keyboard
- [x] `dosbox_lib_load_state()` restores engine state
- [x] Legends layer includes engine state in save format
- [x] CRC32 integrity verification
- [x] Security hardening (bounds validation, size checks)
- [x] TLA+ round-trip invariant verified by tests

### Phase 3 — State Synchronization

- [x] `sync_state_from_engine()` after stepping
- [x] Engine reset integrated into `legends_reset()`
- [x] No sync after load (state already restored)

### Remaining Sprint 2 Work

- [ ] Eliminate thread-local `current_context()` accessors
- [ ] Move all subsystem state to `ctx->subsystem`
- [ ] Multi-instance smoke test (interleaved A/B stepping)
- [ ] CI enforcement preventing new globals

---

## Sprint 3 — Module Graph (Complete)

### Phase 1 — Define Module Boundaries (Complete)

- [x] Create `cmake/ModuleManifest.cmake` with module definitions
- [x] Define DAG: legends_core → aibox_core, leaves: legends_pal, aibox_core
- [x] Update ARCHITECTURE.md with Module Graph section
- [x] Include manifest in CMakeLists.txt

### Phase 2 — Fix Cross-Module Path Includes (Complete)

- [x] Fix builtin.h (12 ../src/ violations)
- [x] Fix bios_disk.h (1 ../src/ violation)
- [x] Fix render.h (1 ../src/ violation)
- [x] Create `engine/include/dosbox/builtin_types.h`
- [x] Create `engine/include/dosbox/cdrom_interface.h`
- [x] Create `engine/include/dosbox/render_types.h`

### Phase 3 — Build Static Library DAG (Complete)

- [x] Create `cmake/ModuleDAG.cmake` with verification function
- [x] Integrate DAG verification into CMakeLists.txt
- [x] Add `legends_print_dag()` for verbose builds
- [x] Add circular dependency detection

### Phase 4 — Service Interfaces (Complete)

- [x] Create `engine/include/dosbox/engine_services.h`
- [x] Add `EngineServiceTable` for dependency injection
- [x] Add `EngineHandle` RAII wrapper
- [x] Update ARCHITECTURE.md with Service Interfaces section

### Phase 5 — CI Include Rule Enforcement (Complete)

- [x] Create `scripts/check_includes.py`
- [x] Create `.github/workflows/module-dag.yml`
- [x] Create `.githooks/pre-commit` hook
- [x] Add Linux and Windows build verification

### Phase 6 — Measure Rebuild Improvement (Complete)

- [x] Create `scripts/measure_rebuild.py`
- [x] Add Build Metrics section to ARCHITECTURE.md
- [x] Capture metrics: all targets met (<3s header, <2s cpp)

---

## Sprint 4 — Deterministic Replay as Product

- [ ] First-class state hash API with stability guarantees
- [ ] Versioned snapshot schema (portable, forward-compatible)
- [ ] Trace format specification
- [ ] Differential debugging runner
- [ ] Fast CI trace corpus
- [ ] Nightly soak suite

---

## Sprint 5 — True Embeddability

- [ ] In-memory configuration only
- [ ] Abstracted filesystem access
- [ ] No implicit environment access
- [ ] Interactive behavior extraction
- [ ] Sandbox compatibility verification

---

## Sprint 6 — Frontend Convergence

- [ ] SDL2 deprecation
- [ ] SDL3 performance tuning
- [ ] SDL2 removal
- [ ] Blessed configuration documentation
- [ ] Optional remote control station
- [ ] Product-quality packaging

---

## Medium-Term Goals

### API Refinement

- [ ] Unify `legends_embed.h` and `aibox/ffi_*.h` APIs
- [ ] Rust bindings (`legends-rs` crate)
- [ ] Python bindings (`pylegends` package)

### Testing Infrastructure

- [ ] Golden file tests for determinism
- [ ] Fuzzing harness for save/load
- [ ] Performance regression tests
- [ ] Memory leak detection (Valgrind/ASan)

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

## Constraints

| Constraint | Description |
|------------|-------------|
| V1 Instance | Single instance per process (17 globals remaining) |
| Threading | Core spawns no threads; host owns threading |
| Determinism | All randomness seedable; same inputs = same outputs |
| ABI Stability | Breaking changes require major version bump |
