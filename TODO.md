# Project Legends - Development Roadmap

## Immediate Priorities

### 1. Compilation & Build Integration

- [ ] **Wire engine to top-level CMakeLists.txt**
  - Add `add_subdirectory(engine)` to root CMakeLists.txt
  - Link `aibox_core` library to `legends_core`
  - Resolve any duplicate symbol issues between engine and embedding layer

- [ ] **Verify headless build compiles**
  - Build with `-DAIBOX_HEADLESS=ON -DAIBOX_LIBRARY_MODE=ON`
  - Fix any missing includes or link errors
  - Ensure all 4,000+ tests pass

- [ ] **Cross-platform build verification**
  - Linux (GCC 13+)
  - Windows (MSVC 2022 / MinGW)
  - macOS (Clang 16+)

### 2. GUI Testing

- [ ] **Assess DOSBox-X GUI survival**
  - Check if `src/gui/` menu system is intact
  - Check if mapper (keyboard configuration) works
  - Document what GUI features are available vs missing

- [ ] **SDL2 backend GUI test**
  - Build with `-DPAL_BACKEND_SDL2=ON`
  - Verify window creation, rendering, input
  - Test fullscreen toggle
  - Test menu bar functionality

- [ ] **SDL3 backend GUI test**
  - Build with `-DPAL_BACKEND_SDL3=ON`
  - Verify SDL3-specific changes work (texture rendering, audio stream)
  - Document any SDL3 API issues

- [ ] **GUI decision point**
  - Option A: Keep DOSBox-X GUI for standalone executable
  - Option B: Strip GUI, headless-only for v1
  - Option C: New minimal GUI with imgui or similar

### 3. LLM Integration Testing

- [ ] **Basic frame capture test**
  - Create instance, step, capture text frame
  - Verify JSON serialization works
  - Verify canonical text format works

- [ ] **Token estimation accuracy**
  - Compare `aibox_llm_estimate_tokens()` against actual tokenizer
  - Tune estimation parameters if needed

- [ ] **Action batch execution**
  - Test `aibox_llm_execute_batch()` with keyboard actions
  - Test mouse movement actions
  - Test special key sequences (Ctrl+C, Alt+F4, etc.)

- [ ] **End-to-end LLM agent test**
  - Boot DOS
  - Have LLM agent navigate DIR command
  - Verify deterministic replay of agent actions

- [ ] **Game testing targets**
  - Oregon Trail
  - Zork
  - Commander Keen
  - DOOM (as stress test)

### 4. Engine Refactoring (Remaining Work)

- [ ] **Complete global migration (17 remaining)**
  - Review `globals_registry.yaml` for pending items
  - Prioritize determinism-relevant globals
  - Update registry as migrations complete

- [ ] **Multi-instance support (V2 contract)**
  - Requires 100% global migration
  - Add tests for concurrent instance creation
  - Update CONTRACT.md when V2 is achieved

- [ ] **Remove dead code**
  - Identify unused DOSBox-X features
  - Remove networking code if not needed
  - Remove printer/parallel port if not needed

- [ ] **Performance optimization**
  - Profile CPU emulation hot paths
  - Consider dynamic recompilation for heavy workloads
  - Optimize frame capture for high-frequency polling

---

## Medium-Term Goals

### API Refinement

- [ ] Unify `legends_embed.h` and `aibox/ffi_*.h` APIs
- [ ] Decide on single API surface vs dual APIs
- [ ] Add Rust bindings (`legends-rs` crate)
- [ ] Add Python bindings (`pylegends` package)

### Testing Infrastructure

- [ ] Golden file tests for determinism verification
- [ ] Fuzzing harness for input handling
- [ ] Performance regression tests
- [ ] Memory leak detection in CI (Valgrind/ASan)

### Documentation

- [ ] API reference documentation (Doxygen)
- [ ] Integration guide for Rust/Python hosts
- [ ] Game compatibility database
- [ ] Troubleshooting guide

---

## Long-Term Vision

### Multi-Instance (V2)

- Complete global state migration
- Thread-safe instance creation
- Per-instance memory isolation

### GPU Acceleration

- OpenGL rendering backend
- Vulkan rendering backend
- GPU-accelerated VGA emulation

### Extended Platform Support

- WebAssembly build
- iOS/Android builds
- Embedded systems (Raspberry Pi)

### Advanced LLM Features

- Semantic screen region detection
- OCR integration for non-text modes
- Action suggestion API
- Reward signal computation for RL

---

## Notes

- **V1 Constraint**: Single instance per process due to remaining globals
- **Threading Model**: Core never spawns threads; host owns all threading decisions
- **Determinism**: All randomness must be seedable; same inputs = same outputs
- **ABI Stability**: Breaking changes require major version bump

---

*Last updated: January 2025*
