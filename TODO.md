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

## Refactoring Roadmap

The refactoring effort follows a deliberate sequence. Each sprint builds on the previous, unlocking capabilities that would be difficult or impossible to add out of order.

---

### Sprint 1 — Library Foundation (Complete)

The foundation sprint delivered a stable embedding API, platform abstraction, and deterministic execution within a single-instance constraint. The engine can be driven as a library, but it still carries some application-like assumptions internally.

- [x] **Stable C API boundary** — The `legends_embed.h` header provides a versioned ABI that host applications can link against without worrying about C++ name mangling or internal implementation changes.

- [x] **Platform Abstraction Layer** — The PAL cleanly separates platform-specific code (SDL2, SDL3, headless) from the engine core, allowing the same emulation code to run in any environment.

- [x] **Contract gate enforcement** — All 23 architectural invariants are mechanically verified in CI, preventing regressions in thread safety, determinism, and lifecycle management.

- [x] **Determinism tests passing** — The engine produces identical output given identical inputs, verified by state hash comparisons across runs.

- [ ] **Remaining constraint** — The 17 unmigrated globals restrict the engine to one instance per process until Sprint 2 completes.

---

### Sprint 2 — Instance Reality

This sprint eliminates the single-instance constraint. Every piece of mutable state moves into the context structure. The engine transforms from "an application you can drive as a library" into "a library that happens to emulate DOS."

- [ ] **Eliminate transitional escape hatches** — Remove thread-local `current_context()` accessors, global registries, and static caches that were acceptable shortcuts during Sprint 1 but prevent true multi-instance operation.

- [ ] **Explicit subsystem ownership** — CPU state, PIC/PIT scheduler, memory maps, VGA framebuffer, DOS kernel structures, and device registries all become members of `ctx->subsystem` rather than ambient globals.

- [ ] **Parameterize cross-subsystem calls** — Functions that previously grabbed globals to communicate across subsystems now accept context pointers or use instance-owned service interfaces.

- [ ] **Multi-instance smoke test** — Create two handles in one process, run interleaved traces (A steps 10ms, B steps 10ms, repeat), and verify both produce correct isolated state hashes without cross-contamination.

- [ ] **CI enforcement of global registry** — New globals fail CI unless explicitly justified and recorded in `globals_registry.yaml`, treating global elimination as a ledger rather than a guideline.

- [ ] **Threading boundary formalization** — Document and enforce that no PAL thread may call into core, making thread-local context usage illegal on audio and input threads.

---

### Sprint 3 — Module Graph

This sprint transforms the codebase from "900k lines of inherited code" into a proper module graph with explicit edges, stable interfaces, and enforceable boundaries.

- [ ] **Define module public headers** — Each subsystem (`cpu`, `hw_bus`, `hw_video`, `hw_audio`, `dos`, `ints`, `shell`) exposes a small set of public headers; everything else becomes private implementation detail.

- [ ] **Eliminate cross-module path includes** — No source file may include headers from sibling directories by relative path; all cross-module dependencies go through the defined public interfaces.

- [ ] **Build as static library DAG** — The engine compiles as a set of static libraries with a defined dependency graph, making the architecture visible in the build system itself.

- [ ] **Introduce service interfaces** — Where modules previously communicated through shared globals, define explicit service interfaces that can be passed through the context or injected at initialization.

- [ ] **CI include rule enforcement** — Automated checks prevent forbidden cross-module includes from entering the codebase, catching architectural violations before they merge.

- [ ] **Measure rebuild improvement** — Track and document the reduction in rebuild fan-out; editing VGA code should no longer force recompilation of DOS shell code.

---

### Sprint 4 — Deterministic Replay as Product

This sprint promotes determinism from a test strategy to a first-class capability. Instead of "we have determinism tests," we ship deterministic replay tooling.

- [ ] **First-class state hash API** — The state hash becomes a documented public API with stability guarantees, not just a test helper buried in the test suite.

- [ ] **Versioned snapshot schema** — Save states include explicit schema identifiers, endianness markers, and alignment guarantees, making them portable across platforms and forward-compatible across versions.

- [ ] **Trace format specification** — Define a documented format for encoding input traces, stepping schedules, and optional capture checkpoints that can be stored, exchanged, and replayed.

- [ ] **Differential debugging runner** — Build tooling that compares two runs (different engine versions, backends, toolchains, or instances) and localizes the first divergence to a specific subsystem boundary.

- [ ] **Fast CI trace corpus** — Curate a suite of small, fast traces that run on every commit and catch obvious determinism regressions within seconds.

- [ ] **Nightly soak suite** — Maintain longer-running traces that execute for minutes or hours, catching rare timing-dependent bugs that only manifest after extended operation.

---

### Sprint 5 — True Embeddability

This sprint removes application policy from the engine. The engine becomes well-behaved inside other programs: no implicit config discovery, no environment sniffing, no filesystem assumptions, no interactive prompts.

- [ ] **In-memory configuration only** — Configuration becomes purely data passed at initialization; file path handling becomes an optional host convenience layer rather than engine behavior.

- [ ] **Abstracted filesystem access** — All file and device I/O moves behind an explicit abstraction layer that can operate in denylist mode, returning errors for unauthorized access rather than silently failing.

- [ ] **No implicit environment access** — The engine never reads `argv`, environment variables, or the current working directory without explicit host instruction; all such access is injectable.

- [ ] **Interactive behavior extraction** — Any prompting, dialog, or UI behavior moves to frontend wrappers; the engine core remains non-interactive and returns structured results for all operations.

- [ ] **Sandbox compatibility verification** — The engine runs successfully in restricted sandbox environments (seccomp, AppArmor, container isolation) and returns structured errors rather than crashing on denied operations.

---

### Sprint 6 — Frontend Convergence

This sprint simplifies the frontend story. SDL3 becomes the primary interactive backend; SDL2 is deprecated and eventually removed. Optionally, a remote control interface enables browser-based or networked operation.

- [ ] **SDL2 deprecation** — Mark the SDL2 backend as deprecated in documentation and emit warnings when it is used, directing users toward SDL3 or headless.

- [ ] **SDL3 performance tuning** — Optimize the SDL3 presentation path, input mapping correctness, and audio queue behavior to match or exceed SDL2 quality.

- [ ] **SDL2 removal** — Remove the SDL2 backend entirely once SDL3 has proven stable, reducing the maintenance matrix and test burden.

- [ ] **Blessed configuration documentation** — Center all documentation and packaging around three configurations: headless deterministic CI runner, SDL3 interactive application, and optional remote control tooling.

- [ ] **Optional remote control station** — Ship tooling (browser UI or lightweight desktop app) that connects to the engine over a local protocol, leveraging the stable C ABI for control and observation.

- [ ] **Product-quality packaging** — Distribution becomes straightforward and repeatable; the project presents as a finished product rather than a research fork.

---

### Roadmap Summary

| Sprint | Unlock |
|--------|--------|
| Sprint 2 | Correctness becomes composable — instances are real |
| Sprint 3 | Codebase becomes survivable — modules are real |
| Sprint 4 | Evolution becomes safe — behavior is pinned |
| Sprint 5 | Embedding becomes predictable — policy is explicit |
| Sprint 6 | Project becomes shippable — frontend converges |

Each sprint builds on the previous. Skipping ahead creates technical debt that compounds. The sequence prioritizes correctness, then maintainability, then velocity, then polish.

---

## Future Possibilities

These are not scheduled but represent potential directions after V6:

- **GPU Acceleration**: OpenGL/Vulkan rendering backends, GPU-accelerated VGA emulation
- **Extended Platforms**: WebAssembly, iOS/Android, embedded systems
- **Advanced LLM Features**: Semantic region detection, OCR for graphics modes, action suggestion API, reward signals for RL
- **Language Bindings**: Rust crate (`legends-rs`), Python package (`pylegends`)

---

## Notes

- **V1 Constraint**: Single instance per process due to remaining globals
- **Threading Model**: Core never spawns threads; host owns all threading decisions
- **Determinism**: All randomness must be seedable; same inputs = same outputs
- **ABI Stability**: Breaking changes require major version bump
