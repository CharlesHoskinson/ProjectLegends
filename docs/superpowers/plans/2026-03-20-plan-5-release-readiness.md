# Plan 5: Release Readiness

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close remaining gaps for Release A: documentation, CI coverage, Phase 3 wiring, integration test stubs, and packaging.

**Architecture:** Independent tasks covering docs, CI, wiring, and tests. Can run in parallel with other plans.

**Tech Stack:** C++23, CMake, GitHub Actions, CPack

---

### Task 1: Create CONTRIBUTING.md

**Audit ref:** Agent 12 — missing contributor guide for external developers

**Files:**
- Create: `CONTRIBUTING.md`

- [ ] **Step 1: Write contributor guide**

Cover: build instructions, code style expectations, PR process, testing requirements, license headers (GPL v2 for engine, MIT for IPC).

- [ ] **Step 2: Commit**

---

### Task 2: Create CHANGELOG.md

**Audit ref:** Agent 12 — missing user-facing release notes

**Files:**
- Create: `CHANGELOG.md`

- [ ] **Step 1: Write initial changelog in keepachangelog format**

Cover releases to date based on git history. Focus on user-facing changes.

- [ ] **Step 2: Commit**

---

### Task 3: Create CMakePresets.json

**Audit ref:** Agent 10 — developers must memorize complex option combinations

**Files:**
- Create: `CMakePresets.json`

- [ ] **Step 1: Define presets for common configurations**

Presets: `dev` (Debug, tests ON), `release` (Release, tests OFF), `asan` (Debug, ASan+UBSan), `tsan` (Debug, TSan), `ipc` (Debug, IPC mode), `coverage` (Debug, coverage flags), `fuzz` (Clang, fuzzing ON).

- [ ] **Step 2: Verify `cmake --preset dev && cmake --build --preset dev` works**
- [ ] **Step 3: Commit**

---

### Task 4: Add IPC Mode CI Job

**Audit ref:** Agent 10 — `LEGENDS_USE_IPC=ON` never tested in any CI workflow

**Files:**
- Modify: `.github/workflows/ci.yml`

- [ ] **Step 1: Add a Linux CI job with `-DLEGENDS_USE_IPC=ON`**

Build both `project_legends` (with proxy) and `legends_engine_host`. Run IPC-specific tests.

- [ ] **Step 2: Enable the IPC integration test (currently DISABLED)**
- [ ] **Step 3: Commit**

---

### Task 5: Wire Shader Renderer into Render Loop

**Audit ref:** Agent 1 (Phase 3) — ShaderRenderer complete but renderFrame() never creates GL context
**Effort:** M — the components exist, just needs wiring

**Files:**
- Modify: `src/app/application.cpp`
- Modify: `src/app/application.h`

- [ ] **Step 1: Add `use_opengl_` flag controlled by config/CLI**
- [ ] **Step 2: In `init()`, when `use_opengl_` is true, call `context_->createOpenGL()` instead of `createSoftware()`**
- [ ] **Step 3: In `renderFrame()`, when using OpenGL, call `shader_renderer_.render()` instead of lockSurface/blit/unlockSurface**
- [ ] **Step 4: Test with `--opengl` CLI flag (visual verification)**
- [ ] **Step 5: Commit**

---

### Task 6: Wire Joystick Engine Bridge

**Audit ref:** Agent 1 (Phase 3) — `legends_joystick_event()` discards all values
**Effort:** S — single function to write values into engine port registers

**Files:**
- Modify: `src/legends/legends_embed_api.cpp` (around line 2917)

- [ ] **Step 1: Implement `legends_joystick_event()` to forward to `dosbox_lib_joystick_event()`**
- [ ] **Step 2: Run joystick tests**
- [ ] **Step 3: Commit**

---

### Task 7: Wire TTF Renderer into Text Mode

**Audit ref:** Agent 1 (Phase 3) — TTFRenderer complete but never invoked
**Effort:** S — conditional in renderFrame() per text cell

**Files:**
- Modify: `src/app/application.cpp`
- Modify: `src/legends/legends_embed_api.cpp` (line 3024, `legends_set_ttf_font` TODO)

- [ ] **Step 1: In text-mode rendering path, check if TTF is enabled**
- [ ] **Step 2: If enabled, call `ttf_renderer_.renderCell()` per text cell instead of VGA font**
- [ ] **Step 3: Implement `legends_set_ttf_font()` to forward font path to engine**
- [ ] **Step 4: Run TTF renderer tests**
- [ ] **Step 5: Commit**

---

### Task 8: Implement Boot-to-Prompt Integration Test

**Audit ref:** Agent 6 — `test_boot_to_prompt.cpp` is a stub, core acceptance gate

**Files:**
- Modify: `tests/integration/test_boot_to_prompt.cpp`

- [ ] **Step 1: Replace GTEST_SKIP with actual test**

Create engine in headless mode, step for ~2 seconds of emulated time, capture text, verify DOS prompt characters (e.g., `C:\>` or `A:\>`) appear in the text capture.

- [ ] **Step 2: Run integration tests**
- [ ] **Step 3: Commit**

---

### Task 9: Fix ROADMAP Status Accuracy

**Audit ref:** Multiple agents found discrepancies between claimed and actual status

**Files:**
- Modify: `ROADMAP.md`

- [ ] **Step 1: Update Section 14 (GPL Process Isolation) from "2/16" to "12-13/16"**
- [ ] **Step 2: Update Section 9 (Security) to reflect 7 items that are partial, not complete**
- [ ] **Step 3: Update Section 12 (Quality Engineering) to reflect missing items**
- [ ] **Step 4: Update Section 13 (UX) to reflect actual 2-3/11 vs claimed 5/11**
- [ ] **Step 5: Commit**

---

### Task 10: Remove wasm.md Reference from README

**Audit ref:** Agent 12 — README project structure lists `wasm.md` but it doesn't exist

**Files:**
- Modify: `README.md`

- [ ] **Step 1: Remove or correct the wasm.md reference**
- [ ] **Step 2: Commit**

---

### Task 11: Move Global Compile Options to Interface Library

**Audit ref:** Agent 10 — `add_compile_options()` leaks into FetchContent dependencies

**Files:**
- Modify: `CMakeLists.txt`

- [ ] **Step 1: Create an INTERFACE library for project warning/hardening flags**

```cmake
add_library(legends_compile_options INTERFACE)
target_compile_options(legends_compile_options INTERFACE
    $<$<CXX_COMPILER_ID:GNU,Clang>:-Wall -Wextra -Wpedantic>
    $<$<CXX_COMPILER_ID:MSVC>:/W4 /permissive->)
```

- [ ] **Step 2: Replace global `add_compile_options()` with per-target linking to the interface library**
- [ ] **Step 3: Verify FetchContent targets (GoogleTest, SDL3, gsl-lite) no longer receive project warnings**
- [ ] **Step 4: Full build + test**
- [ ] **Step 5: Commit**
