# Contributing to Project Legends

Thank you for your interest in contributing to Project Legends. This document
covers the build process, code conventions, testing requirements, and pull
request workflow.

---

## Table of Contents

- [Getting Started](#getting-started)
- [Build Instructions](#build-instructions)
- [Code Style](#code-style)
- [Testing Requirements](#testing-requirements)
- [Pull Request Process](#pull-request-process)
- [License Headers](#license-headers)
- [Project Layout](#project-layout)

---

## Getting Started

### Prerequisites

- **C++23 compiler:** GCC 13+, Clang 18+, or MSVC 17.8+ (VS 2022)
- **CMake 3.20+**
- **Ninja** (recommended) or Make
- **Git**

Optional:
- **SDL3** for graphical builds (fetched automatically if not found)
- **lcov / genhtml** for coverage reports
- **clang-tidy 18** for static analysis
- **wasi-sdk** for Wasm builds

### Clone and Build

```bash
git clone https://github.com/CharlesHoskinson/projectLegends.git
cd projectLegends

# Debug build with tests (default developer workflow)
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DLEGENDS_BUILD_TESTS=ON \
  -DLEGENDS_HEADLESS=ON

cmake --build build
ctest --test-dir build --output-on-failure
```

---

## Build Instructions

### CMake Options

| Option | Default | Description |
|--------|---------|-------------|
| `LEGENDS_BUILD_TESTS` | OFF | Build unit, integration, and ABI tests |
| `LEGENDS_HEADLESS` | OFF | Headless mode (no GUI dependency) |
| `LEGENDS_USE_IPC` | OFF | GPL v2 process isolation mode |
| `PAL_BACKEND_SDL3` | OFF | Build with SDL3 backend |
| `PAL_BACKEND_SDL2` | OFF | Build with SDL2 backend |
| `ENABLE_FUZZING` | OFF | Build libFuzzer fuzz targets (requires Clang) |
| `ENABLE_ASAN` | OFF | AddressSanitizer for fuzz targets |
| `LEGENDS_BUILD_BENCHMARKS` | OFF | Build performance benchmarks |
| `LEGENDS_BUILD_WASM` | OFF | Wasm/WASI target |

### Common Build Configurations

```bash
# Release build
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=Release -DLEGENDS_HEADLESS=ON

# IPC mode (builds legends_engine_host + legends_proxy)
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DLEGENDS_BUILD_TESTS=ON \
  -DLEGENDS_HEADLESS=ON \
  -DLEGENDS_USE_IPC=ON

# AddressSanitizer + UndefinedBehaviorSanitizer
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_COMPILER=clang++-18 \
  -DCMAKE_CXX_FLAGS="-stdlib=libc++ -fsanitize=address,undefined -fno-omit-frame-pointer" \
  -DLEGENDS_BUILD_TESTS=ON \
  -DLEGENDS_HEADLESS=ON
```

### Running Tests

```bash
# All tests (excluding soak)
ctest --test-dir build --output-on-failure

# Unit tests only
ctest --test-dir build -L unit --output-on-failure

# Integration tests only
ctest --test-dir build -L integration --label-exclude soak --output-on-failure

# Specific test suite
./build/legends_unit_tests --gtest_filter="*SaveState*"
```

---

## Code Style

### Language Standard

All new code uses **C++23**. The project enforces this per-target via
`legends_set_strict_cxx_standard()`.

### Contracts

We use **gsl-lite** contracts (`Expects`, `Ensures`) for precondition and
postcondition checking. In library mode, contract violations throw; in
standalone mode, they terminate.

```cpp
#include <gsl/gsl-lite.hpp>

void set_volume(int level) {
    Expects(level >= 0 && level <= 100);
    // ...
    Ensures(current_volume_ == level);
}
```

### Naming Conventions

- **Types:** `PascalCase` (`MachineContext`, `SaveStateHeader`)
- **Functions/methods:** `snake_case` (`step_ms`, `capture_rgb`)
- **Constants/enums:** `UPPER_SNAKE_CASE` (`LEGENDS_OK`, `MAX_FRAME_WIDTH`)
- **Member variables:** `snake_case_` with trailing underscore
- **Namespaces:** `lowercase` (`legends`, `pal`)
- **Files:** `snake_case.cpp` / `snake_case.h`

### C API Surface

The public API (`include/legends/legends_embed.h`) is pure C11. It must:
- Compile with `gcc -std=c11 -Werror`
- Use only C-compatible types (no C++ types, no exceptions)
- Prefix all symbols with `legends_`
- Return error codes (`legends_status_t`), never throw

### Warning Policy

The project uses a two-tier warning strategy:

- **Tier A** (new/refactored code): `-Wall -Wextra -Wpedantic -Werror`
  Applied via `legends_set_strict_cxx_standard()`
- **Tier B** (legacy engine code): `-Wall -Wextra -Wpedantic` without `-Werror`
  Applied via `legends_set_legacy_cxx_standard()`

### Formatting

- Indentation: 4 spaces (no tabs)
- Braces: Allman or K&R (follow surrounding code)
- Line length: 100 characters soft limit
- Include order: project headers, then third-party, then standard library

---

## Testing Requirements

### Before Submitting a PR

1. **All existing tests pass** on your local build
2. **New code has tests** -- unit tests for new functions, integration tests
   for new workflows
3. **No new warnings** with `-Werror` on GCC and Clang
4. **ABI test passes** if you modified `legends_embed.h`

### Test Categories

| Label | Directory | Description |
|-------|-----------|-------------|
| `unit` | `tests/unit/` | Fast isolated tests |
| `integration` | `tests/integration/` | Multi-component workflow tests |
| `abi` | `tests/unit/test_legends_abi.c` | C11 ABI compatibility |
| `toolchain` | `tests/toolchain/` | Compiler/standard verification |
| `soak` | `tests/integration/test_soak_*` | Long-running endurance (CI-only) |
| `fuzz` | `tests/fuzz/` | libFuzzer targets |

### Coverage

The project targets 80% line coverage for `src/app/`. Coverage is checked
in CI on release tags.

---

## Pull Request Process

1. **Fork and branch** from `master`
2. **Make focused commits** -- one logical change per commit
3. **Write descriptive commit messages** -- use imperative mood, explain "why"
4. **Ensure CI passes** -- the PR must pass Linux (GCC + Clang), Windows
   (MSVC), and macOS (AppleClang) builds
5. **Add tests** for new functionality
6. **Update documentation** if the change affects the public API or
   architecture

### CI Checks

PRs run the following CI jobs:
- Linux headless (GCC-13, Clang-18)
- Windows headless (MSVC)
- macOS headless (AppleClang)
- C ABI verification
- Static analysis (clang-tidy)
- Fuzz testing (30s smoke)
- Sanitizer builds (ASan, UBSan, **enforced TSan**)

Nightly / `workflow_dispatch` also runs dependency scanning (osv-scanner over
vendored trees; see `osv-scanner.toml` for issue-linked baseline ignores).

**MSan** is retired from CI until an instrumented libc++ is available
([#40](https://github.com/CharlesHoskinson/ProjectLegends/issues/40)).

Known TSan races are listed in `tsan-suppressions.txt` (one entry per family,
each with a tracking issue). Do not widen suppressions without review.

### Lane demotion rule (R1)

Any of the following is a **demotion** and **MUST** land with a tracked GitHub
issue that states an explicit exit criterion (when the demotion is removed):

- `allow_failure` / `continue-on-error` on a gate job or step
- `|| true` (or equivalent) that swallows a gate failure
- Retiring or narrowing a lane's trigger tier
- Deleting or relaxing a test assertion solely to make CI green
- Adding a TSan suppression or `DISABLED_` / `GTEST_SKIP` that hides a real bug
  (intentional contract tests under TSan are the documented exception; see #45)

YAML comments alone do **not** count as an exit plan. Prefer fixing the root
cause; if temporary relief is required, open the issue first, link it from the
code/workflow, and remove the demotion in the PR that closes the issue.

See `CI-THESIS.md` (R1) and `openspec/changes/ci-stabilize-mandatory-lanes/`.

---

## License Headers

Project Legends is a multi-component project. **Every source file must
include the correct SPDX license header.**

### GPL-2.0-or-later (engine and core code)

Applies to: `engine/`, `src/legends/`, `src/engine_host/`, `src/pal/`,
`include/legends/`, `include/pal/`

```cpp
// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (c) 2024-2025 Charles Hoskinson and Contributors
```

### MIT (IPC protocol code)

Applies to: `include/legends_ipc/`, `src/legends_ipc/`, `src/legends_proxy/`

```cpp
// SPDX-License-Identifier: MIT
// Copyright (c) 2024-2025 Charles Hoskinson and Contributors
```

When in doubt, check the `NOTICE` file for per-directory license assignments.

---

## Project Layout

```
engine/            DOSBox-X core engine (GPL-2.0-or-later)
include/legends/   Public C API headers (GPL-2.0-or-later)
include/pal/       Platform abstraction interfaces (GPL-2.0-or-later)
include/legends_ipc/  IPC protocol headers (MIT)
src/legends/       Legends embedding layer (GPL-2.0-or-later)
src/pal/           PAL backend implementations (GPL-2.0-or-later)
src/app/           Application shell code (GPL-2.0-or-later)
src/engine_host/   Engine host process (GPL-2.0-or-later)
src/legends_ipc/   IPC serialization library (MIT)
src/legends_proxy/  IPC proxy for legends_embed.h (MIT)
tests/             All test code
spec/tla/          TLA+ formal specifications
```

---

## Questions?

Open an issue on GitHub or check existing issues for guidance on where to
contribute.
