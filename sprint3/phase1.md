# Phase 1: Define Module Boundaries

## Objective

Establish formal module definitions and document the allowed dependency graph between modules.

## Deliverables

### 1.1 Create Module Manifest

**File:** `cmake/ModuleManifest.cmake`

```cmake
# Sprint 3 Module Graph - Module Definitions
#
# This file defines the formal module boundaries and allowed dependencies.
# Violations are detected at configure time via ModuleDAG.cmake.

#------------------------------------------------------------------------------
# Module: legends
# Purpose: Embeddable x86 emulation framework with stable C ABI
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_LEGENDS_PUBLIC_INCLUDE "include/legends")
set(LEGENDS_MODULE_LEGENDS_PRIVATE_INCLUDE "src/legends")
set(LEGENDS_MODULE_LEGENDS_TARGET "legends_core")

#------------------------------------------------------------------------------
# Module: pal (Platform Abstraction Layer)
# Purpose: Platform-agnostic interfaces for I/O, audio, timing, input
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_PAL_PUBLIC_INCLUDE "include/pal")
set(LEGENDS_MODULE_PAL_PRIVATE_INCLUDE "src/pal")
set(LEGENDS_MODULE_PAL_TARGET "legends_pal")

#------------------------------------------------------------------------------
# Module: engine
# Purpose: DOSBox-X core with library mode API
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_ENGINE_PUBLIC_INCLUDE "engine/include/dosbox;engine/include/aibox")
set(LEGENDS_MODULE_ENGINE_PRIVATE_INCLUDE "engine/include;engine/src")
set(LEGENDS_MODULE_ENGINE_TARGET "aibox_core")

#------------------------------------------------------------------------------
# Dependency Graph (DAG)
#
# legends_core --> aibox_core (legends depends on engine)
# legends_pal --> (nothing, leaf node)
# aibox_core --> (nothing, leaf node)
#------------------------------------------------------------------------------
set(LEGENDS_DAG_legends_core "aibox_core")
set(LEGENDS_DAG_legends_pal "")
set(LEGENDS_DAG_aibox_core "")

#------------------------------------------------------------------------------
# Public Header Allowlists
# Only these directories can be included cross-module
#------------------------------------------------------------------------------
set(LEGENDS_PUBLIC_HEADERS
    "include/legends"
    "include/pal"
    "engine/include/dosbox"
    "engine/include/aibox"
)

#------------------------------------------------------------------------------
# Forbidden Include Patterns
# These patterns indicate module boundary violations
#------------------------------------------------------------------------------
set(LEGENDS_FORBIDDEN_PATTERNS
    "../src/"           # Public header reaching into private source
    "../../"            # Cross-module private include
    "engine/src/"       # Direct include of engine internals
)
```

### 1.2 Update ARCHITECTURE.md

Add a new section documenting the module graph:

```markdown
## Module Graph (Sprint 3)

### Module Definitions

| Module | Public Headers | Private Sources | Library Target | Tier |
|--------|---------------|-----------------|----------------|------|
| legends | include/legends/ | src/legends/ | legends_core | A (strict) |
| pal | include/pal/ | src/pal/ | legends_pal | A (strict) |
| engine | engine/include/dosbox/, engine/include/aibox/ | engine/src/, engine/include/ | aibox_core | B (legacy) |

### Dependency Rules

1. **legends_core** may depend on **aibox_core** only
2. **legends_pal** has no module dependencies (leaf node)
3. **aibox_core** has no module dependencies (leaf node)
4. Cross-module includes MUST use public header paths only
5. No `../src/` includes in public headers

### Include Path Convention

- Public: `#include "legends/foo.h"` or `#include "dosbox/bar.h"`
- Private: `#include "internal/baz.h"` (within same module only)
```

## Implementation Steps

| Step | Action | Files |
|------|--------|-------|
| 1.1.1 | Create cmake/ModuleManifest.cmake | New file |
| 1.1.2 | Add include(cmake/ModuleManifest.cmake) to CMakeLists.txt | CMakeLists.txt:~15 |
| 1.2.1 | Add Module Graph section to ARCHITECTURE.md | ARCHITECTURE.md |
| 1.2.2 | Update TODO.md to mark Phase 1 complete | TODO.md |

## Test Plan

### Unit Tests

None required - this phase is documentation only.

### Integration Tests

None required - this phase is documentation only.

### Manual Verification

| Test | Command | Expected Result |
|------|---------|-----------------|
| CMake parses manifest | `cmake -B build` | No errors, MODULE variables defined |
| Manifest loads | `cmake -B build -DCMAKE_VERBOSE_MAKEFILE=ON` | See "Loading ModuleManifest.cmake" in output |
| Variables accessible | Add `message(STATUS "DAG: ${LEGENDS_DAG_legends_core}")` | Prints "DAG: aibox_core" |

### Acceptance Criteria

- [ ] `cmake/ModuleManifest.cmake` exists and is syntactically valid
- [ ] CMakeLists.txt includes the manifest
- [ ] ARCHITECTURE.md updated with Module Graph section
- [ ] `cmake -B build` succeeds without errors
- [ ] All three DAG variables are defined and non-empty (except leaf nodes)

## Rollback Plan

If issues arise:
1. Remove `include(cmake/ModuleManifest.cmake)` from CMakeLists.txt
2. Delete cmake/ModuleManifest.cmake
3. Revert ARCHITECTURE.md changes

No build impact - this phase is additive only.
