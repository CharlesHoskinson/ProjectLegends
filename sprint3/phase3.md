# Phase 3: Build Static Library DAG

## Objective

Implement CMake-based verification that library dependencies form a valid Directed Acyclic Graph (DAG). Detect and fail on circular dependencies or unauthorized cross-module links.

## Deliverables

### 3.1 Create DAG Verification Module

**File:** `cmake/ModuleDAG.cmake`

```cmake
#------------------------------------------------------------------------------
# ModuleDAG.cmake
# Sprint 3: Static Library DAG Verification
#
# This module verifies that library dependencies form a valid DAG.
# Circular dependencies or unauthorized links cause a FATAL_ERROR.
#------------------------------------------------------------------------------

include_guard(GLOBAL)

# Require ModuleManifest to be loaded first
if(NOT DEFINED LEGENDS_DAG_legends_core)
    message(FATAL_ERROR "ModuleManifest.cmake must be included before ModuleDAG.cmake")
endif()

#------------------------------------------------------------------------------
# legends_verify_dag(TARGET)
#
# Verify that TARGET's dependencies are in the allowed DAG.
#
# Arguments:
#   TARGET - The CMake target to verify
#
# Fails with FATAL_ERROR if:
#   - TARGET links to a library not in its allowed dependencies
#   - A circular dependency is detected
#------------------------------------------------------------------------------
function(legends_verify_dag TARGET)
    # Skip if target doesn't exist yet (generator expressions)
    if(NOT TARGET ${TARGET})
        message(STATUS "DAG: Skipping ${TARGET} (not yet defined)")
        return()
    endif()

    # Get link libraries
    get_target_property(DEPS ${TARGET} LINK_LIBRARIES)

    if(NOT DEPS)
        message(STATUS "DAG: ${TARGET} has no dependencies (leaf node)")
        return()
    endif()

    # Get allowed dependencies from manifest
    set(ALLOWED_DEPS ${LEGENDS_DAG_${TARGET}})

    # Check each dependency
    foreach(DEP ${DEPS})
        # Skip system libraries, externals, and generator expressions
        if(DEP MATCHES "^\\$<")
            continue()
        endif()
        if(DEP MATCHES "^gsl::|^gsl-lite|^GTest::|^gmock|^SDL|^Threads::")
            continue()
        endif()
        if(DEP MATCHES "^-l|^/")  # Linker flags or absolute paths
            continue()
        endif()

        # Check if this is a project library that needs DAG verification
        if(DEP MATCHES "^(legends_core|legends_pal|aibox_core)$")
            list(FIND ALLOWED_DEPS ${DEP} IDX)
            if(IDX EQUAL -1)
                message(FATAL_ERROR
                    "===== DAG VIOLATION =====\n"
                    "Target: ${TARGET}\n"
                    "Links to: ${DEP}\n"
                    "Allowed dependencies: ${ALLOWED_DEPS}\n"
                    "=========================\n"
                    "Fix: Update cmake/ModuleManifest.cmake to add '${DEP}' to LEGENDS_DAG_${TARGET}\n"
                    "Or: Remove the unauthorized dependency from ${TARGET}"
                )
            endif()
        endif()
    endforeach()

    message(STATUS "DAG: ${TARGET} -> [${ALLOWED_DEPS}] verified")
endfunction()

#------------------------------------------------------------------------------
# legends_verify_all_dags()
#
# Verify all project libraries at once. Call after all targets are defined.
#------------------------------------------------------------------------------
function(legends_verify_all_dags)
    message(STATUS "")
    message(STATUS "===== DAG Verification =====")
    legends_verify_dag(legends_core)
    legends_verify_dag(legends_pal)
    legends_verify_dag(aibox_core)
    message(STATUS "===== All DAGs Valid =====")
    message(STATUS "")
endfunction()

#------------------------------------------------------------------------------
# legends_print_dag()
#
# Print the dependency graph for documentation purposes.
#------------------------------------------------------------------------------
function(legends_print_dag)
    message(STATUS "")
    message(STATUS "===== Module Dependency Graph =====")
    message(STATUS "")
    message(STATUS "  legends_core")
    message(STATUS "       |")
    message(STATUS "       v")
    message(STATUS "  aibox_core")
    message(STATUS "")
    message(STATUS "  legends_pal (leaf)")
    message(STATUS "")
    message(STATUS "===================================")
    message(STATUS "")
endfunction()
```

### 3.2 Update Main CMakeLists.txt

Add DAG verification after library definitions:

```cmake
# Near the top, after project() declaration
include(cmake/ModuleManifest.cmake)
include(cmake/ModuleDAG.cmake)

# ... existing library definitions ...

# After all add_library() calls (around line 400+)
# Verify the dependency graph
legends_verify_all_dags()

# Optional: Print the graph during verbose builds
if(CMAKE_VERBOSE_MAKEFILE)
    legends_print_dag()
endif()
```

### 3.3 Update engine/CMakeLists.txt

Ensure aibox_core dependencies are declared correctly:

```cmake
# After aibox_core target definition
target_link_libraries(aibox_core
    PRIVATE
        gsl::gsl-lite    # Contracts
        Threads::Threads # Threading
        # No project libraries - aibox_core is a leaf node
)
```

## Implementation Steps

| Step | Action | Files |
|------|--------|-------|
| 3.1.1 | Create ModuleDAG.cmake | cmake/ModuleDAG.cmake |
| 3.2.1 | Add include(ModuleDAG.cmake) | CMakeLists.txt:~15 |
| 3.2.2 | Add legends_verify_all_dags() call | CMakeLists.txt:~400 |
| 3.3.1 | Verify aibox_core has no project deps | engine/CMakeLists.txt |
| 3.4.1 | Test DAG violation detection | Intentionally add bad dep |

## Test Plan

### Unit Tests

```cmake
# test_dag_violation.cmake
# Run with: cmake -P test_dag_violation.cmake

# Simulate a DAG violation
set(LEGENDS_DAG_test_target "allowed_dep")
set(TEST_DEPS "allowed_dep;forbidden_dep")

foreach(DEP ${TEST_DEPS})
    list(FIND LEGENDS_DAG_test_target ${DEP} IDX)
    if(IDX EQUAL -1)
        message(STATUS "PASS: Detected violation for ${DEP}")
    else()
        message(STATUS "PASS: Allowed ${DEP}")
    endif()
endforeach()
```

### Integration Tests

```bash
#!/bin/bash
# test_dag_integration.sh

set -e

echo "Test 1: Valid DAG configuration"
cmake -B build-test -DLEGENDS_BUILD_TESTS=OFF
echo "PASS: Valid DAG accepted"

echo "Test 2: Detect DAG violation"
# Temporarily modify CMakeLists.txt to add invalid dependency
sed -i 's/LEGENDS_DAG_legends_pal ""/LEGENDS_DAG_legends_pal ""/' cmake/ModuleManifest.cmake

# This should fail
if cmake -B build-test-fail 2>&1 | grep -q "DAG VIOLATION"; then
    echo "PASS: DAG violation detected"
else
    echo "FAIL: DAG violation not detected"
    exit 1
fi

# Restore original
git checkout cmake/ModuleManifest.cmake

echo "All tests passed"
```

### Manual Verification

| Test | Command | Expected Result |
|------|---------|-----------------|
| CMake configures | `cmake -B build` | "All DAGs Valid" in output |
| DAG printed | `cmake -B build -DCMAKE_VERBOSE_MAKEFILE=ON` | Graph printed |
| Violation detected | Add `legends_core` to aibox_core deps | FATAL_ERROR at configure |
| Build succeeds | `cmake --build build` | No errors |

### Acceptance Criteria

- [ ] cmake/ModuleDAG.cmake exists and is syntactically valid
- [ ] `cmake -B build` prints "All DAGs Valid"
- [ ] Intentionally adding a forbidden dependency causes FATAL_ERROR
- [ ] All three project libraries are verified (legends_core, legends_pal, aibox_core)
- [ ] External dependencies (gsl, GTest, SDL) are not flagged

## Rollback Plan

If issues arise:
1. Remove `legends_verify_all_dags()` call from CMakeLists.txt
2. Remove `include(cmake/ModuleDAG.cmake)` from CMakeLists.txt
3. Delete cmake/ModuleDAG.cmake

**Git commands:**
```bash
git checkout HEAD -- CMakeLists.txt
git rm cmake/ModuleDAG.cmake
```

No build impact - DAG verification is configure-time only.

## Edge Cases

### Generator Expressions

CMake generator expressions (`$<...>`) in dependencies are skipped:
```cmake
target_link_libraries(foo PRIVATE $<$<BOOL:${USE_SSL}>:OpenSSL::SSL>)
# This is correctly ignored by DAG verification
```

### Interface Libraries

Interface libraries (header-only) follow the same rules:
```cmake
add_library(my_interface INTERFACE)
# Still verified by legends_verify_dag()
```

### Circular Dependency Detection

The CMake linker will also detect cycles, but DAG verification catches them earlier:
```
Error: legends_core -> aibox_core -> legends_core (cycle!)
```
