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

# ─────────────────────────────────────────────────────────────────────────────
# DAG Verification Function
# ─────────────────────────────────────────────────────────────────────────────

#[[
legends_verify_dag(TARGET)

Verifies that TARGET only links to allowed internal dependencies.
External dependencies are always permitted (handled by whitelist patterns).

Arguments:
    TARGET - The CMake target name to verify

Fails with FATAL_ERROR if:
    - TARGET links to an internal library not in LEGENDS_DAG_${TARGET}
    - Circular dependency would be created

Example:
    legends_verify_dag(legends_core)
    # Checks that legends_core only links to aibox_core (as defined in manifest)
]]
function(legends_verify_dag TARGET)
    # Get the target's direct link dependencies
    get_target_property(DEPS ${TARGET} LINK_LIBRARIES)

    # Handle case where target has no dependencies
    if(NOT DEPS OR "${DEPS}" STREQUAL "DEPS-NOTFOUND")
        message(STATUS "DAG: ${TARGET} has no dependencies (OK)")
        return()
    endif()

    # Get allowed internal dependencies from manifest
    set(ALLOWED_DEPS ${LEGENDS_DAG_${TARGET}})

    # External dependency whitelist patterns
    # These are always allowed regardless of DAG rules
    set(EXTERNAL_PATTERNS
        "^gsl::"           # gsl-lite library
        "^GTest::"         # Google Test
        "^SDL"             # SDL libraries (SDL2::, SDL3::, etc.)
        "^benchmark::"     # Google Benchmark
        "^\\$<"            # CMake generator expressions
        "^-"               # Linker flags
        "^mingw"           # MinGW runtime
    )

    set(VIOLATIONS "")

    foreach(DEP ${DEPS})
        set(IS_EXTERNAL FALSE)

        # Check if dependency matches external whitelist
        foreach(PATTERN ${EXTERNAL_PATTERNS})
            if(DEP MATCHES "${PATTERN}")
                set(IS_EXTERNAL TRUE)
                break()
            endif()
        endforeach()

        if(IS_EXTERNAL)
            # External dependency - always allowed
            continue()
        endif()

        # Check if it's a known internal target
        if(TARGET ${DEP})
            # Verify against allowed dependencies
            list(FIND ALLOWED_DEPS ${DEP} IDX)
            if(IDX EQUAL -1)
                list(APPEND VIOLATIONS "${DEP}")
            endif()
        endif()
    endforeach()

    # Report any violations
    if(VIOLATIONS)
        list(REMOVE_DUPLICATES VIOLATIONS)
        string(REPLACE ";" ", " VIOLATION_STR "${VIOLATIONS}")
        string(REPLACE ";" ", " ALLOWED_STR "${ALLOWED_DEPS}")

        message(FATAL_ERROR
            "DAG Violation: ${TARGET} links to unauthorized dependencies!\n"
            "  Unauthorized: ${VIOLATION_STR}\n"
            "  Allowed: ${ALLOWED_STR}\n"
            "  \n"
            "  To fix: Update cmake/ModuleManifest.cmake if the dependency is intentional,\n"
            "  or remove the dependency from ${TARGET}'s target_link_libraries()."
        )
    endif()

    message(STATUS "DAG: ${TARGET} -> [${ALLOWED_DEPS}] verified")
endfunction()

# ─────────────────────────────────────────────────────────────────────────────
# Circular Dependency Detection
# ─────────────────────────────────────────────────────────────────────────────

#[[
legends_detect_cycles()

Performs a topological sort to detect circular dependencies in the DAG.
Called automatically when all targets are defined.

Fails with FATAL_ERROR if a cycle is detected.
]]
function(legends_detect_cycles)
    # Get list of all internal modules
    set(MODULES "legends_core" "legends_pal" "aibox_core")

    # Build adjacency list from manifest
    foreach(MODULE ${MODULES})
        set(GRAPH_${MODULE} ${LEGENDS_DAG_${MODULE}})
    endforeach()

    # Kahn's algorithm for topological sort
    set(IN_DEGREE_legends_core 0)
    set(IN_DEGREE_legends_pal 0)
    set(IN_DEGREE_aibox_core 0)

    # Calculate in-degrees
    foreach(MODULE ${MODULES})
        foreach(DEP ${GRAPH_${MODULE}})
            if(DEFINED IN_DEGREE_${DEP})
                math(EXPR IN_DEGREE_${DEP} "${IN_DEGREE_${DEP}} + 1")
            endif()
        endforeach()
    endforeach()

    # Find nodes with in-degree 0
    set(QUEUE "")
    foreach(MODULE ${MODULES})
        if(IN_DEGREE_${MODULE} EQUAL 0)
            list(APPEND QUEUE ${MODULE})
        endif()
    endforeach()

    set(SORTED_COUNT 0)

    while(QUEUE)
        list(POP_FRONT QUEUE CURRENT)
        math(EXPR SORTED_COUNT "${SORTED_COUNT} + 1")

        foreach(NEIGHBOR ${GRAPH_${CURRENT}})
            if(DEFINED IN_DEGREE_${NEIGHBOR})
                math(EXPR IN_DEGREE_${NEIGHBOR} "${IN_DEGREE_${NEIGHBOR}} - 1")
                if(IN_DEGREE_${NEIGHBOR} EQUAL 0)
                    list(APPEND QUEUE ${NEIGHBOR})
                endif()
            endif()
        endforeach()
    endwhile()

    list(LENGTH MODULES MODULE_COUNT)
    if(NOT SORTED_COUNT EQUAL MODULE_COUNT)
        message(FATAL_ERROR
            "Circular dependency detected in module DAG!\n"
            "  Processed ${SORTED_COUNT} of ${MODULE_COUNT} modules.\n"
            "  Check cmake/ModuleManifest.cmake for cycles."
        )
    endif()

    message(STATUS "DAG: No circular dependencies detected (OK)")
endfunction()

# ─────────────────────────────────────────────────────────────────────────────
# Verify All Function
# ─────────────────────────────────────────────────────────────────────────────

#[[
legends_verify_all_dags()

Convenience function to verify all module targets and check for cycles.
Call this after all targets are defined.
]]
function(legends_verify_all_dags)
    message(STATUS "")
    message(STATUS "===== DAG Verification =====")

    # Verify individual targets (only if they exist)
    if(TARGET legends_core)
        legends_verify_dag(legends_core)
    endif()

    if(TARGET legends_pal)
        legends_verify_dag(legends_pal)
    endif()

    if(TARGET aibox_core)
        legends_verify_dag(aibox_core)
    endif()

    # Check for circular dependencies
    legends_detect_cycles()

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
