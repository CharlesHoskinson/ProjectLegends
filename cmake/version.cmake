# SPDX-License-Identifier: GPL-2.0-or-later
# Copyright (C) 2024-2025 Charles Hoskinson and Contributors
#
# Semver from git describe
#
# REQ-OPS-020: Version string from VCS
# REQ-OPS-021: Build metadata in version string
#
# Produces:
#   LEGENDS_VERSION_MAJOR   - e.g. 1
#   LEGENDS_VERSION_MINOR   - e.g. 0
#   LEGENDS_VERSION_PATCH   - e.g. 0
#   LEGENDS_VERSION_STRING  - e.g. "1.0.0" or "1.0.0-3-gabcdef+dirty"

find_package(Git QUIET)

set(LEGENDS_VERSION_MAJOR ${PROJECT_VERSION_MAJOR})
set(LEGENDS_VERSION_MINOR ${PROJECT_VERSION_MINOR})
set(LEGENDS_VERSION_PATCH ${PROJECT_VERSION_PATCH})
set(LEGENDS_VERSION_STRING "${PROJECT_VERSION}")

if(GIT_FOUND)
    execute_process(
        COMMAND ${GIT_EXECUTABLE} describe --tags --always --dirty --match "v[0-9]*"
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        OUTPUT_VARIABLE GIT_DESCRIBE_OUTPUT
        ERROR_QUIET
        OUTPUT_STRIP_TRAILING_WHITESPACE
        RESULT_VARIABLE GIT_DESCRIBE_RESULT
    )

    if(GIT_DESCRIBE_RESULT EQUAL 0 AND GIT_DESCRIBE_OUTPUT)
        # Strip leading "v" if present
        string(REGEX REPLACE "^v" "" GIT_VERSION "${GIT_DESCRIBE_OUTPUT}")

        # Try to parse MAJOR.MINOR.PATCH from the tag
        if(GIT_VERSION MATCHES "^([0-9]+)\\.([0-9]+)\\.([0-9]+)(.*)")
            set(LEGENDS_VERSION_MAJOR "${CMAKE_MATCH_1}")
            set(LEGENDS_VERSION_MINOR "${CMAKE_MATCH_2}")
            set(LEGENDS_VERSION_PATCH "${CMAKE_MATCH_3}")
            set(LEGENDS_VERSION_SUFFIX "${CMAKE_MATCH_4}")
            set(LEGENDS_VERSION_STRING
                "${LEGENDS_VERSION_MAJOR}.${LEGENDS_VERSION_MINOR}.${LEGENDS_VERSION_PATCH}${LEGENDS_VERSION_SUFFIX}")
        else()
            # Fallback: commit hash only (no matching tag)
            set(LEGENDS_VERSION_STRING "${PROJECT_VERSION}+${GIT_VERSION}")
        endif()

        message(STATUS "Version from git: ${LEGENDS_VERSION_STRING}")
    else()
        message(STATUS "Version from PROJECT_VERSION: ${LEGENDS_VERSION_STRING} (not in a git repo or no tags)")
    endif()
else()
    message(STATUS "Version from PROJECT_VERSION: ${LEGENDS_VERSION_STRING} (git not found)")
endif()

# Generate the version header
configure_file(
    "${CMAKE_SOURCE_DIR}/cmake/legends_version.h.in"
    "${CMAKE_BINARY_DIR}/include/legends/legends_version.h"
    @ONLY
)
