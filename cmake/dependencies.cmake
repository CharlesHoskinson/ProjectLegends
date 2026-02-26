# SPDX-License-Identifier: GPL-2.0-or-later
# Copyright (C) 2024-2025 Charles Hoskinson and Contributors
#
# Centralized Dependency Management
#
# All external dependency version pins live here for reproducible builds.
# See DEPENDENCIES.md for the human-readable manifest.
#
# REQ-OPS-001: Version-pinned dependencies
# REQ-OPS-003: Hermetic build support
# REQ-SEC-027: Known-good dependency versions

include(FetchContent)

# ─────────────────────────────────────────────────────────────────────────────
# Version Pins
# ─────────────────────────────────────────────────────────────────────────────

set(LEGENDS_DEP_GSL_LITE_TAG    "v1.0.0"   CACHE STRING "gsl-lite version tag")
set(LEGENDS_DEP_SDL3_TAG        "release-3.2.8" CACHE STRING "SDL3 version tag")
set(LEGENDS_DEP_GOOGLETEST_TAG  "v1.14.0"  CACHE STRING "GoogleTest version tag")
set(LEGENDS_DEP_BENCHMARK_TAG   "v1.8.3"   CACHE STRING "Google Benchmark version tag")

# ─────────────────────────────────────────────────────────────────────────────
# gsl-lite (Contracts Library)
# ─────────────────────────────────────────────────────────────────────────────
#
# gsl-lite v1 uses namespace `gsl_lite` and header `<gsl-lite/gsl-lite.hpp>`
# We create a bridge header (include/legends/gsl.hpp) with a scoped alias.
# Do NOT expose gsl-lite types in public headers (legends_embed.h) - it affects ABI.

find_package(gsl-lite 1.0 QUIET)

if(NOT gsl-lite_FOUND)
    message(STATUS "gsl-lite not found, fetching ${LEGENDS_DEP_GSL_LITE_TAG} from GitHub...")
    FetchContent_Declare(
        gsl-lite
        GIT_REPOSITORY https://github.com/gsl-lite/gsl-lite.git
        GIT_TAG        ${LEGENDS_DEP_GSL_LITE_TAG}
    )
    FetchContent_MakeAvailable(gsl-lite)
endif()

# ─────────────────────────────────────────────────────────────────────────────
# SDL3 (Platform Backend)
# ─────────────────────────────────────────────────────────────────────────────
#
# Try find_package first (system/user-provided), then fall back to FetchContent
# for hermetic builds (REQ-OPS-002).

if(PAL_BACKEND_SDL3)
    # Include SDL3's CPU detection before find_package
    if(EXISTS "${SDL3_DIR}/sdlcpu.cmake")
        include("${SDL3_DIR}/sdlcpu.cmake")
    endif()

    find_package(SDL3 QUIET)
    if(NOT SDL3_FOUND)
        message(STATUS "SDL3 not found, fetching ${LEGENDS_DEP_SDL3_TAG} from GitHub...")
        FetchContent_Declare(SDL3
            GIT_REPOSITORY https://github.com/libsdl-org/SDL.git
            GIT_TAG        ${LEGENDS_DEP_SDL3_TAG}
            GIT_SHALLOW    TRUE
        )
        set(SDL_SHARED ON CACHE BOOL "" FORCE)
        set(SDL_STATIC OFF CACHE BOOL "" FORCE)
        set(SDL_TEST_LIBRARY OFF CACHE BOOL "" FORCE)
        FetchContent_MakeAvailable(SDL3)
    endif()
endif()
