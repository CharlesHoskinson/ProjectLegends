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

# v1.1.0: prefer for MSVC C4875 / modern suppress form (#44). Fallback path
# still works if FetchContent fails; remove legends_gsl_msvc_options when
# confirmed clean under /WX on windows-latest.
set(LEGENDS_DEP_GSL_LITE_TAG    "v1.1.0"   CACHE STRING "gsl-lite version tag")
set(LEGENDS_DEP_SDL3_TAG        "release-3.2.8" CACHE STRING "SDL3 version tag")
set(LEGENDS_DEP_GOOGLETEST_TAG  "v1.14.0"  CACHE STRING "GoogleTest version tag")
set(LEGENDS_DEP_BENCHMARK_TAG   "v1.8.3"   CACHE STRING "Google Benchmark version tag")

# Phase 3: Enhanced Features
set(LEGENDS_DEP_FLUIDSYNTH_TAG  "v2.3.5"   CACHE STRING "FluidSynth version tag")
set(LEGENDS_DEP_MT32EMU_TAG     "v2.7.0"   CACHE STRING "MUNT/mt32emu version tag")

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

# ─────────────────────────────────────────────────────────────────────────────
# libcurl (AI Assistant HTTP client) — Phase 3, Sprint 3
# ─────────────────────────────────────────────────────────────────────────────
#
# libcurl is used for async HTTP requests to AI API endpoints.
# Optional: AI features gracefully degrade without it.

if(LEGENDS_ENABLE_AI)
    find_package(CURL QUIET)
    if(NOT CURL_FOUND)
        message(STATUS "libcurl not found — AI HTTP client will use stub implementation")
    else()
        message(STATUS "Found libcurl: ${CURL_VERSION_STRING}")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────
# FluidSynth (MIDI Synthesis) — Phase 3, Sprint 4
# ─────────────────────────────────────────────────────────────────────────────
#
# FluidSynth provides SoundFont-based MIDI synthesis.
# Optional: gated by LEGENDS_ENABLE_FLUIDSYNTH

if(LEGENDS_ENABLE_FLUIDSYNTH)
    find_package(FluidSynth QUIET)
    if(NOT FluidSynth_FOUND)
        message(STATUS "FluidSynth not found — FluidSynth MIDI device unavailable")
    else()
        message(STATUS "Found FluidSynth: ${FluidSynth_VERSION}")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────
# MUNT/mt32emu (MT-32 Emulation) — Phase 3, Sprint 4
# ─────────────────────────────────────────────────────────────────────────────
#
# MUNT provides Roland MT-32 hardware emulation for authentic MIDI playback.
# Optional: gated by LEGENDS_ENABLE_MT32

if(LEGENDS_ENABLE_MT32)
    find_package(mt32emu QUIET)
    if(NOT mt32emu_FOUND)
        message(STATUS "mt32emu not found — attempting FetchContent...")
        FetchContent_Declare(mt32emu
            GIT_REPOSITORY https://github.com/munt/munt.git
            GIT_TAG        ${LEGENDS_DEP_MT32EMU_TAG}
            GIT_SHALLOW    TRUE
            SOURCE_SUBDIR  mt32emu
        )
        FetchContent_MakeAvailable(mt32emu)
    else()
        message(STATUS "Found mt32emu: ${mt32emu_VERSION}")
    endif()
endif()
