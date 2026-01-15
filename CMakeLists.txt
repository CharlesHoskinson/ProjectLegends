# ═══════════════════════════════════════════════════════════════════════════════
# Project Legends - Embeddable x86 Emulation Framework
# ═══════════════════════════════════════════════════════════════════════════════
#
# Copyright (c) 2024-2025 Charles Hoskinson and Contributors
# Based on DOSBox-X by the DOSBox-X Team
# Licensed under GNU General Public License v2.0
#
# ═══════════════════════════════════════════════════════════════════════════════

cmake_minimum_required(VERSION 3.20)

project(ProjectLegends
    VERSION 1.0.0
    DESCRIPTION "Embeddable x86 Emulation Framework for AI-Driven Computing"
    HOMEPAGE_URL "https://github.com/user/ProjectLegends"
    LANGUAGES CXX C
)

# ─────────────────────────────────────────────────────────────────────────────
# Build Options
# ─────────────────────────────────────────────────────────────────────────────

option(LEGENDS_BUILD_TESTS "Build unit tests" OFF)
option(LEGENDS_HEADLESS "Build in headless mode (no GUI)" OFF)
option(LEGENDS_LIBRARY_MODE "Build as static library" OFF)

# PAL Backend Options
option(PAL_BACKEND_HEADLESS "Build headless PAL backend" ON)
option(PAL_BACKEND_SDL2 "Build SDL2 PAL backend" OFF)
option(PAL_BACKEND_SDL3 "Build SDL3 PAL backend" OFF)
set(PAL_DEFAULT_BACKEND "Headless" CACHE STRING "Default PAL backend (SDL2, SDL3, Headless)")

# ─────────────────────────────────────────────────────────────────────────────
# C++ Standard (per-target, not global - see target_compile_features below)
# ─────────────────────────────────────────────────────────────────────────────

# We set C++23 per-target below, not globally. This ensures:
# 1. Each target explicitly declares its standard requirement
# 2. No accidental standard leakage to consumers
# 3. CI can verify each target compiles as C++23

# ─────────────────────────────────────────────────────────────────────────────
# Compiler Flags (Two-Tier Strategy)
# ─────────────────────────────────────────────────────────────────────────────

# Tier A (new/refactored code): strict warnings, -Werror enabled via target property
# Tier B (legacy migration): warnings on, NOT errors (set per legacy target)

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    # Base warnings for all targets
    add_compile_options(-Wall -Wextra -Wpedantic)
    if(CMAKE_BUILD_TYPE STREQUAL "Debug")
        add_compile_options(-g -O0)
    else()
        add_compile_options(-O2)
    endif()
elseif(MSVC)
    add_compile_options(/W4 /permissive-)
    add_compile_definitions(_CRT_SECURE_NO_WARNINGS)
endif()

# Helper function to apply C++23 and strict warnings to a target (Tier A)
function(legends_set_strict_cxx_standard target_name)
    set_target_properties(${target_name} PROPERTIES
        CXX_STANDARD 23
        CXX_STANDARD_REQUIRED ON
        CXX_EXTENSIONS OFF
    )
    # MSVC: explicitly set /std:c++23preview for reliable C++23 support
    # CMake's CXX_STANDARD 23 may map to /std:c++latest which can drift
    if(MSVC)
        target_compile_options(${target_name} PRIVATE /std:c++23preview /WX)
    elseif(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
        # Tier A: warnings are errors for new/refactored code
        target_compile_options(${target_name} PRIVATE -Werror)
    endif()
endfunction()

# Helper function for legacy code under migration (Tier B)
function(legends_set_legacy_cxx_standard target_name)
    set_target_properties(${target_name} PROPERTIES
        CXX_STANDARD 23
        CXX_STANDARD_REQUIRED ON
        CXX_EXTENSIONS OFF
    )
    # MSVC: explicitly set /std:c++23preview
    if(MSVC)
        target_compile_options(${target_name} PRIVATE /std:c++23preview)
    endif()
    # Tier B: warnings NOT errors (migration in progress)
endfunction()

# ─────────────────────────────────────────────────────────────────────────────
# Dependencies
# ─────────────────────────────────────────────────────────────────────────────

# gsl-lite for contracts (v1.0.0 - stable v1 series)
# See: https://github.com/gsl-lite/gsl-lite
#
# IMPORTANT: gsl-lite v1 uses namespace `gsl_lite` and header `<gsl-lite/gsl-lite.hpp>`
# We create a bridge header (include/legends/gsl.hpp) with a scoped alias.
# Do NOT expose gsl-lite types in public headers (legends_embed.h) - it affects ABI.
#
# FORBIDDEN PATTERNS (CI gate enforced):
#   - <gsl/gsl-lite.hpp> (legacy header, conflicts with Microsoft GSL)
#   - gsl_FEATURE_GSL_COMPATIBILITY_MODE (affects API/ABI, consumer's choice)
#   - Exporting gsl-lite config macros as PUBLIC compile definitions

# Try system-installed gsl-lite first (preferred for reproducible builds)
find_package(gsl-lite 1.0 QUIET)

if(NOT gsl-lite_FOUND)
    message(STATUS "gsl-lite not found, fetching from GitHub...")
    include(FetchContent)
    FetchContent_Declare(
        gsl-lite
        GIT_REPOSITORY https://github.com/gsl-lite/gsl-lite.git
        GIT_TAG v1.0.0
    )
    FetchContent_MakeAvailable(gsl-lite)
endif()

# Note: For v1, link to gsl::gsl-lite-v1 for v1 defaults.
# We keep it PRIVATE to avoid leaking to consumers.

# ─────────────────────────────────────────────────────────────────────────────
# DOSBox-X Engine (AIBox Library)
# ─────────────────────────────────────────────────────────────────────────────
#
# The engine/ directory contains the refactored DOSBox-X library providing:
# - Platform abstraction (headless timing, display, input, audio)
# - Embeddable library API (dosbox_library.h)
# - State hash API for determinism verification
# - Error model (FAIL/PANIC/TRAP taxonomy)
#
# See engine/LIBRARY_CONTRACT.md for API documentation.
#

# Configure engine options before adding subdirectory
set(AIBOX_BUILD_TESTS OFF CACHE BOOL "Disable engine tests (use legends tests)" FORCE)
set(AIBOX_HEADLESS ON CACHE BOOL "Build engine in headless mode" FORCE)
set(AIBOX_LIBRARY_MODE ON CACHE BOOL "Build engine as library" FORCE)

add_subdirectory(engine)

# ─────────────────────────────────────────────────────────────────────────────
# Legends Core Library
# ─────────────────────────────────────────────────────────────────────────────

set(LEGENDS_SOURCES
    src/legends/legends_embed_api.cpp
    src/legends/machine_context.cpp
    src/legends/llm_frame.cpp
    src/legends/llm_actions.cpp
    src/legends/llm_diff.cpp
    src/legends/llm_serializer.cpp
    src/legends/vision_framebuffer.cpp
    src/legends/vision_capture.cpp
    src/legends/vision_overlay.cpp
    src/legends/vision_annotations.cpp
)

if(LEGENDS_HEADLESS)
    list(APPEND LEGENDS_SOURCES src/legends/headless_stub.cpp)
endif()

add_library(legends_core STATIC ${LEGENDS_SOURCES})

# Apply C++23 standard (Tier A - new code, strict warnings)
legends_set_strict_cxx_standard(legends_core)

target_include_directories(legends_core
    PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/include
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
        ${CMAKE_CURRENT_SOURCE_DIR}/engine/include  # DOSBox-X headers
)

# IMPORTANT: gsl-lite is PRIVATE - do NOT expose to consumers
# Consumers include legends_embed.h (pure C ABI), not gsl-lite types
target_link_libraries(legends_core
    PRIVATE
        gsl::gsl-lite-v1
        aibox_core  # DOSBox-X engine library
)

target_compile_definitions(legends_core
    PRIVATE
        $<$<BOOL:${LEGENDS_HEADLESS}>:LEGENDS_HEADLESS=1>
        $<$<BOOL:${LEGENDS_LIBRARY_MODE}>:LEGENDS_LIBRARY_MODE=1>
        # gsl-lite contract violation behavior:
        # Library mode: throw (caught at FFI boundary)
        # Standalone mode: terminate (fail-fast)
        $<$<BOOL:${LEGENDS_LIBRARY_MODE}>:gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1>
        $<$<NOT:$<BOOL:${LEGENDS_LIBRARY_MODE}>>:gsl_CONFIG_CONTRACT_VIOLATION_TERMINATES=1>
)

# ─────────────────────────────────────────────────────────────────────────────
# Platform Abstraction Layer (PAL)
# ─────────────────────────────────────────────────────────────────────────────

set(PAL_HEADERS
    include/pal/types.h
    include/pal/window.h
    include/pal/context.h
    include/pal/audio_sink.h
    include/pal/host_clock.h
    include/pal/input_source.h
    include/pal/platform.h
)

set(PAL_SOURCES "")

# Headless backend (always available)
if(PAL_BACKEND_HEADLESS)
    list(APPEND PAL_SOURCES
        src/pal/headless/window_headless.cpp
        src/pal/headless/context_headless.cpp
        src/pal/headless/audio_sink_headless.cpp
        src/pal/headless/host_clock_headless.cpp
        src/pal/headless/input_source_headless.cpp
        src/pal/headless/platform_headless.cpp
    )
endif()

# SDL2 backend
if(PAL_BACKEND_SDL2)
    find_package(SDL2 REQUIRED)
    list(APPEND PAL_SOURCES
        src/pal/sdl2/window_sdl2.cpp
        src/pal/sdl2/context_sdl2.cpp
        src/pal/sdl2/audio_sink_sdl2.cpp
        src/pal/sdl2/host_clock_sdl2.cpp
        src/pal/sdl2/input_source_sdl2.cpp
        src/pal/sdl2/platform_sdl2.cpp
    )
endif()

# SDL3 backend
if(PAL_BACKEND_SDL3)
    # Include SDL3's CPU detection before find_package
    if(EXISTS "${SDL3_DIR}/sdlcpu.cmake")
        include("${SDL3_DIR}/sdlcpu.cmake")
    endif()
    find_package(SDL3 REQUIRED)
    list(APPEND PAL_SOURCES
        src/pal/sdl3/window_sdl3.cpp
        src/pal/sdl3/context_sdl3.cpp
        src/pal/sdl3/audio_sink_sdl3.cpp
        src/pal/sdl3/host_clock_sdl3.cpp
        src/pal/sdl3/input_source_sdl3.cpp
        src/pal/sdl3/platform_sdl3.cpp
    )
endif()

add_library(legends_pal STATIC ${PAL_SOURCES})

# Apply C++23 standard (Tier A - new code, strict warnings)
legends_set_strict_cxx_standard(legends_pal)

target_include_directories(legends_pal
    PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_compile_definitions(legends_pal
    PUBLIC
        $<$<BOOL:${PAL_BACKEND_HEADLESS}>:PAL_HAS_HEADLESS=1>
        $<$<BOOL:${PAL_BACKEND_SDL2}>:PAL_HAS_SDL2=1>
        $<$<BOOL:${PAL_BACKEND_SDL3}>:PAL_HAS_SDL3=1>
        PAL_DEFAULT_BACKEND="${PAL_DEFAULT_BACKEND}"
)

if(PAL_BACKEND_SDL2)
    target_link_libraries(legends_pal PRIVATE SDL2::SDL2)
    target_include_directories(legends_pal PRIVATE ${SDL2_INCLUDE_DIRS})
endif()

if(PAL_BACKEND_SDL3)
    target_link_libraries(legends_pal PRIVATE SDL3::SDL3-shared)
    target_include_directories(legends_pal PRIVATE ${SDL3_INCLUDE_DIRS})
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Tests
# ─────────────────────────────────────────────────────────────────────────────

if(LEGENDS_BUILD_TESTS)
    enable_testing()

    # GoogleTest
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG v1.14.0
    )
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(googletest)

    include(GoogleTest)

    # ─────────────────────────────────────────────────────────────────────────
    # Unit Tests (C++)
    # ─────────────────────────────────────────────────────────────────────────

    add_executable(legends_unit_tests
        tests/unit/test_error.cpp
        tests/unit/test_result.cpp
        tests/unit/test_exceptions.cpp
        tests/unit/test_ffi.cpp
        tests/unit/test_span.cpp
        tests/unit/test_memory.cpp
        tests/unit/test_io_port.cpp
        tests/unit/test_dma.cpp
        tests/unit/test_cpu_context.cpp
        tests/unit/test_machine_context.cpp
        tests/unit/test_compat_shim.cpp
        tests/unit/test_function_ref.cpp
        tests/unit/test_callback_registry.cpp
        tests/unit/test_enums.cpp
        tests/unit/test_builder.cpp
        tests/unit/test_optional_utils.cpp
        tests/unit/test_events.cpp
        tests/unit/test_handle_registry.cpp
        tests/unit/test_event_bus.cpp
        tests/unit/test_llm_frame.cpp
        tests/unit/test_llm_actions.cpp
        tests/unit/test_llm_serializer.cpp
        tests/unit/test_llm_diff.cpp
        tests/unit/test_vision_framebuffer.cpp
        tests/unit/test_vision_capture.cpp
        tests/unit/test_vision_overlay.cpp
        tests/unit/test_vision_annotations.cpp
        tests/unit/test_legends_embed.cpp
        # PAL Tests
        tests/unit/test_pal_types.cpp
        tests/unit/test_pal_window.cpp
        tests/unit/test_pal_context.cpp
        tests/unit/test_pal_audio_sink.cpp
        tests/unit/test_pal_host_clock.cpp
        tests/unit/test_pal_input_source.cpp
        tests/unit/test_pal_platform.cpp
        tests/unit/test_pal_sdl2_backend.cpp
        tests/unit/test_pal_sdl3_backend.cpp
        # Contract Gates
        tests/unit/test_contract_gates.cpp
        # Extended Test Coverage (Phase 2)
        tests/unit/test_thread_safety.cpp
        tests/unit/test_error_codes.cpp
        tests/unit/test_edge_cases.cpp
        tests/unit/test_stress.cpp
        tests/unit/test_negative.cpp
    )

    # Apply C++23 standard (Tier A - tests should be strict too)
    legends_set_strict_cxx_standard(legends_unit_tests)

    target_link_libraries(legends_unit_tests PRIVATE
        legends_core
        legends_pal
        GTest::gtest_main
        GTest::gmock
        gsl::gsl-lite-v1  # Tests may use gsl-lite directly for testing
    )

    target_compile_definitions(legends_unit_tests PRIVATE
        LEGENDS_LIBRARY_MODE=1
    )

    gtest_discover_tests(legends_unit_tests
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        PROPERTIES LABELS "unit"
    )

    # ─────────────────────────────────────────────────────────────────────────
    # ABI Test (Pure C)
    # ─────────────────────────────────────────────────────────────────────────

    add_executable(legends_abi_test
        tests/unit/test_legends_abi.c
    )

    set_target_properties(legends_abi_test PROPERTIES
        C_STANDARD 11
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
    )

    target_link_libraries(legends_abi_test PRIVATE
        legends_core
    )

    target_include_directories(legends_abi_test PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
    )

    add_test(NAME legends_abi_test
        COMMAND legends_abi_test
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )

    set_tests_properties(legends_abi_test PROPERTIES
        LABELS "abi;unit"
    )

    # ─────────────────────────────────────────────────────────────────────────
    # Custom Test Targets
    # ─────────────────────────────────────────────────────────────────────────

    add_custom_target(test-unit
        COMMAND ${CMAKE_CTEST_COMMAND} -L unit --output-on-failure
        DEPENDS legends_unit_tests
        COMMENT "Running unit tests"
    )

    # Note: test-all target will be updated below after integration tests are defined

    add_custom_target(test-abi
        COMMAND ${CMAKE_CTEST_COMMAND} -L abi --output-on-failure
        DEPENDS legends_abi_test
        COMMENT "Running ABI verification tests"
    )

    # ─────────────────────────────────────────────────────────────────────────
    # Toolchain Verification Tests
    # ─────────────────────────────────────────────────────────────────────────

    add_executable(legends_toolchain_tests
        tests/toolchain/test_cpp_standard.cpp
    )

    # Apply C++23 standard (this IS the gate test - must be strict)
    legends_set_strict_cxx_standard(legends_toolchain_tests)

    target_link_libraries(legends_toolchain_tests PRIVATE
        GTest::gtest_main
    )

    target_compile_definitions(legends_toolchain_tests PRIVATE
        LEGENDS_LIBRARY_MODE=1
    )

    gtest_discover_tests(legends_toolchain_tests
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        PROPERTIES LABELS "toolchain"
    )

    add_custom_target(test-toolchain
        COMMAND ${CMAKE_CTEST_COMMAND} -L toolchain --output-on-failure
        DEPENDS legends_toolchain_tests
        COMMENT "Running toolchain verification tests"
    )

    # ─────────────────────────────────────────────────────────────────────────
    # Integration Tests
    # ─────────────────────────────────────────────────────────────────────────

    add_executable(legends_integration_tests
        tests/integration/test_workflow_basic.cpp
        tests/integration/test_workflow_determinism.cpp
        tests/integration/test_workflow_saveload.cpp
        tests/integration/test_workflow_input.cpp
        tests/integration/test_workflow_llm.cpp
    )

    legends_set_strict_cxx_standard(legends_integration_tests)

    target_link_libraries(legends_integration_tests PRIVATE
        legends_core
        legends_pal
        GTest::gtest_main
        GTest::gmock
    )

    target_compile_definitions(legends_integration_tests PRIVATE
        LEGENDS_LIBRARY_MODE=1
    )

    gtest_discover_tests(legends_integration_tests
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        PROPERTIES
            LABELS "integration"
            TIMEOUT 60
    )

    add_custom_target(test-integration
        COMMAND ${CMAKE_CTEST_COMMAND} -L integration --output-on-failure
        DEPENDS legends_integration_tests
        COMMENT "Running integration tests"
    )

    # test-all includes all test types
    add_custom_target(test-all
        COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
        DEPENDS legends_unit_tests legends_abi_test legends_integration_tests
        COMMENT "Running all tests"
    )

endif()

# ─────────────────────────────────────────────────────────────────────────────
# Benchmarks
# ─────────────────────────────────────────────────────────────────────────────

option(LEGENDS_BUILD_BENCHMARKS "Build performance benchmarks" OFF)

if(LEGENDS_BUILD_BENCHMARKS)
    FetchContent_Declare(
        benchmark
        GIT_REPOSITORY https://github.com/google/benchmark.git
        GIT_TAG v1.8.3
    )
    set(BENCHMARK_ENABLE_TESTING OFF CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(benchmark)

    add_executable(pal_benchmarks
        benchmarks/bench_pal.cpp
    )

    # Apply C++23 standard (Tier A - benchmarks should be strict)
    legends_set_strict_cxx_standard(pal_benchmarks)

    target_link_libraries(pal_benchmarks PRIVATE
        legends_pal
        benchmark::benchmark
    )

    target_compile_definitions(pal_benchmarks PRIVATE
        LEGENDS_LIBRARY_MODE=1
    )
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Installation
# ─────────────────────────────────────────────────────────────────────────────

include(GNUInstallDirs)

install(TARGETS legends_core legends_pal
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

install(DIRECTORY include/legends include/pal
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)

# ─────────────────────────────────────────────────────────────────────────────
# Package Configuration
# ─────────────────────────────────────────────────────────────────────────────

include(CMakePackageConfigHelpers)

write_basic_package_version_file(
    "${CMAKE_CURRENT_BINARY_DIR}/LegendsConfigVersion.cmake"
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY SameMajorVersion
)

configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/LegendsConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/LegendsConfig.cmake"
    @ONLY
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/LegendsConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/LegendsConfigVersion.cmake"
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Legends
)
