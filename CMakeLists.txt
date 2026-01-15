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
# C++ Standard
# ─────────────────────────────────────────────────────────────────────────────

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# ─────────────────────────────────────────────────────────────────────────────
# Compiler Flags
# ─────────────────────────────────────────────────────────────────────────────

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
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

# ─────────────────────────────────────────────────────────────────────────────
# Dependencies
# ─────────────────────────────────────────────────────────────────────────────

# gsl-lite for contracts
include(FetchContent)
FetchContent_Declare(
    gsl-lite
    GIT_REPOSITORY https://github.com/gsl-lite/gsl-lite.git
    GIT_TAG v0.41.0
)
FetchContent_MakeAvailable(gsl-lite)

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

target_include_directories(legends_core
    PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/include
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

target_link_libraries(legends_core
    PUBLIC
        gsl::gsl-lite
)

target_compile_definitions(legends_core
    PRIVATE
        $<$<BOOL:${LEGENDS_HEADLESS}>:LEGENDS_HEADLESS=1>
        $<$<BOOL:${LEGENDS_LIBRARY_MODE}>:LEGENDS_LIBRARY_MODE=1>
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
    )

    target_link_libraries(legends_unit_tests PRIVATE
        legends_core
        legends_pal
        GTest::gtest_main
        GTest::gmock
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

    add_custom_target(test-all
        COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
        DEPENDS legends_unit_tests legends_abi_test
        COMMENT "Running all tests"
    )

    add_custom_target(test-abi
        COMMAND ${CMAKE_CTEST_COMMAND} -L abi --output-on-failure
        DEPENDS legends_abi_test
        COMMENT "Running ABI verification tests"
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
