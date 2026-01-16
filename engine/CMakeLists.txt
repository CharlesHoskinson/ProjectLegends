# ─────────────────────────────────────────────────────────────────────────────
# AIBox - LLM-Optimized DOSBox-X Fork
# CMake Build Configuration
# ─────────────────────────────────────────────────────────────────────────────

cmake_minimum_required(VERSION 3.16)

project(AIBox
    VERSION 0.1.0
    DESCRIPTION "LLM-Optimized DOSBox-X Fork"
    LANGUAGES CXX C
)

# ─────────────────────────────────────────────────────────────────────────────
# Build Options
# ─────────────────────────────────────────────────────────────────────────────

option(AIBOX_BUILD_TESTS "Build unit and integration tests" ON)
option(AIBOX_TEST_COVERAGE "Enable code coverage (GCC/Clang)" OFF)
option(AIBOX_LIBRARY_MODE "Build as embeddable library" ON)
option(AIBOX_SANITIZERS "Enable AddressSanitizer and UBSan (combined)" OFF)
option(AIBOX_ENABLE_ASAN "Enable AddressSanitizer only" OFF)
option(AIBOX_ENABLE_UBSAN "Enable UndefinedBehaviorSanitizer only" OFF)
option(AIBOX_ENABLE_TSAN "Enable ThreadSanitizer" OFF)
option(AIBOX_ALWAYS_BOUNDS_CHECK "Enable bounds checking in release builds" OFF)
option(AIBOX_HEADLESS "Build in headless mode (no SDL dependencies)" ON)
option(AIBOX_BUILD_SHARED "Build shared library instead of static" OFF)

# ─────────────────────────────────────────────────────────────────────────────
# C++ Standard and Compiler Settings
# ─────────────────────────────────────────────────────────────────────────────

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Export compile commands for IDE support
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# ─────────────────────────────────────────────────────────────────────────────
# Compiler Version Checks (C++23 requires modern compilers)
# ─────────────────────────────────────────────────────────────────────────────

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU")
    if(CMAKE_CXX_COMPILER_VERSION VERSION_LESS "13.0")
        message(FATAL_ERROR
            "GCC 13+ required for C++23 support. Found: ${CMAKE_CXX_COMPILER_VERSION}")
    endif()
    message(STATUS "Compiler: GCC ${CMAKE_CXX_COMPILER_VERSION}")
elseif(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    if(CMAKE_CXX_COMPILER_VERSION VERSION_LESS "16.0")
        message(FATAL_ERROR
            "Clang 16+ required for C++23 support. Found: ${CMAKE_CXX_COMPILER_VERSION}")
    endif()
    message(STATUS "Compiler: Clang ${CMAKE_CXX_COMPILER_VERSION}")
elseif(MSVC)
    if(MSVC_VERSION LESS 1934)
        message(FATAL_ERROR
            "MSVC 19.34+ (VS 2022 17.4+) required for C++23. Found: ${MSVC_VERSION}")
    endif()
    message(STATUS "Compiler: MSVC ${MSVC_VERSION}")
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Compiler Flags
# ─────────────────────────────────────────────────────────────────────────────

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    add_compile_options(
        -Wall
        -Wextra
        -Wpedantic
        -Wno-unused-parameter
    )

    # Combined sanitizer option (legacy)
    if(AIBOX_SANITIZERS)
        add_compile_options(-fsanitize=address,undefined -fno-omit-frame-pointer)
        add_link_options(-fsanitize=address,undefined)
        message(STATUS "AddressSanitizer + UBSan enabled")
    endif()

    # Individual sanitizer options (Phase 2)
    if(AIBOX_ENABLE_ASAN)
        add_compile_options(-fsanitize=address -fno-omit-frame-pointer)
        add_link_options(-fsanitize=address)
        message(STATUS "AddressSanitizer enabled")
    endif()

    if(AIBOX_ENABLE_UBSAN)
        add_compile_options(
            -fsanitize=undefined
            -fsanitize=integer
            -fno-sanitize-recover=all
        )
        add_link_options(-fsanitize=undefined)
        message(STATUS "UndefinedBehaviorSanitizer enabled")
    endif()

    if(AIBOX_ENABLE_TSAN)
        add_compile_options(-fsanitize=thread)
        add_link_options(-fsanitize=thread)
        message(STATUS "ThreadSanitizer enabled")
    endif()

    if(AIBOX_TEST_COVERAGE)
        add_compile_options(--coverage -fprofile-arcs -ftest-coverage)
        add_link_options(--coverage)
    endif()
elseif(MSVC)
    add_compile_options(
        /W4
        /wd4100  # unreferenced formal parameter
        /wd4244  # conversion warnings
    )
    add_compile_definitions(_CRT_SECURE_NO_WARNINGS)
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Library Mode Configuration
# ─────────────────────────────────────────────────────────────────────────────

if(AIBOX_LIBRARY_MODE)
    add_compile_definitions(AIBOX_LIBRARY_MODE=1)
    message(STATUS "Building in LIBRARY MODE (exceptions instead of abort)")
endif()

# ─────────────────────────────────────────────────────────────────────────────
# SDL Compile Firewall (PR #21)
# ─────────────────────────────────────────────────────────────────────────────

include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/CompileFirewall.cmake)

if(AIBOX_ALWAYS_BOUNDS_CHECK)
    add_compile_definitions(AIBOX_ALWAYS_BOUNDS_CHECK=1)
    message(STATUS "Always performing bounds checks (even in release builds)")
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Include Directories
# ─────────────────────────────────────────────────────────────────────────────

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

# ─────────────────────────────────────────────────────────────────────────────
# AIBox Core Library
# ─────────────────────────────────────────────────────────────────────────────

# Core source files
set(AIBOX_CORE_SOURCES
    # DOSBox-X Library Mode (PR #2-4: Error Model, Logging, Safe Call)
    src/misc/error_model.cpp
    src/misc/logging.cpp
    src/misc/safe_call.cpp
    # PR #7: State Hash API
    src/misc/state_hash.cpp
    # PR #8: Misuse-Resilient Handle System
    src/misc/instance_handle.cpp
    # PR #9: DOSBoxContext Structure
    src/misc/dosbox_context.cpp
    # PR #22: DOSBox-X Embeddable Library API
    src/misc/dosbox_library.cpp
    # PR #16: Headless Platform Backend
    src/platform/headless/headless_display.cpp
    src/platform/headless/buffer_audio.cpp
    src/platform/headless/thread_safe_input.cpp
    src/aibox/machine_context.cpp
    src/aibox/llm_serializer.cpp
    src/aibox/llm_frame.cpp
    src/aibox/llm_actions.cpp
    src/aibox/llm_diff.cpp
    src/aibox/vision_framebuffer.cpp
    src/aibox/vision_capture.cpp
    src/aibox/vision_overlay.cpp
    src/aibox/vision_annotations.cpp
    # Sprint 2 Phase 3: DMA Compatibility Shim
    src/hardware/dma_compat.cpp
)

# Add headless stub when building without SDL
if(AIBOX_HEADLESS)
    list(APPEND AIBOX_CORE_SOURCES src/aibox/headless_stub.cpp)
    message(STATUS "Headless mode: SDL stubs enabled")
endif()

# Build as shared or static library
if(AIBOX_BUILD_SHARED)
    add_library(aibox_core SHARED ${AIBOX_CORE_SOURCES})
    set_target_properties(aibox_core PROPERTIES
        POSITION_INDEPENDENT_CODE ON
        WINDOWS_EXPORT_ALL_SYMBOLS ON
    )
    target_compile_definitions(aibox_core PRIVATE AIBOX_BUILD_DLL)
    message(STATUS "Building SHARED library")
else()
    add_library(aibox_core STATIC ${AIBOX_CORE_SOURCES})
    message(STATUS "Building STATIC library")
endif()

target_include_directories(aibox_core PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/include
)

# Compile definitions for aibox_core
target_compile_definitions(aibox_core PUBLIC
    $<$<BOOL:${AIBOX_LIBRARY_MODE}>:AIBOX_LIBRARY_MODE=1>
    $<$<BOOL:${AIBOX_LIBRARY_MODE}>:DOSBOX_LIBRARY_MODE=1>
    $<$<BOOL:${AIBOX_ALWAYS_BOUNDS_CHECK}>:AIBOX_ALWAYS_BOUNDS_CHECK=1>
    $<$<BOOL:${AIBOX_HEADLESS}>:AIBOX_HEADLESS=1>
)

# Verify no SDL symbols leak into aibox_core (PR #21)
if(AIBOX_HEADLESS)
    aibox_verify_no_sdl_in_core(aibox_core)
endif()

# ─────────────────────────────────────────────────────────────────────────────
# gsl-lite (Contracts and Safety)
# ─────────────────────────────────────────────────────────────────────────────

include(FetchContent)

FetchContent_Declare(
    gsl-lite
    GIT_REPOSITORY https://github.com/gsl-lite/gsl-lite.git
    GIT_TAG v0.41.0
)

# Configure contract violations to terminate (fail-fast for debugging)
set(GSL_LITE_OPT_CONTRACT_VIOLATION_TERMINATES ON CACHE BOOL "" FORCE)

FetchContent_MakeAvailable(gsl-lite)

# Link gsl-lite to aibox_core
target_link_libraries(aibox_core PUBLIC gsl::gsl-lite-v1)

message(STATUS "gsl-lite: Contract checking enabled")

# ─────────────────────────────────────────────────────────────────────────────
# C++23 Feature Validation
# ─────────────────────────────────────────────────────────────────────────────

# Validate that the compiler's standard library supports C++23 features
try_compile(HAS_CXX23_FEATURES
    ${CMAKE_BINARY_DIR}/cxx23_check
    SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/cmake/test_cxx23.cpp
    CXX_STANDARD 23
    CXX_STANDARD_REQUIRED ON
)

if(NOT HAS_CXX23_FEATURES)
    message(FATAL_ERROR
        "Compiler claims C++23 support but standard library is missing required features.\n"
        "Required: <expected>, <format>, <span>, <ranges>\n"
        "Ensure your standard library (libstdc++/libc++) is up to date.")
endif()

message(STATUS "C++23 feature validation: PASSED")

# ─────────────────────────────────────────────────────────────────────────────
# Testing Infrastructure (Phase 1)
# ─────────────────────────────────────────────────────────────────────────────

if(AIBOX_BUILD_TESTS)
    message(STATUS "Building with test support")

    # Fetch Google Test (FetchContent already included above)
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG v1.14.0
    )

    # Prevent Google Test from overriding compiler/linker settings on Windows
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)

    # Don't install GTest when installing this project
    set(INSTALL_GTEST OFF CACHE BOOL "" FORCE)

    FetchContent_MakeAvailable(googletest)

    # Enable CTest
    enable_testing()
    include(GoogleTest)

    # Add test subdirectory
    add_subdirectory(tests)
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Installation
# ─────────────────────────────────────────────────────────────────────────────

# Install AIBox headers
install(DIRECTORY include/aibox
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)

# ─────────────────────────────────────────────────────────────────────────────
# Summary
# ─────────────────────────────────────────────────────────────────────────────

message(STATUS "")
message(STATUS "AIBox Configuration Summary:")
message(STATUS "  Version:       ${PROJECT_VERSION}")
message(STATUS "  C++ Standard:  ${CMAKE_CXX_STANDARD}")
message(STATUS "  Build Tests:   ${AIBOX_BUILD_TESTS}")
message(STATUS "  Coverage:      ${AIBOX_TEST_COVERAGE}")
message(STATUS "  Library Mode:  ${AIBOX_LIBRARY_MODE}")
message(STATUS "  Headless:      ${AIBOX_HEADLESS}")
message(STATUS "  Shared Lib:    ${AIBOX_BUILD_SHARED}")
message(STATUS "  Sanitizers:    ${AIBOX_SANITIZERS}")
message(STATUS "")
