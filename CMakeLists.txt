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
# Module Graph (Sprint 3)
# ─────────────────────────────────────────────────────────────────────────────
# Load module definitions and DAG constraints early.
# See cmake/ModuleManifest.cmake for module boundaries.
include(cmake/ModuleManifest.cmake)
include(cmake/ModuleDAG.cmake)
include(cmake/dependencies.cmake)
include(cmake/version.cmake)

# ─────────────────────────────────────────────────────────────────────────────
# Build Options
# ─────────────────────────────────────────────────────────────────────────────

option(LEGENDS_BUILD_TESTS "Build unit tests" OFF)
option(LEGENDS_HEADLESS "Build in headless mode (no GUI)" OFF)
option(LEGENDS_LIBRARY_MODE "Build as static library" OFF)
option(LEGENDS_USE_IPC "Build with GPL v2 process isolation (IPC mode). Produces legends_engine_host + legends_proxy instead of monolithic linking." OFF)
option(LEGENDS_BUILD_WASM "Build Wasm/WASI target for Wasmtime sandbox (requires wasi-sdk or equivalent toolchain)" OFF)

# Fuzzing Options (requires Clang)
option(ENABLE_FUZZING "Build fuzz targets with libFuzzer" OFF)
option(ENABLE_ASAN "Enable AddressSanitizer for fuzz targets" OFF)
option(ENABLE_UBSAN "Enable UndefinedBehaviorSanitizer for fuzz targets" OFF)
option(ENABLE_MSAN "Enable MemorySanitizer for fuzz targets" OFF)

# PAL Backend Options
option(PAL_BACKEND_HEADLESS "Build headless PAL backend" ON)
option(PAL_BACKEND_SDL2 "Build SDL2 PAL backend" OFF)
option(PAL_BACKEND_SDL3 "Build SDL3 PAL backend" OFF)
set(PAL_DEFAULT_BACKEND "Headless" CACHE STRING "Default PAL backend (SDL2, SDL3, Headless)")

# Phase 3: Enhanced Feature Flags
option(LEGENDS_ENABLE_AI "Enable AI Assistant (requires libcurl)" OFF)
option(LEGENDS_ENABLE_FLUIDSYNTH "Enable FluidSynth MIDI synthesis" OFF)
option(LEGENDS_ENABLE_MT32 "Enable MUNT MT-32 emulation" OFF)

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
#
# WARNING/HARDENING FLAGS USE AN INTERFACE LIBRARY (legends_compile_options)
# instead of global add_compile_options(). This prevents project warning and
# hardening flags from leaking into FetchContent dependencies (GoogleTest,
# SDL3, gsl-lite, etc.). Each project target links legends_compile_options
# via the legends_set_strict/legacy_cxx_standard() helpers.

add_library(legends_compile_options INTERFACE)

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    # Base warnings for project targets only
    target_compile_options(legends_compile_options INTERFACE
        -Wall -Wextra -Wpedantic
        $<$<CONFIG:Debug>:-g -O0>
        $<$<NOT:$<CONFIG:Debug>>:-O2>
    )
    # Security hardening (H3)
    target_compile_options(legends_compile_options INTERFACE
        -fstack-protector-strong -D_FORTIFY_SOURCE=2
    )
    if(NOT WIN32)
        target_compile_options(legends_compile_options INTERFACE -fPIE)
        target_link_options(legends_compile_options INTERFACE -pie)
    endif()
elseif(MSVC)
    target_compile_options(legends_compile_options INTERFACE /W4 /permissive- /utf-8)
    # MSVC 19.51+ (VS 18 2026 on windows-latest) deprecates non-string-literal
    # [[gsl::suppress]] args (C4875). Pinned gsl-lite still emits them
    # (gsl-lite.hpp:2218), which is fatal under /WX on legends_core/legends_ipc.
    # Tracked: https://github.com/CharlesHoskinson/ProjectLegends/issues/44
    # Remove /wd4875 when the gsl-lite pin advances past the upstream fix.
    target_compile_options(legends_compile_options INTERFACE /wd4875)
    target_compile_definitions(legends_compile_options INTERFACE _CRT_SECURE_NO_WARNINGS)
    # Security hardening (H3)
    target_link_options(legends_compile_options INTERFACE /GUARD:CF)
endif()

if(WIN32)
    target_compile_definitions(legends_compile_options INTERFACE WIN32 _CRT_SECURE_NO_WARNINGS)
endif()

# Helper function to apply C++23 and strict warnings to a target (Tier A)
function(legends_set_strict_cxx_standard target_name)
    target_link_libraries(${target_name} PRIVATE $<BUILD_INTERFACE:legends_compile_options>)
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
    target_link_libraries(${target_name} PRIVATE $<BUILD_INTERFACE:legends_compile_options>)
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
# Dependencies (loaded from cmake/dependencies.cmake above)
# ─────────────────────────────────────────────────────────────────────────────
#
# All dependency version pins and FetchContent declarations are centralized
# in cmake/dependencies.cmake. See DEPENDENCIES.md for the full manifest.
#
# gsl-lite: PRIVATE to legends_core — never exposed in public headers.
# SDL3: try-find-then-FetchContent for hermetic builds.
# GoogleTest/Benchmark: fetched in test/benchmark sections below using pinned tags.

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
set(AIBOX_BUILD_TESTS ON CACHE BOOL "Build engine tests alongside legends tests" FORCE)
set(AIBOX_HEADLESS ON CACHE BOOL "Build engine in headless mode" FORCE)
set(AIBOX_LIBRARY_MODE ON CACHE BOOL "Build engine as library" FORCE)

if(WIN32)
    add_compile_definitions(WIN32 _CRT_SECURE_NO_WARNINGS)
endif()

add_subdirectory(engine)

# ─────────────────────────────────────────────────────────────────────────────
# Legends Core Library
# ─────────────────────────────────────────────────────────────────────────────

set(LEGENDS_SOURCES
    src/legends/legends_embed_api.cpp
)
# All other sources (llm_*, vision_*, machine_context, headless_stub)
# are compiled via aibox_core. The legends headers in include/legends/
# are forwarding headers that alias aibox namespaces to legends.

add_library(legends_core STATIC ${LEGENDS_SOURCES})

# Apply C++23 standard (Tier A - new code, strict warnings)
legends_set_strict_cxx_standard(legends_core)

target_include_directories(legends_core
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# IMPORTANT: gsl-lite is PRIVATE - do NOT expose to consumers
# Consumers include legends_embed.h (pure C ABI), not gsl-lite types
target_link_libraries(legends_core
    PUBLIC
        aibox_core  # forwarding headers in include/legends/ reference aibox headers
    PRIVATE
        gsl::gsl-lite-v1
)

target_compile_definitions(legends_core
    PUBLIC
        LEGENDS_STATIC=1
    PRIVATE
        $<$<BOOL:${LEGENDS_HEADLESS}>:LEGENDS_HEADLESS=1>
        $<$<BOOL:${LEGENDS_LIBRARY_MODE}>:LEGENDS_LIBRARY_MODE=1>
        $<$<BOOL:${LEGENDS_BUILD_TESTS}>:LEGENDS_TESTING=1>
        # gsl-lite v1 strict C++23 configuration
        gsl_CONFIG_DEFAULTS_VERSION=1
        gsl_FEATURE_GSL_COMPATIBILITY_MODE=0
        gsl_FEATURE_STRING_SPAN=0
        gsl_FEATURE_BYTE=0
        gsl_CONFIG_NOT_NULL_EXPLICIT_CTOR=1
        gsl_CONFIG_TRANSPARENT_NOT_NULL=1
        gsl_CONFIG_CONTRACT_CHECKING_ON
        gsl_CONFIG_UNENFORCED_CONTRACTS_ELIDE
        # Contract violation behavior (mode-dependent):
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

# SDL3 backend (find_package/FetchContent handled in cmake/dependencies.cmake)
if(PAL_BACKEND_SDL3)
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
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
)

target_compile_definitions(legends_pal
    PUBLIC
        $<$<BOOL:${PAL_BACKEND_HEADLESS}>:PAL_HAS_HEADLESS=1>
        $<$<BOOL:${PAL_BACKEND_SDL2}>:PAL_HAS_SDL2=1>
        $<$<BOOL:${PAL_BACKEND_SDL3}>:PAL_HAS_SDL3=1>
        PAL_DEFAULT_BACKEND="${PAL_DEFAULT_BACKEND}"
)

target_link_libraries(legends_pal PRIVATE gsl::gsl-lite-v1)

target_compile_definitions(legends_pal
    PRIVATE
        gsl_CONFIG_DEFAULTS_VERSION=1
        gsl_CONFIG_CONTRACT_CHECKING_ON
        gsl_CONFIG_CONTRACT_VIOLATION_TERMINATES=1
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
# IPC Library (MIT-licensed — no GPL dependencies)
# ─────────────────────────────────────────────────────────────────────────────
#
# The legends_ipc library provides message serialization and IPC transport
# for the process isolation architecture. It is MIT-licensed and MUST NOT
# link any GPL code (aibox_core, legends_core).
#
# See docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md (TDD-LIC-001)

add_library(legends_ipc STATIC
    src/legends_ipc/protocol.cpp
    src/legends_ipc/messages.cpp
    src/legends_ipc/message_codec.cpp
    src/legends_ipc/framebuffer_shm.cpp
    src/legends_ipc/audio_ring.cpp
    $<$<PLATFORM_ID:Windows>:src/legends_ipc/platform/windows/shared_memory_win.cpp>
    $<$<NOT:$<PLATFORM_ID:Windows>>:src/legends_ipc/platform/posix/shared_memory_posix.cpp>
    $<$<PLATFORM_ID:Windows>:src/legends_ipc/platform/windows/control_channel_win.cpp>
    $<$<NOT:$<PLATFORM_ID:Windows>>:src/legends_ipc/platform/posix/control_channel_posix.cpp>
    $<$<PLATFORM_ID:Windows>:src/legends_ipc/platform/windows/engine_spawner_win.cpp>
    $<$<NOT:$<PLATFORM_ID:Windows>>:src/legends_ipc/platform/posix/engine_spawner_posix.cpp>
)

legends_set_strict_cxx_standard(legends_ipc)

target_include_directories(legends_ipc
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
)

target_link_libraries(legends_ipc PUBLIC gsl::gsl-lite-v1)

target_compile_definitions(legends_ipc PUBLIC
    gsl_CONFIG_DEFAULTS_VERSION=1
    gsl_CONFIG_CONTRACT_CHECKING_ON
    gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1
)

# IMPORTANT: legends_ipc must NOT link any GPL-licensed targets.
# This is verified by REQ-ISO-003 and REQ-ISO-016.

# ─────────────────────────────────────────────────────────────────────────────
# Engine Host Executable (GPL-2.0 — links engine + IPC)
# ─────────────────────────────────────────────────────────────────────────────
#
# The engine host runs the DOSBox-X engine in a separate process and
# communicates with the application shell via IPC. It is GPL-2.0 licensed
# because it links legends_core and aibox_core.

if(LEGENDS_USE_IPC)
    add_executable(legends_engine_host
        src/engine_host/main.cpp
        src/engine_host/cli_parser.cpp
        src/engine_host/engine_dispatcher.cpp
        src/engine_host/version_info.cpp
    )

    legends_set_strict_cxx_standard(legends_engine_host)

    target_link_libraries(legends_engine_host PRIVATE
        legends_core
        legends_ipc
    )

    target_include_directories(legends_engine_host PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src/engine_host
    )

    target_compile_definitions(legends_engine_host PRIVATE
        LEGENDS_ENGINE_HOST=1
    )
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Proxy Library (MIT-licensed — IPC frontend for legends_embed.h)
# ─────────────────────────────────────────────────────────────────────────────
#
# The legends_proxy library implements the legends_embed.h C API by forwarding
# calls over IPC to the engine host process. It links only legends_ipc (MIT).
# This enables the application shell to remain non-GPL.

if(LEGENDS_USE_IPC)
    add_library(legends_proxy STATIC
        src/legends_proxy/proxy_api.cpp
        src/legends_proxy/proxy_connection.cpp
        src/legends_proxy/crash_handler.cpp
        src/legends_proxy/heartbeat.cpp
    )

    legends_set_strict_cxx_standard(legends_proxy)

    target_include_directories(legends_proxy
        PUBLIC
            $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
            $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
        PRIVATE
            ${CMAKE_CURRENT_SOURCE_DIR}/src/legends_proxy
    )

    # IMPORTANT: legends_proxy must NOT link any GPL-licensed targets.
    # It links only legends_ipc (MIT).
    target_link_libraries(legends_proxy
        PUBLIC
            legends_ipc
    )

    target_compile_definitions(legends_proxy
        PUBLIC
            LEGENDS_USE_IPC=1
            LEGENDS_STATIC=1
    )
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Backend Switch: IPC mode vs monolithic
# ─────────────────────────────────────────────────────────────────────────────
# When LEGENDS_USE_IPC is ON, the application shell links legends_proxy
# instead of legends_core, removing all GPL object code from the binary.
# This is the core mechanism for GPL v2 process isolation.
# The actual switch is inside the PAL_BACKEND_SDL2 block (Main Executable section).

# ─────────────────────────────────────────────────────────────────────────────
# Wasm/WASI Target (Wasmtime Sandbox)
# ─────────────────────────────────────────────────────────────────────────────
#
# When LEGENDS_BUILD_WASM is ON, configure the build for a wasm32-wasi target.
# This requires a WASI SDK or compatible toolchain (e.g., wasi-sdk, Rust wasm32-wasi).
# This block is a planned scaffold: the referenced wasm.md and
# wit/legends-emulator.wit artifacts are not present at HEAD, and no checked-in
# toolchain file currently makes LEGENDS_BUILD_WASM a complete build path.
#
# See ARCHITECTURE.md for the planned Wasm sandbox design.

if(LEGENDS_BUILD_WASM)
    message(STATUS "Wasm/WASI build enabled")

    # Verify toolchain is targeting wasm32
    if(NOT CMAKE_SYSTEM_PROCESSOR MATCHES "wasm" AND NOT DEFINED WASI_SDK_PREFIX)
        message(WARNING
            "LEGENDS_BUILD_WASM is ON but no WASI toolchain detected. "
            "Set WASI_SDK_PREFIX or use a wasm32-wasi CMake toolchain file."
        )
    endif()

    # Wasm-specific compile definitions for the core libraries
    target_compile_definitions(legends_core PRIVATE LEGENDS_BUILD_WASM=1)

    # WIT generation target (requires wit-bindgen or wasm-tools)
    find_program(WIT_BINDGEN_EXECUTABLE wit-bindgen)
    if(WIT_BINDGEN_EXECUTABLE)
        add_custom_target(legends_wit_generate
            COMMAND ${WIT_BINDGEN_EXECUTABLE} c
                --world legends-emulator
                "${CMAKE_CURRENT_SOURCE_DIR}/wit/legends-emulator.wit"
                --out-dir "${CMAKE_CURRENT_BINARY_DIR}/wit-generated"
            WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
            COMMENT "Generating WIT bindings for legends-emulator"
            SOURCES wit/legends-emulator.wit
        )
    else()
        message(STATUS "wit-bindgen not found; WIT generation target disabled")
    endif()

    # Wasm component validation target (requires wasm-tools)
    find_program(WASM_TOOLS_EXECUTABLE wasm-tools)
    if(WASM_TOOLS_EXECUTABLE)
        add_custom_target(legends_wasm_validate
            COMMAND ${WASM_TOOLS_EXECUTABLE} component validate
                "$<TARGET_FILE:legends_core>"
            COMMENT "Validating Wasm component"
        )
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Application Library (shared between executable and unit tests)
# ─────────────────────────────────────────────────────────────────────────────
#
# The legends_app STATIC library collects all src/app/ sources plus supporting
# external/engine files (glad, zmbv) so they are compiled once and linked by
# both the project_legends executable and the legends_unit_tests target.

add_library(legends_app STATIC
    src/app/application.cpp
    src/app/runtime_host.cpp
    src/app/cli_parser.cpp
    src/app/config_parser.cpp
    src/app/platform_dirs.cpp
    src/app/scancode_map.cpp
    src/app/action_bus.cpp
    src/app/capture.cpp
    src/app/input_mapper.cpp
    src/app/save_manager.cpp
    src/app/menu_system.cpp
    src/app/hotkey_dispatcher.cpp
    src/app/mount_manager.cpp
    src/app/image_validator.cpp
    src/app/zmbv_codec.cpp
    src/app/video_capture.cpp
    src/app/mapper_ui.cpp
    src/app/save_browser.cpp
    src/app/overlay_render.cpp
    # Phase 3: Enhanced Features
    src/app/joystick_mapper.cpp
    src/app/shader_renderer.cpp
    src/app/shader_presets.cpp
    src/app/ai_config.cpp
    src/app/ai_http_client.cpp
    src/app/ai_screen_context.cpp
    src/app/ai_panel.cpp
    src/app/audio_mixer.cpp
    src/app/midi_config.cpp
    src/app/printer_manager.cpp
    src/app/ttf_renderer.cpp
    src/app/ipx_config.cpp
    src/app/glide_config.cpp
    src/app/pc98_config.cpp
    # Phase 4: Polish & Release
    src/app/file_logger.cpp
    src/app/error_reporter.cpp
    src/app/crash_breadcrumb.cpp
    src/app/crash_reporter.cpp
    # Phase 4 Sprint 4: SSIM
    src/app/ssim.cpp
    # Phase 4 Sprint 6: Portable mode
    src/app/portable_mode.cpp
    # Phase 4 Sprint 7: Update checker
    src/app/update_checker.cpp
    $<$<PLATFORM_ID:Windows>:src/app/update_checker_win.cpp>
    $<$<PLATFORM_ID:Darwin>:src/app/update_checker_mac.cpp>
    $<$<AND:$<NOT:$<PLATFORM_ID:Windows>>,$<NOT:$<PLATFORM_ID:Darwin>>>:src/app/update_checker_linux.cpp>
    # External / engine support files
    external/glad/glad.c
    engine/src/libs/zmbv/zmbv.cpp       # ZMBV codec for video capture
    engine/src/libs/zmbv/zmbv_stubs.cpp  # Stub VideoCodec when C_SSHOT is off
)

legends_set_strict_cxx_standard(legends_app)

target_include_directories(legends_app
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/src>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/external
        ${CMAKE_CURRENT_SOURCE_DIR}/external/glad
        ${CMAKE_CURRENT_SOURCE_DIR}/engine/src/libs  # ZMBV codec headers
        ${CMAKE_BINARY_DIR}/include
)

target_link_libraries(legends_app
    PUBLIC
        legends_core
        legends_pal
    PRIVATE
        gsl::gsl-lite-v1
)

target_compile_definitions(legends_app PRIVATE
    gsl_CONFIG_DEFAULTS_VERSION=1
    gsl_CONFIG_CONTRACT_CHECKING_ON
    gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1
)

function(legends_configure_app_entrypoint_target target_name)
    target_include_directories(${target_name} PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${CMAKE_CURRENT_SOURCE_DIR}/src
        ${CMAKE_CURRENT_SOURCE_DIR}/external
        ${CMAKE_CURRENT_SOURCE_DIR}/external/glad
        ${CMAKE_CURRENT_SOURCE_DIR}/engine/src/libs
        ${CMAKE_BINARY_DIR}/include
    )

    target_link_libraries(${target_name} PRIVATE gsl::gsl-lite-v1)

    target_compile_definitions(${target_name} PRIVATE
        gsl_CONFIG_DEFAULTS_VERSION=1
        gsl_CONFIG_CONTRACT_CHECKING_ON
        gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1
    )
endfunction()

# ─────────────────────────────────────────────────────────────────────────────
# Tests
# ─────────────────────────────────────────────────────────────────────────────

if(LEGENDS_BUILD_TESTS)
    enable_testing()

    # GoogleTest (version pinned in cmake/dependencies.cmake)
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG        ${LEGENDS_DEP_GOOGLETEST_TAG}
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
        tests/unit/test_legends_embed_lifecycle.cpp
        tests/unit/test_legends_embed_capture.cpp
        tests/unit/test_legends_embed_input.cpp
        tests/unit/test_legends_embed_savestate.cpp
        tests/unit/test_legends_embed_security.cpp
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
        tests/unit/test_gsl_contracts.cpp
        # Extended Test Coverage (Phase 2)
        tests/unit/test_thread_safety.cpp
        tests/unit/test_error_codes.cpp
        tests/unit/test_edge_cases.cpp
        tests/unit/test_stress.cpp
        tests/unit/test_negative.cpp
        # Portable Serialization Tests
        tests/unit/test_portable_serialize.cpp
        # Sprint 2: Global-to-Context Migration Wiring Tests
        tests/unit/test_sprint2_migration.cpp
        # Sprint 2: Instance Migration TDD Tests
        tests/unit/test_instance_migration.cpp
        # Audit Fix Tests
        tests/unit/test_safe_arithmetic.cpp
        tests/unit/test_text_input_utf8.cpp
        # Phase 0: Runtime Safety
        tests/unit/test_reentrancy_guard.cpp
        tests/unit/test_config_deep_copy.cpp
        tests/unit/test_headless_reset.cpp
        # Phase A: CPU Bridge
        tests/unit/test_cpu_bridge_sync.cpp
        # Phase B: Serialization
        tests/unit/test_wire_format.cpp
        tests/unit/test_pic_serialization.cpp
        tests/unit/test_v4_serialization.cpp
        # Phase D: PIC Hardware Tests
        tests/unit/test_pic_hardware.cpp
        # Phase C: Context Unification
        tests/unit/test_timing_single_source.cpp
        tests/unit/test_context_guard_unified.cpp
        tests/unit/test_context_unification.cpp
        # Phase E: Determinism at Scale
        tests/unit/test_determinism_at_scale.cpp
        # Phase 1: QA
        tests/unit/test_cli_parser.cpp
        tests/unit/test_config_parser.cpp
        tests/unit/test_platform_dirs.cpp
        tests/unit/test_scancode_mapping.cpp
        # Phase 2: Core Experience
        tests/unit/test_action_bus.cpp
        tests/unit/test_pause_reset.cpp
        tests/unit/test_capture.cpp
        tests/unit/test_input_mapper.cpp
        tests/unit/test_save_manager.cpp
        tests/unit/test_clipboard_paste.cpp
        tests/unit/test_menu_system.cpp
        tests/unit/test_hotkey_dispatcher.cpp
        tests/unit/test_mount_manager.cpp
        tests/unit/test_zmbv_codec.cpp
        tests/unit/test_video_capture.cpp
        tests/unit/test_mapper_ui.cpp
        tests/unit/test_save_browser.cpp
        tests/unit/test_menu_bar.cpp
        # Phase 3: Enhanced Features
        tests/unit/test_fullscreen_toggle.cpp
        tests/unit/test_joystick_mapper.cpp
        tests/unit/test_shader_presets.cpp
        tests/unit/test_ai_config.cpp
        tests/unit/test_ai_screen_context.cpp
        tests/unit/test_ai_http_client.cpp
        tests/unit/test_ai_panel.cpp
        tests/unit/test_audio_mixer.cpp
        tests/unit/test_midi_config.cpp
        tests/unit/test_printer_manager.cpp
        tests/unit/test_ttf_renderer.cpp
        tests/unit/test_ipx_config.cpp
        tests/unit/test_glide_config.cpp
        tests/unit/test_pc98_config.cpp
        # Phase 3: Bridge layer tests
        tests/unit/test_phase3_bridge.cpp
        # Phase 4: Polish & Release
        tests/unit/test_file_logger.cpp
        tests/unit/test_error_reporter.cpp
        tests/unit/test_crash_breadcrumb.cpp
        tests/unit/test_crash_reporter.cpp
        # Phase 4 Sprint 2: Application coverage
        tests/unit/test_application_init.cpp
        tests/unit/test_application_events.cpp
        tests/unit/test_application_lifecycle.cpp
        # Phase 4 Sprint 4: SSIM
        tests/unit/test_ssim.cpp
        # Phase 4 Sprint 6: Portable mode
        tests/unit/test_portable_mode.cpp
        # Phase 4 Sprint 7: Update checker
        tests/unit/test_update_checker.cpp
        # IPC Process Isolation
        tests/unit/test_ipc_wire_format.cpp
        tests/unit/test_ipc_message_header.cpp
        tests/unit/test_ipc_messages.cpp
        tests/unit/test_ipc_message_codec.cpp
        tests/unit/test_ipc_shared_memory.cpp
        tests/unit/test_ipc_framebuffer_shm.cpp
        tests/unit/test_ipc_audio_ring.cpp
        tests/unit/test_ipc_control_channel.cpp
        tests/unit/test_engine_host_cli.cpp
        tests/unit/test_engine_dispatcher.cpp
        tests/unit/test_proxy_connection.cpp
        tests/unit/test_proxy_api.cpp
        tests/unit/test_engine_spawner.cpp
        tests/unit/test_crash_handler.cpp
        tests/unit/test_heartbeat.cpp
    )

    # Apply C++23 standard (Tier A - tests should be strict too)
    legends_set_strict_cxx_standard(legends_unit_tests)

    target_link_libraries(legends_unit_tests PRIVATE
        legends_app
        legends_ipc
        GTest::gtest_main
        GTest::gmock
        gsl::gsl-lite-v1  # Tests may use gsl-lite directly for testing
    )

    # Engine host sources for IPC dispatcher tests (not part of legends_app)
    target_sources(legends_unit_tests PRIVATE
        src/engine_host/cli_parser.cpp
        src/engine_host/engine_dispatcher.cpp
    )

    target_include_directories(legends_unit_tests PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src/legends  # F6: internal FFI headers
        ${CMAKE_CURRENT_SOURCE_DIR}/src/engine_host  # Engine host dispatcher tests
        ${CMAKE_BINARY_DIR}/include
        ${CMAKE_CURRENT_SOURCE_DIR}/tests/unit      # Shared test fixtures
    )

    target_compile_definitions(legends_unit_tests PRIVATE
        LEGENDS_LIBRARY_MODE=1
        LEGENDS_TESTING=1
        # gsl-lite contract config (must match legends_core)
        gsl_CONFIG_DEFAULTS_VERSION=1
        gsl_CONFIG_CONTRACT_CHECKING_ON
        gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1
    )
    # R1 / issue #45: intentional WRONG_THREAD tests skip under TSan so the
    # enforced TSan lane does not treat deliberate cross-thread calls as bugs.
    string(CONCAT _legends_cxx_flags_for_tsan
        "${CMAKE_CXX_FLAGS} ${CMAKE_CXX_FLAGS_DEBUG} ${CMAKE_CXX_FLAGS_RELEASE}")
    if(_legends_cxx_flags_for_tsan MATCHES "fsanitize=thread")
        target_compile_definitions(legends_unit_tests PRIVATE LEGENDS_TSAN_BUILD=1)
    endif()
    if(MSVC)
        # Test code intentionally exercises [[nodiscard]] APIs in negative paths.
        # Keep /WX on production targets while containing this to test binaries.
        target_compile_options(legends_unit_tests PRIVATE /wd4834)
    elseif(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
        target_compile_options(legends_unit_tests PRIVATE -Wno-error)
    endif()

    gtest_discover_tests(legends_unit_tests
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        PROPERTIES
            LABELS "unit"
            TIMEOUT 30
    )

    # ─────────────────────────────────────────────────────────────────────────
    # IPC Integration Tests (requires LEGENDS_USE_IPC and engine host)
    # ─────────────────────────────────────────────────────────────────────────

    if(LEGENDS_USE_IPC)
        add_executable(legends_ipc_integration_tests
            tests/integration/test_ipc_integration.cpp
        )

        legends_set_strict_cxx_standard(legends_ipc_integration_tests)

        target_link_libraries(legends_ipc_integration_tests PRIVATE
            legends_ipc
            GTest::gtest_main
        )

        target_compile_definitions(legends_ipc_integration_tests PRIVATE
            gsl_CONFIG_DEFAULTS_VERSION=1
            gsl_CONFIG_CONTRACT_CHECKING_ON
            gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1
        )
        if(MSVC)
            target_compile_options(legends_ipc_integration_tests PRIVATE /wd4834)
        endif()

        add_dependencies(legends_ipc_integration_tests legends_engine_host)

        gtest_discover_tests(legends_ipc_integration_tests
            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            PROPERTIES LABELS "integration;ipc"
        )
    endif()

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

    add_custom_target(legends-test-unit
        COMMAND ${CMAKE_CTEST_COMMAND} -L unit --output-on-failure
        DEPENDS legends_unit_tests
        COMMENT "Running legends unit tests"
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
        tests/toolchain/test_shell_h_headless.cpp
    )

    # Apply C++23 standard (this IS the gate test - must be strict)
    legends_set_strict_cxx_standard(legends_toolchain_tests)

    target_link_libraries(legends_toolchain_tests PRIVATE
        GTest::gtest_main
    )

    target_compile_definitions(legends_toolchain_tests PRIVATE
        LEGENDS_LIBRARY_MODE=1
        AIBOX_HEADLESS=1
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
        tests/integration/test_agent_smoke.cpp
        # Input/SaveState Tests (Issues 1, 3, 4, 5)
        tests/integration/test_input_injection.cpp
        tests/integration/test_save_state_safety.cpp
        # Debugging Report Remediation (F1, F2)
        tests/integration/test_v2_load_safety.cpp
        tests/integration/test_load_state_atomicity.cpp
        # Phase -1: Engine I/O Plumbing
        tests/integration/test_framebuffer_plumbing.cpp
        tests/integration/test_audio_plumbing.cpp
        tests/integration/test_presentation_contract.cpp
        # Phase 1: QA
        tests/integration/test_volume_control.cpp
        tests/integration/test_dynamic_resolution.cpp
        # Phase 4: Soak & Endurance
        tests/integration/test_soak_endurance.cpp
        # Phase 4, Sprint 3: Integration Test Suite
        tests/integration/test_boot_to_prompt.cpp
        tests/integration/test_determinism_hash.cpp
        tests/integration/test_replay_determinism.cpp
        tests/integration/test_cross_platform_smoke.cpp
        tests/integration/test_save_state_compat.cpp
        tests/integration/test_pairwise_config.cpp
        # Phase 4, Sprint 4: Visual, Audio, and Timing Tests
        tests/integration/test_golden_visual.cpp
        tests/integration/test_visual_regression.cpp
        tests/integration/test_audio_validation.cpp
        tests/integration/test_frame_timing.cpp
        # Phase 4, Sprint 7: Full Lifecycle
        tests/integration/test_full_lifecycle.cpp
        # Phase 2: Mounting + Video Capture
        tests/integration/test_mount_lifecycle.cpp
        tests/integration/test_video_capture_lifecycle.cpp
        tests/integration/test_event_callbacks.cpp
    )

    legends_set_strict_cxx_standard(legends_integration_tests)

    # Sprint 4: SSIM source needed by golden visual & visual regression tests
    target_sources(legends_integration_tests PRIVATE
        src/app/ssim.cpp
    )

    target_include_directories(legends_integration_tests PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
        ${CMAKE_CURRENT_SOURCE_DIR}/tests/integration  # Shared test fixtures
    )

    target_link_libraries(legends_integration_tests PRIVATE
        legends_core
        legends_pal
        GTest::gtest_main
        GTest::gmock
    )

    target_compile_definitions(legends_integration_tests PRIVATE
        LEGENDS_LIBRARY_MODE=1
    )
    if(MSVC)
        target_compile_options(legends_integration_tests PRIVATE /wd4834)
    elseif(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
        target_compile_options(legends_integration_tests PRIVATE -Wno-error)
    endif()

    gtest_discover_tests(legends_integration_tests
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        PROPERTIES
            LABELS "integration"
            TIMEOUT 60
    )

    # Override labels for soak tests so they are excluded from normal CI
    # and only run in the soak-nightly workflow.
    # Note: gtest_discover_tests registers tests at CTest time, so we use
    # DISCOVERY_MODE PRE_TEST above and set properties via a CTest hook
    # script instead. The soak label is applied by test name prefix matching
    # in cmake/SoakTestLabels.cmake (if present).
    # set_tests_properties cannot be used here because the tests are not
    # yet registered at configure time.

    add_custom_target(test-integration
        COMMAND ${CMAKE_CTEST_COMMAND} -L integration --label-exclude soak --output-on-failure
        DEPENDS legends_integration_tests
        COMMENT "Running integration tests (excluding soak)"
    )

    # Soak tests: long-running endurance tests (excluded from normal CI)
    add_custom_target(test-soak
        COMMAND ${CMAKE_CTEST_COMMAND} -L soak --output-on-failure --timeout 46800
        DEPENDS legends_integration_tests
        COMMENT "Running soak/endurance tests"
    )

    # test-all includes all test types (excluding soak)
    add_custom_target(legends-test-all
        COMMAND ${CMAKE_CTEST_COMMAND} --label-exclude soak --output-on-failure
        DEPENDS legends_unit_tests legends_abi_test legends_integration_tests
        COMMENT "Running all legends tests (excluding soak)"
    )

    # ── Coverage Check (Phase 4 Sprint 7) ─────────────────────────────────
    # Report-only src/app/ coverage target. CI uploads coverage artifacts but
    # does not enforce a threshold until a stable baseline is established.
    find_program(LCOV_EXE lcov)
    find_program(GENHTML_EXE genhtml)
    if(LCOV_EXE AND GENHTML_EXE AND CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
        add_custom_target(coverage-check
            COMMENT "Generating report-only coverage for src/app/"
            COMMAND ${LCOV_EXE} --capture --directory . --output-file coverage.info --quiet
            COMMAND ${LCOV_EXE} --extract coverage.info "*/src/app/*" --output-file coverage_app.info --quiet
            COMMAND ${GENHTML_EXE} coverage_app.info --output-directory coverage_report --quiet
            COMMAND ${LCOV_EXE} --summary coverage_app.info
                | grep -oP "lines\\.+:\\s+\\K[0-9.]+" || true
            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            DEPENDS legends_unit_tests legends_integration_tests
        )
    endif()

endif()

# ─────────────────────────────────────────────────────────────────────────────
# Fuzz Testing
# ─────────────────────────────────────────────────────────────────────────────

if(ENABLE_FUZZING)
    add_subdirectory(tests/fuzz)
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Benchmarks
# ─────────────────────────────────────────────────────────────────────────────

option(LEGENDS_BUILD_BENCHMARKS "Build performance benchmarks" OFF)

if(LEGENDS_BUILD_BENCHMARKS)
    FetchContent_Declare(
        benchmark
        GIT_REPOSITORY https://github.com/google/benchmark.git
        GIT_TAG        ${LEGENDS_DEP_BENCHMARK_TAG}
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

    # Emulation performance benchmarks (Phase 4)
    add_executable(emulation_benchmarks
        benchmarks/bench_emulation.cpp
    )

    legends_set_strict_cxx_standard(emulation_benchmarks)

    target_link_libraries(emulation_benchmarks PRIVATE
        legends_core
        benchmark::benchmark
    )

    target_include_directories(emulation_benchmarks PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${CMAKE_BINARY_DIR}/include
    )

    target_compile_definitions(emulation_benchmarks PRIVATE
        LEGENDS_LIBRARY_MODE=1
    )

    # IPC performance benchmarks (Sprint 8: Process Isolation)
    add_executable(legends_ipc_benchmarks
        benchmarks/bench_ipc_overhead.cpp
    )

    legends_set_strict_cxx_standard(legends_ipc_benchmarks)

    target_link_libraries(legends_ipc_benchmarks PRIVATE
        legends_ipc
        benchmark::benchmark
        benchmark::benchmark_main
    )

    target_compile_definitions(legends_ipc_benchmarks PRIVATE
        gsl_CONFIG_DEFAULTS_VERSION=1
        gsl_CONFIG_CONTRACT_CHECKING_ON
        gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1
    )
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Main Executable
# ─────────────────────────────────────────────────────────────────────────────

# Build the interactive emulator executable when SDL2 is available
if(PAL_BACKEND_SDL2)
    add_executable(project_legends
        src/main.cpp
        # REQ-QA-015: Windows DPI awareness manifest
        $<$<PLATFORM_ID:Windows>:src/app/project_legends.manifest>
    )

    legends_set_strict_cxx_standard(project_legends)
    legends_configure_app_entrypoint_target(project_legends)

    target_include_directories(project_legends PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/external/SDL2/include
    )

    if(WIN32)
        target_link_directories(project_legends PRIVATE
            ${CMAKE_CURRENT_SOURCE_DIR}/external/SDL2/lib
        )
    endif()

    # In IPC mode, link the proxy (MIT) instead of legends_core (GPL).
    # In monolithic mode (default), link legends_core directly.
    if(LEGENDS_USE_IPC)
        target_link_libraries(project_legends PRIVATE
            legends_proxy
            legends_pal
        )
        target_compile_definitions(project_legends PRIVATE
            LEGENDS_USE_IPC=1
        )
    else()
        target_link_libraries(project_legends PRIVATE
            legends_app
            legends_pal
        )
    endif()

    if(WIN32)
        target_link_libraries(project_legends PRIVATE mingw32 SDL2main SDL2)
    elseif(TARGET SDL2::SDL2)
        target_link_libraries(project_legends PRIVATE SDL2::SDL2)
    else()
        target_link_libraries(project_legends PRIVATE ${SDL2_LIBRARIES})
    endif()

    # Copy SDL2.dll to output directory for local Windows builds that use the
    # bundled SDL2 binary layout.
    if(WIN32 AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/external/SDL2/bin/SDL2.dll")
        add_custom_command(TARGET project_legends POST_BUILD
            COMMAND ${CMAKE_COMMAND} -E copy_if_different
                "${CMAKE_CURRENT_SOURCE_DIR}/external/SDL2/bin/SDL2.dll"
                "$<TARGET_FILE_DIR:project_legends>"
        )
    endif()

    message(STATUS "Building project_legends executable with SDL2")
endif()

# Build the interactive emulator executable when SDL3 is available
if(PAL_BACKEND_SDL3)
    add_executable(project_legends
        src/main.cpp
        $<$<PLATFORM_ID:Windows>:src/app/project_legends.manifest>
        src/app/runtime_host.cpp
        src/app/application.cpp
        src/app/action_bus.cpp
        src/app/capture.cpp
        src/app/input_mapper.cpp
        src/app/save_manager.cpp
        src/app/menu_system.cpp
        src/app/hotkey_dispatcher.cpp
        src/app/cli_parser.cpp
        src/app/config_parser.cpp
        src/app/platform_dirs.cpp
        src/app/scancode_map.cpp
        src/app/mount_manager.cpp
        src/app/image_validator.cpp
        src/app/video_capture.cpp
        src/app/zmbv_codec.cpp
        src/app/mapper_ui.cpp
        src/app/save_browser.cpp
        src/app/overlay_render.cpp
        # Phase 3: Enhanced Features
        src/app/joystick_mapper.cpp
        src/app/shader_renderer.cpp
        src/app/shader_presets.cpp
        src/app/ai_config.cpp
        src/app/ai_http_client.cpp
        src/app/ai_screen_context.cpp
        src/app/ai_panel.cpp
        src/app/audio_mixer.cpp
        src/app/midi_config.cpp
        src/app/printer_manager.cpp
        src/app/ttf_renderer.cpp
        src/app/ipx_config.cpp
        src/app/glide_config.cpp
        src/app/pc98_config.cpp
        # Phase 4: Polish & Release
        src/app/file_logger.cpp
        src/app/error_reporter.cpp
        src/app/crash_breadcrumb.cpp
        src/app/crash_reporter.cpp
        # Phase 4 Sprint 4: SSIM
        src/app/ssim.cpp
        # Phase 4 Sprint 6: Portable mode
        src/app/portable_mode.cpp
        # Phase 4 Sprint 7: Update checker (platform-conditional)
        src/app/update_checker.cpp
        $<$<PLATFORM_ID:Windows>:src/app/update_checker_win.cpp>
        $<$<PLATFORM_ID:Darwin>:src/app/update_checker_mac.cpp>
        $<$<AND:$<NOT:$<PLATFORM_ID:Windows>>,$<NOT:$<PLATFORM_ID:Darwin>>>:src/app/update_checker_linux.cpp>
        external/glad/glad.c
        engine/src/libs/zmbv/zmbv.cpp       # ZMBV codec for video capture
        engine/src/libs/zmbv/zmbv_stubs.cpp  # Stub VideoCodec when C_SSHOT is off
    )

    legends_set_strict_cxx_standard(project_legends)
    legends_configure_app_entrypoint_target(project_legends)

    # In IPC mode, link the proxy (MIT) instead of legends_core (GPL).
    # In monolithic mode (default), link legends_app which transitively
    # brings in legends_core and legends_pal.
    if(LEGENDS_USE_IPC)
        target_link_libraries(project_legends PRIVATE
            legends_proxy
            legends_pal
            SDL3::SDL3-shared
        )
        target_compile_definitions(project_legends PRIVATE
            LEGENDS_USE_IPC=1
        )
    else()
        target_link_libraries(project_legends PRIVATE
            legends_app
            SDL3::SDL3-shared
        )
    endif()

    # Phase 3: Optional feature-gated library linking
    if(LEGENDS_ENABLE_AI AND CURL_FOUND)
        target_link_libraries(project_legends PRIVATE CURL::libcurl)
        target_compile_definitions(project_legends PRIVATE LEGENDS_HAS_CURL=1)
    endif()
    if(LEGENDS_ENABLE_FLUIDSYNTH AND FluidSynth_FOUND)
        target_link_libraries(project_legends PRIVATE FluidSynth::FluidSynth)
        target_compile_definitions(project_legends PRIVATE LEGENDS_HAS_FLUIDSYNTH=1)
    endif()
    if(LEGENDS_ENABLE_MT32 AND TARGET mt32emu)
        target_link_libraries(project_legends PRIVATE mt32emu)
        target_compile_definitions(project_legends PRIVATE LEGENDS_HAS_MT32=1)
    endif()

    # Copy SDL3.dll next to the executable so it can be found at runtime
    if(WIN32 AND TARGET SDL3-shared)
        add_custom_command(TARGET project_legends POST_BUILD
            COMMAND ${CMAKE_COMMAND} -E copy_if_different
                "$<TARGET_FILE:SDL3::SDL3-shared>"
                "$<TARGET_FILE_DIR:project_legends>"
            COMMENT "Copying SDL3.dll to output directory"
        )
    endif()

    message(STATUS "Building project_legends executable with SDL3")
endif()

# Guard: SDL2 and SDL3 executables cannot coexist in a single build tree
if(PAL_BACKEND_SDL2 AND PAL_BACKEND_SDL3)
    message(FATAL_ERROR
        "Cannot enable both PAL_BACKEND_SDL2 and PAL_BACKEND_SDL3 "
        "for the project_legends executable. Pick one.")
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Installation
# ─────────────────────────────────────────────────────────────────────────────

include(GNUInstallDirs)

# When SDL3 is built from FetchContent, legends_pal cannot be in the export
# set because SDL3-shared is not an installed/imported target.  Install it
# without EXPORT in that case.
if(PAL_BACKEND_SDL3 AND NOT SDL3_FOUND)
    install(TARGETS legends_core aibox_core
        EXPORT LegendsTargets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    )
    install(TARGETS legends_pal
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    )
else()
    install(TARGETS legends_core legends_pal aibox_core
        EXPORT LegendsTargets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    )
endif()

install(DIRECTORY include/legends include/pal
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)

# License files (COPYING, LICENSE, NOTICE) — required by GPL v2 Section 1
install(FILES
    "${CMAKE_CURRENT_SOURCE_DIR}/COPYING"
    "${CMAKE_CURRENT_SOURCE_DIR}/LICENSE"
    "${CMAKE_CURRENT_SOURCE_DIR}/NOTICE"
    DESTINATION ${CMAKE_INSTALL_DOCDIR}
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

install(EXPORT LegendsTargets
    NAMESPACE Legends::
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Legends
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/LegendsConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/LegendsConfigVersion.cmake"
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Legends
)

# ─────────────────────────────────────────────────────────────────────────────
# Module DAG Verification (Sprint 3)
# ─────────────────────────────────────────────────────────────────────────────
#
# Verify static library DAG at configure time.
# This ensures:
#   - No circular dependencies between internal libraries
#   - Only allowed dependencies are linked
#   - Clean module boundaries are enforced
#
# See cmake/ModuleManifest.cmake for module definitions.
# See cmake/ModuleDAG.cmake for verification logic.

legends_verify_all_dags()

# Optional: Print the graph during verbose builds
if(CMAKE_VERBOSE_MAKEFILE)
    legends_print_dag()
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Packaging (CPack — must come last)
# ─────────────────────────────────────────────────────────────────────────────
include(cmake/packaging.cmake)
