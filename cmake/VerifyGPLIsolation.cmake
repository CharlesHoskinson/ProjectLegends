# SPDX-License-Identifier: MIT
#
# VerifyGPLIsolation.cmake
#
# Post-build verification step that scans the linker map file for GPL symbols.
# Only active when LEGENDS_USE_IPC is ON.
#
# Usage: include(VerifyGPLIsolation) after defining the project_legends target.

if(NOT LEGENDS_USE_IPC)
    return()
endif()

find_package(Python3 COMPONENTS Interpreter QUIET)

if(NOT Python3_FOUND)
    message(WARNING "Python3 not found; GPL isolation verification disabled")
    return()
endif()

set(VERIFY_GPL_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/scripts/verify_gpl_isolation.py")

if(NOT EXISTS "${VERIFY_GPL_SCRIPT}")
    message(WARNING "verify_gpl_isolation.py not found; GPL isolation verification disabled")
    return()
endif()

# Generate linker map file based on compiler
if(MSVC)
    # MSVC: /MAP generates .map alongside the binary
    target_link_options(project_legends PRIVATE "/MAP")
    set(MAP_FILE "$<TARGET_FILE_DIR:project_legends>/$<TARGET_FILE_BASE_NAME:project_legends>.map")
elseif(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    # GCC/Clang: -Wl,-Map generates a map file
    target_link_options(project_legends PRIVATE "-Wl,-Map,$<TARGET_FILE_DIR:project_legends>/$<TARGET_FILE_BASE_NAME:project_legends>.map")
    set(MAP_FILE "$<TARGET_FILE_DIR:project_legends>/$<TARGET_FILE_BASE_NAME:project_legends>.map")
else()
    message(WARNING "Unknown compiler; GPL isolation map generation disabled")
    return()
endif()

# Post-build step: scan the map file
add_custom_command(
    TARGET project_legends POST_BUILD
    COMMAND ${Python3_EXECUTABLE} "${VERIFY_GPL_SCRIPT}" "${MAP_FILE}"
    COMMENT "Verifying GPL isolation in shell binary..."
    VERBATIM
)

message(STATUS "GPL isolation verification enabled (post-build)")
