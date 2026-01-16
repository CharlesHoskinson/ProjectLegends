# CompileFirewall.cmake
# PR #21: SDL Compile Firewall
#
# This module provides functions to verify that core library code
# does not depend on SDL symbols, ensuring clean headless operation.

# Function: aibox_verify_no_sdl_in_core
# Verifies that a target does not link against SDL or use SDL headers.
# This is enforced at configure time and optionally at link time.
#
# Usage:
#   aibox_verify_no_sdl_in_core(target_name)
#
function(aibox_verify_no_sdl_in_core TARGET_NAME)
    if(NOT TARGET ${TARGET_NAME})
        message(WARNING "aibox_verify_no_sdl_in_core: Target '${TARGET_NAME}' does not exist")
        return()
    endif()

    # Get the target's link libraries
    get_target_property(LINK_LIBS ${TARGET_NAME} LINK_LIBRARIES)

    if(LINK_LIBS)
        foreach(LIB ${LINK_LIBS})
            string(TOLOWER "${LIB}" LIB_LOWER)
            if(LIB_LOWER MATCHES "sdl")
                message(FATAL_ERROR
                    "SDL Compile Firewall Violation!\n"
                    "Target '${TARGET_NAME}' links against SDL: ${LIB}\n"
                    "Core library code must not depend on SDL.\n"
                    "Use platform abstraction interfaces instead.")
            endif()
        endforeach()
    endif()

    # Get include directories
    get_target_property(INCLUDE_DIRS ${TARGET_NAME} INCLUDE_DIRECTORIES)

    if(INCLUDE_DIRS)
        foreach(DIR ${INCLUDE_DIRS})
            string(TOLOWER "${DIR}" DIR_LOWER)
            if(DIR_LOWER MATCHES "sdl")
                message(WARNING
                    "SDL include directory in core target '${TARGET_NAME}': ${DIR}\n"
                    "This may indicate SDL header dependencies.")
            endif()
        endforeach()
    endif()

    message(STATUS "SDL Firewall: ${TARGET_NAME} passed SDL dependency check")
endfunction()

# Function: aibox_add_sdl_firewall_test
# Adds a post-build check to verify no SDL symbols in the binary.
# Only works on systems with nm or similar tools.
#
function(aibox_add_sdl_firewall_test TARGET_NAME)
    if(CMAKE_SYSTEM_NAME STREQUAL "Linux" OR CMAKE_SYSTEM_NAME STREQUAL "Darwin")
        add_custom_command(TARGET ${TARGET_NAME} POST_BUILD
            COMMAND ${CMAKE_COMMAND} -E echo "Checking ${TARGET_NAME} for SDL symbols..."
            COMMAND sh -c "nm $<TARGET_FILE:${TARGET_NAME}> 2>/dev/null | grep -i 'sdl' && echo 'WARNING: SDL symbols found' || echo 'No SDL symbols found'"
            VERBATIM
        )
    endif()
endfunction()
