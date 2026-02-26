# SPDX-License-Identifier: GPL-2.0-or-later
# Copyright (C) 2024-2025 Charles Hoskinson and Contributors
#
# CPack packaging skeleton
#
# REQ-BUILD-005: Packaging artifacts for distribution
#
# This file MUST be included last in the top-level CMakeLists.txt
# because CPack reads variables at include() time.

set(CPACK_PACKAGE_NAME "ProjectLegends")
set(CPACK_PACKAGE_VENDOR "Charles Hoskinson and Contributors")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "Embeddable x86 Emulation Framework for AI-Driven Computing")
set(CPACK_PACKAGE_VERSION "${LEGENDS_VERSION_STRING}")
set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_SOURCE_DIR}/COPYING")

if(WIN32)
    set(CPACK_GENERATOR "NSIS;ZIP")
elseif(APPLE)
    set(CPACK_GENERATOR "DragNDrop;TGZ")
else()
    set(CPACK_GENERATOR "TGZ")
endif()

# Install the executable (if built)
if(TARGET project_legends)
    install(TARGETS project_legends RUNTIME DESTINATION bin)
endif()

# Install license files alongside the binary
install(FILES
    "${CMAKE_SOURCE_DIR}/COPYING"
    "${CMAKE_SOURCE_DIR}/LICENSE"
    "${CMAKE_SOURCE_DIR}/NOTICE"
    DESTINATION share/doc/ProjectLegends
)

include(CPack)
