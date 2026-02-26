/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Copyright (C) 2024-2025 Charles Hoskinson and Contributors */
/*
 * DLL export/import macro for the legends_embed.h C ABI.
 *
 * REQ-API-014: Shared library symbol visibility
 *
 * Usage:
 *   - Static library builds: define LEGENDS_STATIC (set automatically by CMake)
 *   - DLL builds on Windows: define LEGENDS_BUILDING_DLL when compiling the library
 *   - Consumers importing: nothing to define (dllimport is the default)
 *   - GCC/Clang: uses visibility("default")
 */

#ifndef LEGENDS_EXPORT_H
#define LEGENDS_EXPORT_H

#if defined(LEGENDS_STATIC)
    #define LEGENDS_API
#elif defined(_WIN32) || defined(__CYGWIN__)
    #if defined(LEGENDS_BUILDING_DLL)
        #define LEGENDS_API __declspec(dllexport)
    #else
        #define LEGENDS_API __declspec(dllimport)
    #endif
#elif defined(__GNUC__) || defined(__clang__)
    #define LEGENDS_API __attribute__((visibility("default")))
#else
    #define LEGENDS_API
#endif

#endif /* LEGENDS_EXPORT_H */
