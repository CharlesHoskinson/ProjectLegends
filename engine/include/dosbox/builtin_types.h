/*
 *  Copyright (C) 2002-2021  The DOSBox Team
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 */

/**
 * @file builtin_types.h
 * @brief Public type definitions for built-in file blobs
 *
 * This header provides the BuiltinFileBlob struct definition as part of
 * the engine's public API. The actual blob data is defined in private
 * source files (engine/src/builtin/*.cpp).
 *
 * Module: aibox_core (public API)
 */

#ifndef DOSBOX_BUILTIN_TYPES_H
#define DOSBOX_BUILTIN_TYPES_H

#include <cstddef>
#include <cstdint>

/**
 * @brief Binary blob for built-in executable/data files
 *
 * This structure represents a built-in file that is embedded directly
 * in the engine binary. These are used for internal tools like DOS
 * utilities (MEM.EXE, DEBUG.EXE, etc.) that are provided by the emulator.
 *
 * @note The data pointer remains valid for the lifetime of the engine.
 *       The data is stored in read-only memory (const).
 */
struct BuiltinFileBlob {
    /** Recommended filename when exposing to DOS (e.g., "MEM.EXE") */
    const char* recommended_file_name;

    /** Pointer to the raw binary data */
    const unsigned char* data;

    /** Size of the data in bytes */
    size_t length;
};

#endif /* DOSBOX_BUILTIN_TYPES_H */
