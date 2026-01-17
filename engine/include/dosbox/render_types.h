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
 * @file render_types.h
 * @brief Public render/scaler type definitions
 *
 * This header provides the minimal public API types for the render system.
 * The full scaler implementation is in engine/src/gui/render_scalers.h (private).
 *
 * Module: aibox_core (public API)
 *
 * REFACTORING NOTE (Sprint 3):
 * Extracted from engine/src/gui/render_scalers.h to provide clean module boundaries.
 * render.h now includes this public header instead of ../src/gui/render_scalers.h.
 */

#ifndef DOSBOX_RENDER_TYPES_H
#define DOSBOX_RENDER_TYPES_H

/**
 * @brief Scaler color mode
 *
 * Defines the bit depth/color format for scaler operations.
 */
typedef enum {
    scalerMode8,    /**< 8-bit indexed color */
    scalerMode15,   /**< 15-bit color (5-5-5) */
    scalerMode16,   /**< 16-bit color (5-6-5) */
    scalerMode32    /**< 32-bit true color (8-8-8-8) */
} scalerMode_t;

/**
 * @brief Scaler operation type
 *
 * Defines which scaling algorithm to use for video output.
 * Some scalers require RENDER_USE_ADVANCED_SCALERS to be enabled.
 */
typedef enum scalerOperation {
    scalerOpNormal,     /**< Normal/nearest neighbor scaling */
#if RENDER_USE_ADVANCED_SCALERS > 2
    scalerOpAdvMame,    /**< AdvMAME2x/3x scaler */
    scalerOpAdvInterp,  /**< Advanced interpolation scaler */
    scalerOpHQ,         /**< HQ2x/HQ3x scaler */
    scalerOpSaI,        /**< 2xSaI scaler */
    scalerOpSuperSaI,   /**< Super 2xSaI scaler */
    scalerOpSuperEagle, /**< Super Eagle scaler */
#endif
#if RENDER_USE_ADVANCED_SCALERS > 0
    scalerOpTV,         /**< TV scanline effect */
    scalerOpRGB,        /**< RGB scanline effect */
    scalerOpScan,       /**< Scanline effect */
    scalerOpGray,       /**< Grayscale conversion */
#endif
    scalerLast          /**< Sentinel value */
} scalerOperation_t;

/**
 * @brief Line handler function pointer
 *
 * Function type for simple line-based scalers.
 * Takes a source line and renders it to the output buffer.
 *
 * @param src Pointer to source scanline data
 */
typedef void (*ScalerLineHandler_t)(const void* src);

/**
 * @brief Complex scaler handler function pointer
 *
 * Function type for complex scalers that require access to
 * multiple input lines (e.g., HQ2x, 2xSaI).
 */
typedef void (*ScalerComplexHandler_t)(void);

#endif /* DOSBOX_RENDER_TYPES_H */
