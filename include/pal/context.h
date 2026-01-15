// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Rendering Context Interface

#pragma once

#include "pal/types.h"
#include <cstdint>

namespace pal {

/// Type of rendering context
enum class ContextType {
    None = 0,
    Software,    // Software surface / memory buffer
    OpenGL,      // OpenGL context
    Vulkan,      // Vulkan surface (future)
    GPU          // SDL3 GPU API (future)
};

/// Software context details returned by lockSurface()
struct SoftwareContext {
    void* pixels = nullptr;        // Pointer to pixel data
    uint32_t pitch = 0;            // Bytes per row
    uint32_t width = 0;            // Surface width in pixels
    uint32_t height = 0;           // Surface height in pixels
    PixelFormat format = PixelFormat::Unknown;
};

/// Rendering context interface
///
/// Provides access to software surfaces or OpenGL contexts.
/// PAL provides the context; existing OUTPUT_* code produces pixels.
class IContext {
public:
    virtual ~IContext() = default;

    // ═══════════════════════════════════════════════════════════════════════
    // Creation
    // ═══════════════════════════════════════════════════════════════════════

    /// Create a software rendering context (memory buffer)
    /// @return Success, InvalidParameter, OutOfMemory, AlreadyInitialized
    virtual Result createSoftware(uint32_t width, uint32_t height, PixelFormat fmt) = 0;

    /// Create an OpenGL rendering context
    /// @param major OpenGL major version (e.g., 3)
    /// @param minor OpenGL minor version (e.g., 3)
    /// @param core_profile True for core profile, false for compatibility
    /// @return Success, NotSupported, AlreadyInitialized
    virtual Result createOpenGL(int major, int minor, bool core_profile) = 0;

    /// Destroy the context and release resources
    virtual void destroy() = 0;

    /// Check if context has been created
    virtual bool isCreated() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Software Context Operations
    // ═══════════════════════════════════════════════════════════════════════

    /// Lock the software surface for direct pixel access
    /// @param ctx [out] Receives surface details
    /// @return Success, InvalidOperation (not software), AlreadyLocked
    virtual Result lockSurface(SoftwareContext& ctx) = 0;

    /// Unlock the software surface after writing pixels
    virtual void unlockSurface() = 0;

    /// Check if surface is currently locked
    virtual bool isLocked() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // OpenGL Context Operations
    // ═══════════════════════════════════════════════════════════════════════

    /// Make this OpenGL context current on the calling thread
    /// @return Success, InvalidOperation (not OpenGL), NotInitialized
    virtual Result makeCurrent() = 0;

    /// Swap front and back buffers (OpenGL double-buffering)
    virtual void swapBuffers() = 0;

    /// Get OpenGL function pointer by name
    /// @return Function pointer, or nullptr if not found
    virtual void* getProcAddress(const char* name) = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Query
    // ═══════════════════════════════════════════════════════════════════════

    /// Get the type of this context
    virtual ContextType getType() const = 0;
};

/// Convert ContextType to string for debugging
constexpr const char* toString(ContextType type) noexcept {
    switch (type) {
        case ContextType::None:     return "None";
        case ContextType::Software: return "Software";
        case ContextType::OpenGL:   return "OpenGL";
        case ContextType::Vulkan:   return "Vulkan";
        case ContextType::GPU:      return "GPU";
    }
    return "Unknown";
}

} // namespace pal
