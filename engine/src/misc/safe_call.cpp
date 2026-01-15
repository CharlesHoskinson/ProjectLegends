/**
 * @file safe_call.cpp
 * @brief Implementation of API boundary containment.
 *
 * Most of safe_call is header-only templates. This file provides:
 * - Explicit instantiations if needed
 * - Any non-template helper functions
 * - Ensures the translation unit is compiled for ODR
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/safe_call.h"

namespace dosbox {

// Currently all safe_call functionality is in the header as templates.
// This file exists to:
// 1. Ensure the header compiles correctly
// 2. Provide a place for future non-template implementations
// 3. Allow explicit template instantiations if needed for link-time optimization

namespace detail {

// Marker to ensure this translation unit is linked
// (prevents linker from discarding if all code is header-only)
volatile int safe_call_link_marker = 0;

} // namespace detail

} // namespace dosbox
