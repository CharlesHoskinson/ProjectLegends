/**
 * @file gsl.hpp
 * @brief Internal bridge header for gsl-lite v1.
 *
 * This header provides a scoped namespace alias for gsl-lite, isolating
 * the dependency to internal implementation files.
 *
 * IMPORTANT: gsl-lite is a PRIVATE dependency of legends_core.
 *            Do NOT include this header in public API headers.
 *            Do NOT expose gsl-lite types in legends_embed.h (C ABI).
 *
 * gsl-lite v1 uses:
 *   - Namespace: gsl_lite (not gsl)
 *   - Header: <gsl-lite/gsl-lite.hpp> (not <gsl/gsl>)
 *
 * Usage:
 * @code
 *   #include <legends/gsl.hpp>
 *
 *   void foo(legends::gsl::span<int> data) {
 *       legends::gsl::Expects(data.size() > 0);
 *       // ...
 *   }
 * @endcode
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include <gsl-lite/gsl-lite.hpp>

namespace legends {

/**
 * @brief Scoped alias for gsl-lite v1 namespace.
 *
 * We use a namespace alias rather than `using namespace` to:
 * 1. Avoid polluting legends namespace with gsl-lite symbols
 * 2. Make gsl-lite usage explicit and greppable (legends::gsl::span)
 * 3. Allow future migration to std:: equivalents with minimal changes
 */
namespace gsl = ::gsl_lite;

} // namespace legends
