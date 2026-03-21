// SPDX-License-Identifier: MIT
//
// Shared IPC test helpers: unique name generation and SHM skip guards.

#ifndef LEGENDS_TEST_UTILS_IPC_TEST_HELPERS_H
#define LEGENDS_TEST_UTILS_IPC_TEST_HELPERS_H

#include <gtest/gtest.h>
#include <string>

#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#else
#include <unistd.h>
#endif

namespace legends_ipc {
namespace test_utils {

/// Generate a unique IPC resource name using PID + monotonic counter.
/// Guarantees no collisions across tests in the same process.
inline std::string ipc_test_unique_name(const char* base) {
    static int counter = 0;
#ifdef _WIN32
    auto pid = static_cast<unsigned long>(GetCurrentProcessId());
#else
    auto pid = static_cast<unsigned long>(getpid());
#endif
    return std::string(base) + "_" + std::to_string(pid) +
           "_" + std::to_string(counter++);
}

} // namespace test_utils
} // namespace legends_ipc

/// Skip the current test if shared memory is not available (CI limitation).
/// Use at the top of any test that creates SHM resources.
#define SKIP_IF_NO_SHM(result_expr)                                            \
    do {                                                                        \
        auto _shm_result = (result_expr);                                      \
        if (!_shm_result.has_value()) {                                        \
            GTEST_SKIP() << "Shared memory not available "                     \
                            "(CI environment limitation)";                     \
        }                                                                      \
    } while (0)

#endif // LEGENDS_TEST_UTILS_IPC_TEST_HELPERS_H
