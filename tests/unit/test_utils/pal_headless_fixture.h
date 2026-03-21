// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 ProjectLegends Contributors
//
// Shared test fixture for PAL headless-mode tests.
// Handles Platform::shutdown()/initialize(Backend::Headless) in SetUp/TearDown.

#ifndef LEGENDS_TEST_UTILS_PAL_HEADLESS_FIXTURE_H
#define LEGENDS_TEST_UTILS_PAL_HEADLESS_FIXTURE_H

#include <gtest/gtest.h>
#include "pal/platform.h"

namespace pal {
namespace test_utils {

// ═══════════════════════════════════════════════════════════════════════════════
// PalHeadlessFixture: Ensures the PAL platform is initialized in headless mode
// before each test and cleanly shut down afterward.
// ═══════════════════════════════════════════════════════════════════════════════

class PalHeadlessFixture : public ::testing::Test {
protected:
    void SetUp() override {
        Platform::shutdown();
        ASSERT_EQ(Platform::initialize(Backend::Headless), Result::Success);
    }

    void TearDown() override {
        Platform::shutdown();
    }
};

} // namespace test_utils
} // namespace pal

#endif // LEGENDS_TEST_UTILS_PAL_HEADLESS_FIXTURE_H
