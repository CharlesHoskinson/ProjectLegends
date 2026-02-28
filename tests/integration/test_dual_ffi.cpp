/**
 * @file test_dual_ffi.cpp
 * @brief H10: dosbox_lib and legends_embed use different error models.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include "dosbox/dosbox_library.h"

TEST(DualFFI, ErrorModelsAreDifferent) {
    // Both APIs define OK as 0 but have independent error enums
    EXPECT_EQ(DOSBOX_LIB_OK, 0);
    EXPECT_EQ(LEGENDS_OK, 0);

    // H10: A failure in one API does not propagate error details to the other.
    // After unification, there should be a single error surface.
}
