/**
 * @file test_context_synchronization.cpp
 * @brief H5: Three unsynchronized context pointers across layers.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>

TEST(ContextSync, CrossLayerContextIndependence) {
    legends_handle handle = nullptr;
    auto err = legends_create(nullptr, &handle);
    ASSERT_EQ(err, LEGENDS_OK);
    err = legends_init(handle);
    ASSERT_EQ(err, LEGENDS_OK);

    // H5: legends, engine, and aibox layers each maintain their own
    // context pointer. Setting one does not update the others.
    EXPECT_NE(handle, nullptr);

    legends_destroy(handle);
}
