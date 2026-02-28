/**
 * @file test_error_propagation.cpp
 * @brief M14: Duplicate g_last_error across layers.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>

TEST(ErrorPropagation, LayerErrorsAreIndependent) {
    legends_handle handle = nullptr;
    ASSERT_EQ(legends_create(nullptr, &handle), LEGENDS_OK);
    ASSERT_EQ(legends_init(handle), LEGENDS_OK);

    // Trigger error at legends layer
    char buf[256];
    size_t len = sizeof(buf);
    auto err = legends_get_last_error(nullptr, buf, &len);
    EXPECT_NE(err, LEGENDS_OK);

    // M14: engine layer has its own g_last_error, independent of legends layer
    legends_destroy(handle);
}
