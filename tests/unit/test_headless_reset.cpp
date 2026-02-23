#include <gtest/gtest.h>
#include <aibox/headless_stub.h>

TEST(HeadlessState, ResetClearsAllState) {
    aibox::headless::AdvanceTicks(42);
    EXPECT_EQ(aibox::headless::GetTicks(), 42u);

    aibox::headless::ResetState();

    EXPECT_EQ(aibox::headless::GetTicks(), 0u);
    EXPECT_FALSE(aibox::headless::HasTimingProvider());
    EXPECT_FALSE(aibox::headless::HasDisplayProvider());
    EXPECT_FALSE(aibox::headless::HasInputProvider());
    EXPECT_FALSE(aibox::headless::HasAudioProvider());
}

TEST(HeadlessState, ResetRestoresDefaultVideoMode) {
    aibox::headless::SetVideoMode({640, 480, 32, false});
    aibox::headless::ResetState();

    auto mode = aibox::headless::GetVideoMode();
    EXPECT_EQ(mode.width, 320);
    EXPECT_EQ(mode.height, 200);
    EXPECT_EQ(mode.bpp, 8);
    EXPECT_TRUE(mode.is_indexed);
}
