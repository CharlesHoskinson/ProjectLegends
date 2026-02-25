/**
 * @file test_presentation_contract.cpp
 * @brief REQ-PLUMB-005: Presentation contract enforcement tests.
 *
 * Validates the lock/unlock/present cycle using the headless backend
 * to ensure the software rendering pipeline contract is stable.
 */

#include <gtest/gtest.h>
#include <pal/platform.h>
#include <pal/context.h>
#include <pal/window.h>
#include <cstring>

class PresentationContractTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        ASSERT_EQ(pal::Platform::initialize(pal::Backend::Headless),
                  pal::Result::Success);

        window_ = pal::Platform::createWindow();
        ASSERT_NE(window_, nullptr);

        pal::WindowConfig config;
        config.width = 640;
        config.height = 400;
        ASSERT_EQ(window_->create(config), pal::Result::Success);

        context_ = pal::Platform::createContext(*window_);
        ASSERT_NE(context_, nullptr);

        ASSERT_EQ(context_->createSoftware(640, 400, pal::PixelFormat::RGBA8888),
                  pal::Result::Success);
    }

    void TearDown() override {
        context_.reset();
        window_.reset();
        pal::Platform::shutdown();
    }

    std::unique_ptr<pal::IWindow> window_;
    std::unique_ptr<pal::IContext> context_;
};

// REQ-PLUMB-005: Lock, write, unlock cycle succeeds
TEST_F(PresentationContractTest, LockUnlockCycleSucceeds) {
    pal::SoftwareContext sctx;
    ASSERT_EQ(context_->lockSurface(sctx), pal::Result::Success);
    EXPECT_NE(sctx.pixels, nullptr);
    EXPECT_GT(sctx.pitch, 0u);
    EXPECT_EQ(sctx.width, 640u);
    EXPECT_EQ(sctx.height, 400u);
    EXPECT_TRUE(context_->isLocked());

    // Write a test pixel
    auto* pixels = static_cast<uint8_t*>(sctx.pixels);
    pixels[0] = 0xFF;

    context_->unlockSurface();
    EXPECT_FALSE(context_->isLocked());
}

// REQ-PLUMB-005: Window present is independent of unlock
TEST_F(PresentationContractTest, WindowPresentAfterUnlockIsIndependent) {
    pal::SoftwareContext sctx;
    ASSERT_EQ(context_->lockSurface(sctx), pal::Result::Success);
    context_->unlockSurface();

    // Present should succeed independently
    EXPECT_EQ(window_->present(), pal::Result::Success);
}

// REQ-PLUMB-005: Multiple lock/unlock cycles are stable
TEST_F(PresentationContractTest, MultipleCyclesStable) {
    for (int i = 0; i < 100; ++i) {
        pal::SoftwareContext sctx;
        ASSERT_EQ(context_->lockSurface(sctx), pal::Result::Success)
            << "Lock failed on cycle " << i;
        EXPECT_NE(sctx.pixels, nullptr);

        // Write a byte to exercise the buffer
        auto* pixels = static_cast<uint8_t*>(sctx.pixels);
        pixels[0] = static_cast<uint8_t>(i & 0xFF);

        context_->unlockSurface();
        EXPECT_FALSE(context_->isLocked())
            << "Still locked after unlock on cycle " << i;
    }
}
