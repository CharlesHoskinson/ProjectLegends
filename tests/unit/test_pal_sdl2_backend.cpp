// SPDX-License-Identifier: GPL-2.0-or-later
// Test SDL2 backend functionality

#include <gtest/gtest.h>
#include "pal/platform.h"
#include "pal/window.h"
#include "pal/context.h"
#include "pal/audio_sink.h"
#include "pal/host_clock.h"
#include "pal/input_source.h"

#ifdef PAL_HAS_SDL2

class SDL2BackendTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Shutdown any previous backend
        pal::Platform::shutdown();
        // Initialize SDL2 backend
        auto result = pal::Platform::initialize(pal::Backend::SDL2);
        ASSERT_EQ(result, pal::Result::Success) << "Failed to initialize SDL2 backend";
    }

    void TearDown() override {
        pal::Platform::shutdown();
    }
};

TEST_F(SDL2BackendTest, BackendInitializes) {
    EXPECT_TRUE(pal::Platform::isInitialized());
    EXPECT_EQ(pal::Platform::getActiveBackend(), pal::Backend::SDL2);
    EXPECT_STREQ(pal::Platform::getBackendName(), "SDL2");
}

TEST_F(SDL2BackendTest, HostClockWorks) {
    auto clock = pal::Platform::createHostClock();
    ASSERT_NE(clock, nullptr);
    
    auto result = clock->initialize();
    EXPECT_EQ(result, pal::Result::Success);
    
    uint64_t t1 = clock->getTicksUs();
    clock->sleepMs(10);
    uint64_t t2 = clock->getTicksUs();
    
    // Should have elapsed at least 5ms (allowing for timing variance)
    EXPECT_GT(t2 - t1, 5000);
    
    clock->shutdown();
}

TEST_F(SDL2BackendTest, WindowCreates) {
    auto window = pal::Platform::createWindow();
    ASSERT_NE(window, nullptr);
    
    pal::WindowConfig config{};
    config.width = 640;
    config.height = 480;
    config.title = "SDL2 Test Window";
    config.resizable = true;
    config.fullscreen = false;
    
    auto result = window->create(config);
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_TRUE(window->isCreated());
    
    uint32_t w, h;
    window->getSize(w, h);
    EXPECT_EQ(w, 640u);
    EXPECT_EQ(h, 480u);
    
    window->destroy();
    EXPECT_FALSE(window->isCreated());
}

TEST_F(SDL2BackendTest, ContextCreatesSoftware) {
    auto window = pal::Platform::createWindow();
    ASSERT_NE(window, nullptr);
    
    pal::WindowConfig wconfig{};
    wconfig.width = 320;
    wconfig.height = 200;
    wconfig.title = "Context Test";
    ASSERT_EQ(window->create(wconfig), pal::Result::Success);
    
    auto context = pal::Platform::createContext(*window);
    ASSERT_NE(context, nullptr);
    
    auto result = context->createSoftware(320, 200, pal::PixelFormat::RGBA8888);
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_TRUE(context->isCreated());
    EXPECT_EQ(context->getType(), pal::ContextType::Software);
    
    // Lock surface and write pixels
    pal::SoftwareContext sctx;
    result = context->lockSurface(sctx);
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_NE(sctx.pixels, nullptr);
    EXPECT_GT(sctx.pitch, 0u);
    
    context->unlockSurface();
    context->destroy();
    window->destroy();
}

TEST_F(SDL2BackendTest, AudioSinkOpens) {
    auto sink = pal::Platform::createAudioSink();
    ASSERT_NE(sink, nullptr);
    
    pal::AudioConfig config{};
    config.sample_rate = 44100;
    config.channels = 2;
    config.buffer_ms = 50;
    
    auto result = sink->open(config);
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_TRUE(sink->isOpen());
    
    // Push some samples
    int16_t samples[1024] = {0};
    result = sink->pushSamples(samples, 512); // 512 frames = 1024 samples stereo
    EXPECT_EQ(result, pal::Result::Success);
    
    EXPECT_GT(sink->getQueuedFrames(), 0u);
    
    sink->close();
    EXPECT_FALSE(sink->isOpen());
}

TEST_F(SDL2BackendTest, InputSourceInitializes) {
    auto input = pal::Platform::createInputSource();
    ASSERT_NE(input, nullptr);
    
    auto result = input->initialize();
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_TRUE(input->isInitialized());
    
    // Poll should return 0 events (none queued)
    pal::InputEvent events[10];
    uint32_t count = input->poll(events, 10);
    EXPECT_EQ(count, 0u);
    
    input->shutdown();
    EXPECT_FALSE(input->isInitialized());
}

#else

TEST(SDL2BackendTest, NotAvailable) {
    GTEST_SKIP() << "SDL2 backend not built";
}

#endif
