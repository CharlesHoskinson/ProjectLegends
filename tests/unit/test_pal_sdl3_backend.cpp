// SPDX-License-Identifier: GPL-2.0-or-later
// Test SDL3 backend functionality

#include <gtest/gtest.h>
#include "pal/platform.h"
#include "pal/window.h"
#include "pal/context.h"
#include "pal/audio_sink.h"
#include "pal/host_clock.h"
#include "pal/input_source.h"

#ifdef PAL_HAS_SDL3

class SDL3BackendTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Shutdown any previous backend
        pal::Platform::shutdown();
        // Initialize SDL3 backend
        auto result = pal::Platform::initialize(pal::Backend::SDL3);
        ASSERT_EQ(result, pal::Result::Success) << "Failed to initialize SDL3 backend";
    }

    void TearDown() override {
        pal::Platform::shutdown();
    }
};

TEST_F(SDL3BackendTest, BackendInitializes) {
    EXPECT_TRUE(pal::Platform::isInitialized());
    EXPECT_EQ(pal::Platform::getActiveBackend(), pal::Backend::SDL3);
    EXPECT_STREQ(pal::Platform::getBackendName(), "SDL3");
}

TEST_F(SDL3BackendTest, HostClockWorks) {
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

TEST_F(SDL3BackendTest, WindowCreates) {
    auto window = pal::Platform::createWindow();
    ASSERT_NE(window, nullptr);

    pal::WindowConfig config{};
    config.width = 640;
    config.height = 480;
    config.title = "SDL3 Test Window";
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

TEST_F(SDL3BackendTest, ContextCreatesSoftwareWithTexture) {
    auto window = pal::Platform::createWindow();
    ASSERT_NE(window, nullptr);

    pal::WindowConfig wconfig{};
    wconfig.width = 320;
    wconfig.height = 200;
    wconfig.title = "SDL3 Context Test";
    ASSERT_EQ(window->create(wconfig), pal::Result::Success);

    auto context = pal::Platform::createContext(*window);
    ASSERT_NE(context, nullptr);

    // SDL3 uses texture-based software rendering
    auto result = context->createSoftware(320, 200, pal::PixelFormat::RGBA8888);
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_TRUE(context->isCreated());
    EXPECT_EQ(context->getType(), pal::ContextType::Software);

    // Lock texture and write pixels
    pal::SoftwareContext sctx;
    result = context->lockSurface(sctx);
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_NE(sctx.pixels, nullptr);
    EXPECT_GT(sctx.pitch, 0u);
    EXPECT_EQ(sctx.width, 320u);
    EXPECT_EQ(sctx.height, 200u);

    context->unlockSurface();
    context->destroy();
    window->destroy();
}

TEST_F(SDL3BackendTest, AudioSinkOpensWithStream) {
    auto sink = pal::Platform::createAudioSink();
    ASSERT_NE(sink, nullptr);

    pal::AudioConfig config{};
    config.sample_rate = 44100;
    config.channels = 2;
    config.buffer_ms = 50;

    auto result = sink->open(config);
    EXPECT_EQ(result, pal::Result::Success);
    EXPECT_TRUE(sink->isOpen());

    // SDL3 uses push model with SDL_AudioStream
    int16_t samples[1024] = {0};
    result = sink->pushSamples(samples, 512); // 512 frames = 1024 samples stereo
    EXPECT_EQ(result, pal::Result::Success);

    EXPECT_GT(sink->getQueuedFrames(), 0u);

    sink->close();
    EXPECT_FALSE(sink->isOpen());
}

TEST_F(SDL3BackendTest, InputSourceInitializes) {
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

TEST_F(SDL3BackendTest, HostClockNanosecondSleep) {
    auto clock = pal::Platform::createHostClock();
    ASSERT_NE(clock, nullptr);

    auto result = clock->initialize();
    EXPECT_EQ(result, pal::Result::Success);

    // SDL3 has nanosecond precision sleep via SDL_DelayNS
    uint64_t t1 = clock->getTicksUs();
    clock->sleepUs(1000); // Sleep 1ms using microsecond API
    uint64_t t2 = clock->getTicksUs();

    // Should have elapsed at least 500us
    EXPECT_GT(t2 - t1, 500);

    clock->shutdown();
}

#else

TEST(SDL3BackendTest, NotAvailable) {
    GTEST_SKIP() << "SDL3 backend not built";
}

#endif
