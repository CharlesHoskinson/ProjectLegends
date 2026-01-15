// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// PAL Performance Benchmarks

#include <benchmark/benchmark.h>
#include "pal/platform.h"
#include "pal/window.h"
#include "pal/context.h"
#include "pal/audio_sink.h"
#include "pal/host_clock.h"
#include "pal/input_source.h"
#include <vector>
#include <cstring>

// ═══════════════════════════════════════════════════════════════════════════
// Benchmark Fixtures
// ═══════════════════════════════════════════════════════════════════════════

class PALBenchmark : public benchmark::Fixture {
public:
    void SetUp(const benchmark::State&) override {
        pal::Platform::shutdown();
        // Use headless for consistent benchmarking
        pal::Platform::initialize(pal::Backend::Headless);
    }

    void TearDown(const benchmark::State&) override {
        pal::Platform::shutdown();
    }
};

// ═══════════════════════════════════════════════════════════════════════════
// Host Clock Benchmarks
// ═══════════════════════════════════════════════════════════════════════════

BENCHMARK_F(PALBenchmark, BM_HostClockGetTicksUs)(benchmark::State& state) {
    auto clock = pal::Platform::createHostClock();
    clock->initialize();

    for (auto _ : state) {
        benchmark::DoNotOptimize(clock->getTicksUs());
    }

    clock->shutdown();
}

BENCHMARK_F(PALBenchmark, BM_HostClockGetTicksMs)(benchmark::State& state) {
    auto clock = pal::Platform::createHostClock();
    clock->initialize();

    for (auto _ : state) {
        benchmark::DoNotOptimize(clock->getTicksMs());
    }

    clock->shutdown();
}

// ═══════════════════════════════════════════════════════════════════════════
// Window Benchmarks
// ═══════════════════════════════════════════════════════════════════════════

BENCHMARK_F(PALBenchmark, BM_WindowCreateDestroy)(benchmark::State& state) {
    for (auto _ : state) {
        auto window = pal::Platform::createWindow();
        pal::WindowConfig config{640, 480, "Benchmark", false, false, true};
        window->create(config);
        window->destroy();
    }
}

BENCHMARK_F(PALBenchmark, BM_WindowGetSize)(benchmark::State& state) {
    auto window = pal::Platform::createWindow();
    pal::WindowConfig config{640, 480, "Benchmark", false, false, true};
    window->create(config);

    uint32_t w, h;
    for (auto _ : state) {
        window->getSize(w, h);
        benchmark::DoNotOptimize(w);
        benchmark::DoNotOptimize(h);
    }

    window->destroy();
}

// ═══════════════════════════════════════════════════════════════════════════
// Context Benchmarks
// ═══════════════════════════════════════════════════════════════════════════

BENCHMARK_F(PALBenchmark, BM_ContextLockUnlock)(benchmark::State& state) {
    auto window = pal::Platform::createWindow();
    pal::WindowConfig wconfig{320, 200, "Benchmark", false, false, true};
    window->create(wconfig);

    auto context = pal::Platform::createContext(*window);
    context->createSoftware(320, 200, pal::PixelFormat::RGBA8888);

    pal::SoftwareContext ctx;
    for (auto _ : state) {
        context->lockSurface(ctx);
        benchmark::DoNotOptimize(ctx.pixels);
        context->unlockSurface();
    }

    context->destroy();
    window->destroy();
}

BENCHMARK_F(PALBenchmark, BM_ContextFillFrame)(benchmark::State& state) {
    auto window = pal::Platform::createWindow();
    pal::WindowConfig wconfig{320, 200, "Benchmark", false, false, true};
    window->create(wconfig);

    auto context = pal::Platform::createContext(*window);
    context->createSoftware(320, 200, pal::PixelFormat::RGBA8888);

    pal::SoftwareContext ctx;
    for (auto _ : state) {
        context->lockSurface(ctx);
        // Simulate filling a frame (DOS 320x200 mode)
        std::memset(ctx.pixels, 0x42, ctx.pitch * ctx.height);
        context->unlockSurface();
    }

    state.SetBytesProcessed(state.iterations() * 320 * 200 * 4);
    context->destroy();
    window->destroy();
}

// ═══════════════════════════════════════════════════════════════════════════
// Audio Benchmarks
// ═══════════════════════════════════════════════════════════════════════════

BENCHMARK_F(PALBenchmark, BM_AudioPushSamples)(benchmark::State& state) {
    auto sink = pal::Platform::createAudioSink();
    pal::AudioConfig config{44100, 2, 100};
    sink->open(config);

    // 1ms of audio at 44100Hz stereo = 44 frames = 88 samples
    std::vector<int16_t> samples(88, 0);

    for (auto _ : state) {
        sink->pushSamples(samples.data(), 44);
    }

    state.SetItemsProcessed(state.iterations() * 44);
    sink->close();
}

BENCHMARK_F(PALBenchmark, BM_AudioGetQueued)(benchmark::State& state) {
    auto sink = pal::Platform::createAudioSink();
    pal::AudioConfig config{44100, 2, 100};
    sink->open(config);

    // Push some samples first
    std::vector<int16_t> samples(882, 0);  // 10ms
    sink->pushSamples(samples.data(), 441);

    for (auto _ : state) {
        benchmark::DoNotOptimize(sink->getQueuedFrames());
    }

    sink->close();
}

// ═══════════════════════════════════════════════════════════════════════════
// Input Benchmarks
// ═══════════════════════════════════════════════════════════════════════════

BENCHMARK_F(PALBenchmark, BM_InputPoll)(benchmark::State& state) {
    auto input = pal::Platform::createInputSource();
    input->initialize();

    pal::InputEvent events[64];
    for (auto _ : state) {
        benchmark::DoNotOptimize(input->poll(events, 64));
    }

    input->shutdown();
}

// ═══════════════════════════════════════════════════════════════════════════
// Combined Frame Simulation
// ═══════════════════════════════════════════════════════════════════════════

BENCHMARK_F(PALBenchmark, BM_SimulateFrame60Hz)(benchmark::State& state) {
    auto window = pal::Platform::createWindow();
    pal::WindowConfig wconfig{640, 480, "Benchmark", false, false, true};
    window->create(wconfig);

    auto context = pal::Platform::createContext(*window);
    context->createSoftware(640, 480, pal::PixelFormat::RGBA8888);

    auto audio = pal::Platform::createAudioSink();
    pal::AudioConfig aconfig{44100, 2, 50};
    audio->open(aconfig);

    auto input = pal::Platform::createInputSource();
    input->initialize();

    // Audio for 1 frame at 60Hz = ~735 frames
    std::vector<int16_t> audio_samples(1470, 0);
    pal::SoftwareContext ctx;
    pal::InputEvent events[64];

    for (auto _ : state) {
        // Poll input
        input->poll(events, 64);

        // Render frame
        context->lockSurface(ctx);
        std::memset(ctx.pixels, 0, ctx.pitch * ctx.height);
        context->unlockSurface();

        // Push audio
        audio->pushSamples(audio_samples.data(), 735);
    }

    input->shutdown();
    audio->close();
    context->destroy();
    window->destroy();
}

BENCHMARK_MAIN();
