// SPDX-License-Identifier: MIT
//
// Performance benchmarks for IPC overhead.
// Uses Google Benchmark to measure control channel round-trip,
// shared memory flip+read, and audio push+pop latencies.

#include <benchmark/benchmark.h>
#include <legends_ipc/message_codec.h>
#include <legends_ipc/messages.h>
#include <legends_ipc/framebuffer_shm.h>
#include <legends_ipc/audio_ring.h>
#include <array>
#include <cstring>
#include <string>

#ifdef _WIN32
#include <windows.h>
#define GET_PID() static_cast<uint32_t>(GetCurrentProcessId())
#else
#include <unistd.h>
#define GET_PID() static_cast<uint32_t>(getpid())
#endif

using namespace legends_ipc;

static std::string bench_name(const char* base) {
    static int counter = 0;
    return std::string(base) + "_" + std::to_string(GET_PID()) +
           "_" + std::to_string(counter++);
}

// Benchmark: MessageCodec encode + decode round-trip
static void BM_CodecRoundTrip(benchmark::State& state) {
    MessageCodec codec;
    std::array<uint8_t, 28> payload{}; // StepMsResp size

    for (auto _ : state) {
        auto wire = MessageCodec::encode(MsgType::StepMsResp, 1, payload);
        codec.feed(wire);
        auto msg = codec.try_decode();
        benchmark::DoNotOptimize(msg);
    }
}
BENCHMARK(BM_CodecRoundTrip);

// Benchmark: Framebuffer write + flip + read
static void BM_FramebufferFlipRead(benchmark::State& state) {
    auto name = bench_name("bench_fb");
    auto fb = FramebufferShm::create(name, 640, 480);
    if (!fb) {
        state.SkipWithError("Failed to create framebuffer shm");
        return;
    }

    uint64_t last_idx = 0;
    for (auto _ : state) {
        auto buf = fb->begin_write();
        // Simulate partial write (just touch first/last pixel)
        buf[0] = 0xFF;
        buf[buf.size() - 1] = 0xFF;
        fb->end_write(640, 480);

        auto frame = fb->read_if_new(last_idx);
        if (frame) last_idx = frame->frame_index;
        benchmark::DoNotOptimize(frame);
    }
}
BENCHMARK(BM_FramebufferFlipRead);

// Benchmark: Audio ring push + pop
static void BM_AudioPushPop(benchmark::State& state) {
    auto name = bench_name("bench_audio");
    auto ring = AudioRingBuffer::create(name, 2048, 2, 44100);
    if (!ring) {
        state.SkipWithError("Failed to create audio ring");
        return;
    }

    std::array<int16_t, 2048> input{};
    std::array<int16_t, 2048> output{};

    for (auto _ : state) {
        ring->push(input);
        uint32_t n = ring->pop(output);
        benchmark::DoNotOptimize(n);
    }
}
BENCHMARK(BM_AudioPushPop);

// Benchmark: Message serialization
static void BM_StepMsRespSerialize(benchmark::State& state) {
    msg::StepMsResp resp;
    resp.error_code = 0;
    resp.cycles_executed = 500000;
    resp.emu_time_us = 100000;
    resp.stop_reason = 0;
    resp.events_processed = 42;

    std::array<uint8_t, msg::StepMsResp::serialized_size> buf{};

    for (auto _ : state) {
        resp.serialize(buf);
        auto r = msg::StepMsResp::deserialize(buf);
        benchmark::DoNotOptimize(r);
    }
}
BENCHMARK(BM_StepMsRespSerialize);

BENCHMARK_MAIN();
