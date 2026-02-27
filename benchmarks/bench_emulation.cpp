// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Google Benchmark: emulation performance benchmarks.
// REQ-TEST-009: Performance regression detection.

#include <legends/legends_embed.h>

#include <benchmark/benchmark.h>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <vector>

namespace {

/// Fixture that manages engine lifecycle for benchmarks.
class EmulationBenchmark : public benchmark::Fixture {
public:
    void SetUp(benchmark::State& /*state*/) override {
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.deterministic = 1;
        legends_error_t err = legends_create(&cfg, &engine_);
        if (err != LEGENDS_OK) {
            engine_ = nullptr;
        }
    }

    void TearDown(benchmark::State& /*state*/) override {
        if (engine_) {
            legends_destroy(engine_);
            engine_ = nullptr;
        }
    }

protected:
    legends_handle engine_ = nullptr;
};

// ── Step Cycles Benchmarks ───────────────────────────────────────────────

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_StepCycles_1K)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }
    for (auto _ : state) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 1, &result); // ~1ms ≈ ~1K cycles at default speed
    }
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_StepCycles_1K)
    ->Unit(benchmark::kMicrosecond)
    ->Iterations(10000);

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_StepCycles_100K)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }
    for (auto _ : state) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 100, &result); // ~100ms ≈ ~100K cycles
    }
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_StepCycles_100K)
    ->Unit(benchmark::kMillisecond)
    ->Iterations(100);

// ── Capture Benchmarks ──────────────────────────────────────────────────

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_CaptureRGB)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }

    // Step engine once to produce a frame
    legends_step_result_t result{};
    legends_step_ms(engine_, 16, &result);

    // Determine buffer size
    size_t size_needed = 0;
    uint16_t w = 0, h = 0;
    legends_capture_rgb(engine_, nullptr, 0, &size_needed, &w, &h);

    std::vector<uint8_t> buffer(std::max(size_needed, static_cast<size_t>(640 * 480 * 3)));

    for (auto _ : state) {
        legends_capture_rgb(engine_, buffer.data(), buffer.size(),
                           &size_needed, &w, &h);
    }
    state.SetBytesProcessed(
        static_cast<int64_t>(state.iterations()) *
        static_cast<int64_t>(size_needed));
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_CaptureRGB)
    ->Unit(benchmark::kMicrosecond);

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_CaptureAudio)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }

    // Step engine to produce audio
    legends_step_result_t result{};
    legends_step_ms(engine_, 16, &result);

    size_t avail = 0;
    legends_capture_audio(engine_, nullptr, 0, &avail);
    std::vector<int16_t> buffer(avail > 0 ? avail : 4096);

    for (auto _ : state) {
        size_t actual = 0;
        legends_step_ms(engine_, 16, &result);
        legends_capture_audio(engine_, buffer.data(), buffer.size(), &actual);
    }
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_CaptureAudio)
    ->Unit(benchmark::kMicrosecond);

// ── Save/Load State Benchmarks ──────────────────────────────────────────

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_SaveState)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }

    // Step to a stable state
    for (int i = 0; i < 10; ++i) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 16, &result);
    }

    // Determine save size
    size_t save_size = 0;
    legends_save_state(engine_, nullptr, 0, &save_size);
    std::vector<uint8_t> buffer(save_size > 0 ? save_size : 1024 * 1024);

    for (auto _ : state) {
        size_t actual = 0;
        legends_save_state(engine_, buffer.data(), buffer.size(), &actual);
    }
    state.SetBytesProcessed(
        static_cast<int64_t>(state.iterations()) *
        static_cast<int64_t>(save_size));
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_SaveState)
    ->Unit(benchmark::kMillisecond);

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_LoadState)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }

    // Step to a stable state and save
    for (int i = 0; i < 10; ++i) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 16, &result);
    }

    size_t save_size = 0;
    legends_save_state(engine_, nullptr, 0, &save_size);
    std::vector<uint8_t> buffer(save_size > 0 ? save_size : 1024 * 1024);
    size_t actual = 0;
    legends_save_state(engine_, buffer.data(), buffer.size(), &actual);

    for (auto _ : state) {
        legends_load_state(engine_, buffer.data(), actual);
    }
    state.SetBytesProcessed(
        static_cast<int64_t>(state.iterations()) *
        static_cast<int64_t>(actual));
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_LoadState)
    ->Unit(benchmark::kMillisecond);

// ── State Hash Benchmark ────────────────────────────────────────────────

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_StateHash)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }

    for (int i = 0; i < 10; ++i) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 16, &result);
    }

    for (auto _ : state) {
        uint64_t hash = 0;
        legends_get_state_hash(engine_, &hash);
        benchmark::DoNotOptimize(hash);
    }
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_StateHash)
    ->Unit(benchmark::kMicrosecond);

// ── Text Capture Benchmark ──────────────────────────────────────────────

BENCHMARK_DEFINE_F(EmulationBenchmark, BM_CaptureText)(benchmark::State& state) {
    if (!engine_) {
        state.SkipWithError("Engine creation failed");
        return;
    }

    for (int i = 0; i < 10; ++i) {
        legends_step_result_t result{};
        legends_step_ms(engine_, 16, &result);
    }

    legends_text_cell_t text_buf[4096];
    for (auto _ : state) {
        size_t count = 0;
        legends_capture_text(engine_, text_buf, 4096, &count, nullptr);
        benchmark::DoNotOptimize(count);
    }
}
BENCHMARK_REGISTER_F(EmulationBenchmark, BM_CaptureText)
    ->Unit(benchmark::kMicrosecond);

} // namespace

BENCHMARK_MAIN();
