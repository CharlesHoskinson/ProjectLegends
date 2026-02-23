/**
 * @file test_timing_single_source.cpp
 * @brief Verify timing is routed through context, not a separate global.
 *
 * After Phase C, all timing queries go through g_context->timing
 * instead of the eliminated g_time_state.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <vector>

class TimingSingleSourceTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        legends_create(&cfg, &handle_);
    }
    void TearDown() override {
        if (handle_) legends_destroy(handle_);
        pal::Platform::shutdown();
    }
};

TEST_F(TimingSingleSourceTest, CyclesAccumulateCorrectly) {
    legends_step_result_t r{};
    legends_step_cycles(handle_, 1000, &r);
    EXPECT_EQ(r.cycles_executed, 1000u);

    legends_step_cycles(handle_, 2000, &r);
    EXPECT_EQ(r.cycles_executed, 2000u);

    uint64_t total = 0;
    legends_get_total_cycles(handle_, &total);
    EXPECT_EQ(total, 3000u);
}

TEST_F(TimingSingleSourceTest, EmuTimeConsistentWithCycles) {
    legends_step_cycles(handle_, 3000, nullptr);

    uint64_t time_us = 0;
    legends_get_emu_time(handle_, &time_us);
    // 3000 cycles at 3000 cycles/ms = 1ms = 1000us
    EXPECT_EQ(time_us, 1000u);
}

TEST_F(TimingSingleSourceTest, SaveLoadPreservesTiming) {
    legends_step_cycles(handle_, 3000, nullptr);

    // Save state
    size_t sz = 0;
    legends_save_state(handle_, nullptr, 0, &sz);
    std::vector<uint8_t> buf(sz);
    legends_save_state(handle_, buf.data(), sz, &sz);

    // Load state
    legends_load_state(handle_, buf.data(), sz);

    // Timing should survive round-trip
    uint64_t total = 0;
    legends_get_total_cycles(handle_, &total);
    EXPECT_EQ(total, 3000u);

    uint64_t time_us = 0;
    legends_get_emu_time(handle_, &time_us);
    EXPECT_EQ(time_us, 1000u);
}

TEST_F(TimingSingleSourceTest, SplitStepsEqualSingleStep) {
    // Determinism: 10000 cycles in one call == 5000+5000 in two calls
    legends_step_cycles(handle_, 5000, nullptr);
    legends_step_cycles(handle_, 5000, nullptr);

    uint64_t total = 0;
    legends_get_total_cycles(handle_, &total);
    EXPECT_EQ(total, 10000u);

    uint64_t time_us = 0;
    legends_get_emu_time(handle_, &time_us);
    // 10000 cycles at 3000 cycles/ms = 3.333ms = 3333us (integer division)
    EXPECT_EQ(time_us, 3333u);
}
