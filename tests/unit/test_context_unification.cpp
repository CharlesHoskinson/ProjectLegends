/**
 * @file test_context_unification.cpp
 * @brief Phase C: verify context TLS pointers and timing config unification.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>

class ContextUnificationTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
    }

    void TearDown() override {
        if (handle_) legends_destroy(handle_);
        handle_ = nullptr;
        pal::Platform::shutdown();
    }

    void createWithCycles(uint32_t cpu_cycles) {
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.cpu_cycles = cpu_cycles;
        auto err = legends_create(&cfg, &handle_);
        ASSERT_EQ(err, LEGENDS_OK) << "legends_create failed";
    }
};

// Both context TLS pointers set during legends_step_cycles.
// Proves dosbox context was active (timing updated) and no crash
// from compat shims.
TEST_F(ContextUnificationTest, DosboxContextSetDuringStep) {
    createWithCycles(3000);

    legends_step_result_t r{};
    auto err = legends_step_cycles(handle_, 100, &r);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(r.cycles_executed, 100u);

    uint64_t total = 0;
    legends_get_total_cycles(handle_, &total);
    EXPECT_EQ(total, 100u);
}

// g_cycles_per_ms accessor matches config: 5000 cycles at 5000 cycles/ms = 1ms = 1000us.
TEST_F(ContextUnificationTest, CyclesPerMsMatchesConfig) {
    createWithCycles(5000);

    legends_step_cycles(handle_, 5000, nullptr);

    uint64_t time_us = 0;
    legends_get_emu_time(handle_, &time_us);
    EXPECT_EQ(time_us, 1000u);
}

// Different rate: 6000 cycles/ms, step 3000 cycles => 500us.
TEST_F(ContextUnificationTest, DifferentRatesGiveCorrectTiming) {
    createWithCycles(6000);

    legends_step_cycles(handle_, 3000, nullptr);

    uint64_t time_us = 0;
    legends_get_emu_time(handle_, &time_us);
    EXPECT_EQ(time_us, 500u);
}
