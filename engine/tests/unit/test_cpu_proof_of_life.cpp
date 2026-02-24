/**
 * @file test_cpu_proof_of_life.cpp
 * @brief Proof-of-life: execute real x86 instructions and verify results.
 *
 * These tests write machine code into guest memory, step the CPU,
 * and read back memory to verify the CPU core actually executed
 * real x86 instructions (not a stub).
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_library.h"
#include "dosbox/dosbox_context.h"

class CpuProofOfLife : public ::testing::Test {
protected:
    dosbox_lib_handle_t handle_ = nullptr;

    void SetUp() override {
        dosbox_lib_config_t config = DOSBOX_LIB_CONFIG_INIT;
        config.memory_kb = 640;
        auto err = dosbox_lib_create(&config, &handle_);
        ASSERT_EQ(err, DOSBOX_LIB_OK) << "Failed to create instance";
        err = dosbox_lib_init(handle_);
        ASSERT_EQ(err, DOSBOX_LIB_OK) << "Failed to init instance";
    }

    void TearDown() override {
        if (handle_) {
            dosbox_lib_destroy(handle_);
            handle_ = nullptr;
        }
    }
};

/**
 * Memory witness test: MOV AX, 0x1234 / MOV [0x8000], AX / HLT
 *
 * This test writes x86 machine code at address 0x0000 (CS:IP = 0000:0000),
 * steps the CPU, and reads back memory at 0x8000 to verify the
 * MOV instruction actually executed.
 *
 * Machine code:
 *   B8 34 12       MOV AX, 0x1234
 *   A3 00 80       MOV [0x8000], AX
 *   F4             HLT
 */
TEST_F(CpuProofOfLife, MemoryWitness_MovAxStore) {
    // x86 machine code: MOV AX, 0x1234; MOV [0x8000], AX; HLT
    uint8_t code[] = {
        0xB8, 0x34, 0x12,       // MOV AX, 0x1234
        0xA3, 0x00, 0x80,       // MOV [0x8000], AX
        0xF4                    // HLT
    };

    // Write code at address 0 (CS:IP starts at 0000:0000)
    auto err = dosbox_lib_write_memory(handle_, code, 0x0000, sizeof(code));
    ASSERT_EQ(err, DOSBOX_LIB_OK) << "Failed to write code";

    // Clear witness location
    uint8_t zero[2] = {0, 0};
    err = dosbox_lib_write_memory(handle_, zero, 0x8000, 2);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Step enough cycles for 3 instructions
    dosbox_lib_step_result_t result{};
    err = dosbox_lib_step_cycles(handle_, 1000, &result);
    ASSERT_EQ(err, DOSBOX_LIB_OK) << "step_cycles failed";

    // CPU should have halted
    EXPECT_EQ(result.stop_reason, (uint32_t)DOSBOX_LIB_STOP_HALT)
        << "Expected HLT stop, got " << result.stop_reason;
    EXPECT_GT(result.cycles_executed, 0u)
        << "Expected some cycles executed";

    // Read back the witness location
    uint8_t readback[2] = {};
    err = dosbox_lib_read_memory(handle_, 0x8000, readback, 2);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Verify: little-endian 0x1234 = {0x34, 0x12}
    EXPECT_EQ(readback[0], 0x34) << "Low byte mismatch";
    EXPECT_EQ(readback[1], 0x12) << "High byte mismatch";
}

/**
 * Counter test: increment a byte in a loop.
 *
 * Machine code at 0x0000:
 *   loop:
 *     FE 06 00 80     INC BYTE [0x8000]
 *     EB FA           JMP SHORT loop   (offset -6, back to start)
 *
 * Run for enough cycles that the counter increments measurably,
 * then verify the witness byte is non-zero.
 */
TEST_F(CpuProofOfLife, CounterLoop) {
    uint8_t code[] = {
        0xFE, 0x06, 0x00, 0x80,  // INC BYTE [0x8000]
        0xEB, 0xFA               // JMP SHORT -6 (back to offset 0)
    };

    auto err = dosbox_lib_write_memory(handle_, code, 0x0000, sizeof(code));
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Clear counter
    uint8_t zero = 0;
    err = dosbox_lib_write_memory(handle_, &zero, 0x8000, 1);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Step many cycles - each loop iteration is ~10 cycles
    dosbox_lib_step_result_t result{};
    err = dosbox_lib_step_cycles(handle_, 5000, &result);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Should have completed (infinite loop exhausts budget)
    EXPECT_EQ(result.stop_reason, (uint32_t)DOSBOX_LIB_STOP_COMPLETED);
    EXPECT_GT(result.cycles_executed, 0u);

    // Read counter - should be non-zero (loop ran many times)
    uint8_t counter = 0;
    err = dosbox_lib_read_memory(handle_, 0x8000, &counter, 1);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    EXPECT_GT(counter, 0u) << "Counter should have incremented";
}

/**
 * ADD test: verify arithmetic works.
 *
 * Machine code:
 *   B0 25           MOV AL, 0x25
 *   04 1B           ADD AL, 0x1B
 *   A2 00 80        MOV [0x8000], AL
 *   F4              HLT
 *
 * Expected: 0x25 + 0x1B = 0x40 at address 0x8000.
 */
TEST_F(CpuProofOfLife, ArithmeticAdd) {
    uint8_t code[] = {
        0xB0, 0x25,             // MOV AL, 0x25
        0x04, 0x1B,             // ADD AL, 0x1B
        0xA2, 0x00, 0x80,       // MOV [0x8000], AL
        0xF4                    // HLT
    };

    auto err = dosbox_lib_write_memory(handle_, code, 0x0000, sizeof(code));
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    dosbox_lib_step_result_t result{};
    err = dosbox_lib_step_cycles(handle_, 1000, &result);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    EXPECT_EQ(result.stop_reason, (uint32_t)DOSBOX_LIB_STOP_HALT);

    uint8_t readback = 0;
    err = dosbox_lib_read_memory(handle_, 0x8000, &readback, 1);
    ASSERT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(readback, 0x40) << "0x25 + 0x1B should = 0x40";
}
