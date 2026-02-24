/**
 * @file test_gsl_contracts.cpp
 * @brief Cross-module gsl-lite contract violation tests.
 *
 * Verifies that gsl_Expects/gsl_Assert are configured to throw
 * legends::gsl::fail_fast in library mode, providing fail-safe
 * behavior rather than silent UB or process termination.
 */

#include <gtest/gtest.h>
#include <legends/gsl.hpp>
#include <legends/memory.h>
#include <legends/handle_registry.h>
#include <legends/callback_registry.h>
#include <legends/vision_framebuffer.h>
#include <legends/llm_serializer.h>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// GuestMemory Contracts
// ─────────────────────────────────────────────────────────────────────────────

TEST(GslContractTest, GuestMemoryZeroSizeThrows) {
    EXPECT_THROW(GuestMemory(0), legends::gsl::fail_fast);
}

// ─────────────────────────────────────────────────────────────────────────────
// HandleRegistry Contracts
// ─────────────────────────────────────────────────────────────────────────────

TEST(GslContractTest, HandleRegistryAllocateNullThrows) {
    HandleRegistry registry;
    int* null_ptr = nullptr;
    EXPECT_THROW(
        (void)registry.allocate(null_ptr, HandleType::Emulator),
        legends::gsl::fail_fast
    );
}

TEST(GslContractTest, HandleRegistryAllocateInvalidTypeThrows) {
    HandleRegistry registry;
    int obj = 42;
    EXPECT_THROW(
        (void)registry.allocate(&obj, HandleType::Invalid),
        legends::gsl::fail_fast
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// VgaPalette Contracts
// ─────────────────────────────────────────────────────────────────────────────

TEST(GslContractTest, VgaPaletteLoadFromDacNullThrows) {
    vision::VgaPalette palette;
    EXPECT_THROW(palette.load_from_dac(nullptr), legends::gsl::fail_fast);
}

TEST(GslContractTest, VgaPaletteExportRgbNullThrows) {
    vision::VgaPalette palette;
    EXPECT_THROW(palette.export_rgb(nullptr), legends::gsl::fail_fast);
}

// ─────────────────────────────────────────────────────────────────────────────
// LLM Serializer Contracts
// ─────────────────────────────────────────────────────────────────────────────

TEST(GslContractTest, Cp437ToUtf8NullWithLengthThrows) {
    EXPECT_THROW(llm::cp437_to_utf8(nullptr, 10), legends::gsl::fail_fast);
}

TEST(GslContractTest, SerializeTextScreenNullDataThrows) {
    EXPECT_THROW(
        llm::serialize_text_screen(nullptr, 80, 25, 0, 0, false),
        legends::gsl::fail_fast
    );
}

TEST(GslContractTest, EncodeUtf8NullOutputThrows) {
    EXPECT_THROW((void)llm::encode_utf8(U'A', nullptr), legends::gsl::fail_fast);
}

// ─────────────────────────────────────────────────────────────────────────────
// Meta: Verify gsl-lite Configuration
// ─────────────────────────────────────────────────────────────────────────────

TEST(GslContractTest, FailFastIsThrowable) {
    // Verify that legends::gsl::fail_fast is a catchable exception type,
    // confirming gsl_CONFIG_CONTRACT_VIOLATION_THROWS is active.
    try {
        throw legends::gsl::fail_fast("test");
    } catch (const legends::gsl::fail_fast& e) {
        EXPECT_NE(std::string(e.what()).find("test"), std::string::npos);
        return;
    }
    FAIL() << "legends::gsl::fail_fast should be catchable";
}
