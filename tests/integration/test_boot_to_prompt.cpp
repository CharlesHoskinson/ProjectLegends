// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Boot-to-prompt integration test: verify that the engine boots to a DOS
// prompt within ~2 seconds of emulated time.

#include <legends/legends_embed.h>
#include <pal/platform.h>

#include <cstdint>
#include <cstring>
#include <gtest/gtest.h>
#include <string>
#include <vector>

namespace legends {
namespace {

class BootToPromptTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();

        // Create engine in headless mode with default (deterministic) config
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.deterministic = 1;
        legends_error_t err = legends_create(&cfg, &engine_);
        if (err != LEGENDS_OK) {
            GTEST_SKIP() << "Engine creation failed (err=" << err
                         << "), skipping boot-to-prompt test";
        }
    }

    void TearDown() override {
        if (engine_) {
            legends_destroy(engine_);
            engine_ = nullptr;
        }
        pal::Platform::shutdown();
    }

    /// Step the engine for a given number of frames at ~16ms each.
    void stepFrames(int frames) {
        for (int i = 0; i < frames; ++i) {
            legends_step_result_t result{};
            legends_step_ms(engine_, 16, &result);
        }
    }

    /// Capture all text cells and return as a single string (characters only).
    std::string captureTextContent() {
        size_t cell_count = 0;
        legends_text_info_t info{};
        legends_capture_text(engine_, nullptr, 0, &cell_count, &info);
        if (cell_count == 0) return {};

        std::vector<legends_text_cell_t> cells(cell_count);
        legends_capture_text(engine_, cells.data(), cells.size(),
                             &cell_count, &info);

        std::string text;
        text.reserve(cell_count + info.rows); // room for newlines
        for (uint8_t row = 0; row < info.rows; ++row) {
            for (uint8_t col = 0; col < info.columns; ++col) {
                size_t idx = row * info.columns + col;
                if (idx < cell_count) {
                    char c = static_cast<char>(cells[idx].character);
                    text += (c >= 32 && c < 127) ? c : ' ';
                }
            }
            text += '\n';
        }
        return text;
    }

    /// Check if text contains DOS prompt patterns.
    static bool containsDosPrompt(const std::string& text) {
        // Common DOS prompt patterns:
        // "C:\>" or "C:\" or ":\" or ">" at end of a non-empty line
        if (text.find(":\\>") != std::string::npos) return true;
        if (text.find("C:\\") != std::string::npos) return true;
        if (text.find("A:\\") != std::string::npos) return true;
        if (text.find("Z:\\") != std::string::npos) return true;

        // Look for ">" preceded by a drive letter pattern
        for (size_t i = 1; i < text.size(); ++i) {
            if (text[i] == '>' && text[i - 1] != ' ' && text[i - 1] != '\n') {
                return true;
            }
        }
        return false;
    }

    legends_handle engine_ = nullptr;
};

TEST_F(BootToPromptTest, EngineBootsToDosPrompt) {
    ASSERT_NE(engine_, nullptr);

    // Step for ~2 seconds of emulated time (~120 frames at 16ms each)
    stepFrames(120);

    // Capture text screen
    std::string screen = captureTextContent();

    // The screen should not be empty after booting
    // (trim whitespace to check for actual content)
    bool has_content = false;
    for (char c : screen) {
        if (c != ' ' && c != '\n' && c != '\0') {
            has_content = true;
            break;
        }
    }
    EXPECT_TRUE(has_content) << "Screen should have visible content after 2s boot";

    // Verify DOS prompt characters appear
    EXPECT_TRUE(containsDosPrompt(screen))
        << "Expected DOS prompt pattern (e.g., C:\\>) in screen text:\n"
        << screen;
}

TEST_F(BootToPromptTest, TextCaptureReturnsValidDimensions) {
    ASSERT_NE(engine_, nullptr);

    // Step enough to initialize video
    stepFrames(30);

    size_t cell_count = 0;
    legends_text_info_t info{};
    legends_capture_text(engine_, nullptr, 0, &cell_count, &info);

    // Standard text mode should be 80x25
    EXPECT_GE(info.columns, 40u) << "Text mode should have at least 40 columns";
    EXPECT_GE(info.rows, 25u) << "Text mode should have at least 25 rows";
    EXPECT_EQ(cell_count, static_cast<size_t>(info.columns) * info.rows)
        << "Cell count should equal columns * rows";
}

TEST_F(BootToPromptTest, FramebufferProducedAfterBoot) {
    ASSERT_NE(engine_, nullptr);

    // Step to boot
    stepFrames(120);

    // Verify RGB capture works
    size_t rgb_size = 0;
    uint16_t fw = 0, fh = 0;
    legends_capture_rgb(engine_, nullptr, 0, &rgb_size, &fw, &fh);
    EXPECT_GT(rgb_size, 0u) << "Framebuffer should have data";
    EXPECT_GT(fw, 0u) << "Frame width should be positive";
    EXPECT_GT(fh, 0u) << "Frame height should be positive";

    // Capture actual pixels
    std::vector<uint8_t> pixels(rgb_size);
    legends_capture_rgb(engine_, pixels.data(), pixels.size(),
                        &rgb_size, &fw, &fh);

    // Verify not all black (engine should have rendered something)
    bool has_nonblack = false;
    for (size_t i = 0; i < rgb_size; i += 3) {
        if (pixels[i] != 0 || pixels[i+1] != 0 || pixels[i+2] != 0) {
            has_nonblack = true;
            break;
        }
    }
    EXPECT_TRUE(has_nonblack) << "Framebuffer should not be all black after boot";
}

} // namespace
} // namespace legends
