// SPDX-License-Identifier: MIT
//
// Tests for proxy API functions. These test the error mapping and
// not-connected behavior. Full E2E testing is in integration tests.

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <legends_ipc/ipc_error.h>

// Test that proxy functions return appropriate errors when not connected.
// These tests are meaningful when built with LEGENDS_USE_IPC=ON.
// When built without IPC, they test the monolithic path instead.

#ifdef LEGENDS_USE_IPC

TEST(ProxyApiTest, GetApiVersionWhenNotConnected) {
    uint32_t major, minor, patch;
    auto err = legends_get_api_version(&major, &minor, &patch);
    EXPECT_EQ(err, LEGENDS_ERR_NOT_INITIALIZED);
}

TEST(ProxyApiTest, CreateWhenNotConnected) {
    legends_handle h;
    auto err = legends_create(nullptr, &h);
    EXPECT_EQ(err, LEGENDS_ERR_NOT_INITIALIZED);
}

TEST(ProxyApiTest, StepMsWhenNotConnected) {
    auto err = legends_step_ms(nullptr, 100, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NOT_INITIALIZED);
}

TEST(ProxyApiTest, KeyEventWhenNotConnected) {
    auto err = legends_key_event(nullptr, 0x1C, 1);
    EXPECT_EQ(err, LEGENDS_ERR_NOT_INITIALIZED);
}

TEST(ProxyApiTest, MouseEventWhenNotConnected) {
    auto err = legends_mouse_event(nullptr, 10, 20, 0);
    EXPECT_EQ(err, LEGENDS_ERR_NOT_INITIALIZED);
}

TEST(ProxyApiTest, CaptureAudioWhenNotConnected) {
    size_t count;
    auto err = legends_capture_audio(nullptr, nullptr, 0, &count);
    EXPECT_EQ(err, LEGENDS_ERR_NOT_INITIALIZED);
}

TEST(ProxyApiTest, UnsupportedFunctionsReturnNotSupported) {
    EXPECT_EQ(legends_text_input(nullptr, "hello"), LEGENDS_ERR_NOT_SUPPORTED);
    EXPECT_EQ(legends_start_video_capture(nullptr, "test.avi"), LEGENDS_ERR_NOT_SUPPORTED);
    EXPECT_EQ(legends_joystick_event(nullptr, 0, 128, 128, 0), LEGENDS_ERR_NOT_SUPPORTED);
}

#endif // LEGENDS_USE_IPC
