/**
 * @file test_shell_h_headless.cpp
 * @brief Compile-time verification that the SDL headless guard logic works.
 *
 * This test validates the headless guard pattern used in shell.h and timer.h.
 * The include chain that broke CI was:
 *   dosbox_library.cpp -> drives.h -> shell.h -> <SDL.h> -> FATAL ERROR
 *
 * We can't include shell.h directly here because it transitively includes
 * dosbox.h which requires the generated config.h. Instead, we replicate the
 * guard logic and verify it produces the correct SDL_STRING definition.
 *
 * The actual SDL firewall is verified by the aibox_core library building
 * successfully with AIBOX_HEADLESS=1 (which includes dosbox_library.cpp
 * that includes shell.h).
 *
 * @copyright GPL-2.0-or-later
 */

// Simulate headless build environment
#ifndef AIBOX_HEADLESS
#define AIBOX_HEADLESS 1
#endif

// Replicate the exact guard logic from shell.h (lines 25-36)
#if defined(C_HEADLESS) || defined(AIBOX_HEADLESS)
  #define SDL_STRING "SDL3"
#else
  // In non-headless mode, this would #include <SDL.h>
  // For this test, we never reach here because AIBOX_HEADLESS is defined.
  #error "Headless guard failed — SDL.h would be included"
#endif

// Verify SDL_STRING is defined (needed for version identification)
static_assert(sizeof(SDL_STRING) > 0, "SDL_STRING must be defined in headless mode");

#include <gtest/gtest.h>
#include <cstring>

namespace {

TEST(ShellHHeadless, SDLStringDefined) {
    // SDL_STRING should be a non-empty string in headless mode
    EXPECT_GT(strlen(SDL_STRING), 0u);
}

TEST(ShellHHeadless, SDLStringIsSDL3InHeadless) {
    // Headless mode should report SDL3 (our target platform)
    EXPECT_STREQ(SDL_STRING, "SDL3");
}

} // namespace
