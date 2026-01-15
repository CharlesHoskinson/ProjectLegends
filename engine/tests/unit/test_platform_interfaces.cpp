/**
 * @file test_platform_interfaces.cpp
 * @brief Unit tests for DOSBox platform abstraction interfaces (PR #15).
 *
 * Tests:
 * - Display interface (NullDisplay)
 * - Audio interface (NullAudio)
 * - Input interface (QueueInput)
 * - Timing interface (VirtualTiming, HostTiming)
 * - Platform backend convenience functions
 */

#include <gtest/gtest.h>
#include "dosbox/platform/platform.h"

using namespace dosbox::platform;

// ═══════════════════════════════════════════════════════════════════════════════
// PixelFormat Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(PixelFormatTest, BytesPerPixel) {
    EXPECT_EQ(bytes_per_pixel(PixelFormat::Indexed8), 1u);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::RGB565), 2u);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::RGB888), 3u);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::BGRA8888), 4u);
    EXPECT_EQ(bytes_per_pixel(PixelFormat::RGBA8888), 4u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// FrameInfo Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(FrameInfoTest, MinPitch) {
    FrameInfo info;
    info.width = 640;
    info.format = PixelFormat::Indexed8;
    EXPECT_EQ(info.min_pitch(), 640);

    info.format = PixelFormat::RGB565;
    EXPECT_EQ(info.min_pitch(), 1280);

    info.format = PixelFormat::RGB888;
    EXPECT_EQ(info.min_pitch(), 1920);

    info.format = PixelFormat::BGRA8888;
    EXPECT_EQ(info.min_pitch(), 2560);
}

TEST(FrameInfoTest, FrameSize) {
    FrameInfo info;
    info.width = 640;
    info.height = 480;
    info.format = PixelFormat::Indexed8;
    info.pitch = 640;
    EXPECT_EQ(info.frame_size(), 640u * 480u);

    info.pitch = 1024;  // With padding
    EXPECT_EQ(info.frame_size(), 1024u * 480u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// NullDisplay Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(NullDisplayTest, SetMode) {
    NullDisplay display;
    display.set_mode(800, 600, PixelFormat::BGRA8888, false);

    auto info = display.get_frame_info();
    EXPECT_EQ(info.width, 800);
    EXPECT_EQ(info.height, 600);
    EXPECT_EQ(info.format, PixelFormat::BGRA8888);
    EXPECT_EQ(info.pitch, 800 * 4);
}

TEST(NullDisplayTest, UploadFrame) {
    NullDisplay display;
    display.set_mode(320, 200, PixelFormat::Indexed8, false);

    std::vector<uint8_t> pixels(320 * 200, 0);
    FrameInfo info;
    info.width = 320;
    info.height = 200;
    info.format = PixelFormat::Indexed8;
    info.pitch = 320;

    display.upload_frame(pixels, info);
    display.upload_frame(pixels, info);
    display.upload_frame(pixels, info);

    EXPECT_EQ(display.frame_count(), 3u);
}

TEST(NullDisplayTest, Present) {
    NullDisplay display;
    display.set_mode(640, 480, PixelFormat::Indexed8, false);

    // Present is a no-op for NullDisplay
    display.present();
    display.present();
    // Should not crash
}

TEST(NullDisplayTest, HardwareNotSupported) {
    NullDisplay display;
    EXPECT_FALSE(display.supports_hardware_present());
    EXPECT_EQ(display.lock_texture(nullptr), nullptr);
}

TEST(NullDisplayTest, CaptureNotSupported) {
    NullDisplay display;
    EXPECT_FALSE(display.has_frame());
    EXPECT_TRUE(display.capture_frame().empty());
}

// ═══════════════════════════════════════════════════════════════════════════════
// AudioSpec Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(AudioSpecTest, Defaults) {
    AudioSpec spec;
    EXPECT_EQ(spec.sample_rate, 44100u);
    EXPECT_EQ(spec.channels, 2);
    EXPECT_EQ(spec.samples, 1024);
    EXPECT_EQ(spec.format, AudioFormat::S16);
}

TEST(AudioSpecTest, BytesPerSample) {
    AudioSpec spec;
    spec.format = AudioFormat::S16;
    EXPECT_EQ(spec.bytes_per_sample(), 2u);

    spec.format = AudioFormat::F32;
    EXPECT_EQ(spec.bytes_per_sample(), 4u);
}

TEST(AudioSpecTest, BufferSizeBytes) {
    AudioSpec spec;
    spec.sample_rate = 44100;
    spec.channels = 2;
    spec.samples = 1024;
    spec.format = AudioFormat::S16;

    // 1024 samples * 2 channels * 2 bytes = 4096 bytes
    EXPECT_EQ(spec.buffer_size_bytes(), 4096u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// NullAudio Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(NullAudioTest, OpenClose) {
    NullAudio audio;
    EXPECT_FALSE(audio.is_open());

    AudioSpec spec;
    EXPECT_TRUE(audio.open(spec));
    EXPECT_TRUE(audio.is_open());

    auto actual = audio.get_spec();
    EXPECT_EQ(actual.sample_rate, spec.sample_rate);
    EXPECT_EQ(actual.channels, spec.channels);

    audio.close();
    EXPECT_FALSE(audio.is_open());
}

TEST(NullAudioTest, PushSamples) {
    NullAudio audio;
    AudioSpec spec;
    audio.open(spec);

    std::vector<int16_t> samples(1024, 0);
    size_t pushed = audio.push_samples(samples);
    EXPECT_EQ(pushed, 1024u);

    pushed = audio.push_samples(samples);
    EXPECT_EQ(pushed, 1024u);

    EXPECT_EQ(audio.total_samples(), 2048u);
}

TEST(NullAudioTest, PushWhilePaused) {
    NullAudio audio;
    audio.open(AudioSpec{});

    std::vector<int16_t> samples(512, 0);
    audio.push_samples(samples);
    EXPECT_EQ(audio.total_samples(), 512u);

    audio.pause(true);
    EXPECT_TRUE(audio.is_paused());

    size_t pushed = audio.push_samples(samples);
    EXPECT_EQ(pushed, 0u);  // Rejected while paused
    EXPECT_EQ(audio.total_samples(), 512u);

    audio.pause(false);
    pushed = audio.push_samples(samples);
    EXPECT_EQ(pushed, 512u);
    EXPECT_EQ(audio.total_samples(), 1024u);
}

TEST(NullAudioTest, BufferState) {
    NullAudio audio;
    audio.open(AudioSpec{});

    EXPECT_EQ(audio.get_queued_samples(), 0u);  // Always empty
    EXPECT_GT(audio.get_buffer_capacity(), 0u);
    EXPECT_FLOAT_EQ(audio.get_buffer_fill_ratio(), 0.0f);
}

// ═══════════════════════════════════════════════════════════════════════════════
// KeyCode and KeyMod Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(KeyModTest, BitwiseOr) {
    KeyMod mods = KeyMod::LeftShift | KeyMod::LeftCtrl;
    EXPECT_TRUE(has_mod(mods, KeyMod::LeftShift));
    EXPECT_TRUE(has_mod(mods, KeyMod::LeftCtrl));
    EXPECT_FALSE(has_mod(mods, KeyMod::LeftAlt));
}

TEST(KeyModTest, BitwiseAnd) {
    KeyMod mods = KeyMod::LeftShift | KeyMod::RightShift;
    EXPECT_TRUE(has_mod(mods, KeyMod::Shift));
    EXPECT_FALSE(has_mod(mods, KeyMod::Ctrl));
}

// ═══════════════════════════════════════════════════════════════════════════════
// InputEvent Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(InputEventTest, KeyDown) {
    auto event = InputEvent::key_down(KeyCode::A, KeyMod::LeftShift);
    EXPECT_EQ(event.type, InputEventType::KeyDown);
    EXPECT_EQ(event.key.code, KeyCode::A);
    EXPECT_EQ(event.key.mods, KeyMod::LeftShift);
    EXPECT_FALSE(event.key.repeat);
}

TEST(InputEventTest, KeyUp) {
    auto event = InputEvent::key_up(KeyCode::Escape);
    EXPECT_EQ(event.type, InputEventType::KeyUp);
    EXPECT_EQ(event.key.code, KeyCode::Escape);
}

TEST(InputEventTest, MouseMotion) {
    auto event = InputEvent::motion(10, -5);
    EXPECT_EQ(event.type, InputEventType::MouseMotion);
    EXPECT_EQ(event.mouse_motion.dx, 10);
    EXPECT_EQ(event.mouse_motion.dy, -5);
}

TEST(InputEventTest, MouseButton) {
    auto down = InputEvent::button_down(MouseButton::Left, 100, 200);
    EXPECT_EQ(down.type, InputEventType::MouseButtonDown);
    EXPECT_EQ(down.mouse_button.button, MouseButton::Left);
    EXPECT_EQ(down.mouse_button.x, 100);
    EXPECT_EQ(down.mouse_button.y, 200);

    auto up = InputEvent::button_up(MouseButton::Right);
    EXPECT_EQ(up.type, InputEventType::MouseButtonUp);
    EXPECT_EQ(up.mouse_button.button, MouseButton::Right);
}

TEST(InputEventTest, MouseWheel) {
    auto event = InputEvent::wheel(0, -3);
    EXPECT_EQ(event.type, InputEventType::MouseWheel);
    EXPECT_EQ(event.mouse_wheel.dx, 0);
    EXPECT_EQ(event.mouse_wheel.dy, -3);
}

// ═══════════════════════════════════════════════════════════════════════════════
// QueueInput Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(QueueInputTest, PushAndPoll) {
    QueueInput input;

    EXPECT_FALSE(input.has_events());

    input.push_key(KeyCode::A, true);
    EXPECT_TRUE(input.has_events());
    EXPECT_EQ(input.queue_size(), 1u);

    auto event = input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->type, InputEventType::KeyDown);
    EXPECT_EQ(event->key.code, KeyCode::A);

    EXPECT_FALSE(input.has_events());
}

TEST(QueueInputTest, MultipleEvents) {
    QueueInput input;

    input.push_key(KeyCode::W, true);
    input.push_mouse_motion(5, -3);
    input.push_mouse_button(MouseButton::Left, true);
    input.push_key(KeyCode::W, false);

    EXPECT_EQ(input.queue_size(), 4u);

    auto e1 = input.poll_event();
    ASSERT_TRUE(e1.has_value());
    EXPECT_EQ(e1->type, InputEventType::KeyDown);

    auto e2 = input.poll_event();
    ASSERT_TRUE(e2.has_value());
    EXPECT_EQ(e2->type, InputEventType::MouseMotion);

    auto e3 = input.poll_event();
    ASSERT_TRUE(e3.has_value());
    EXPECT_EQ(e3->type, InputEventType::MouseButtonDown);

    auto e4 = input.poll_event();
    ASSERT_TRUE(e4.has_value());
    EXPECT_EQ(e4->type, InputEventType::KeyUp);

    auto e5 = input.poll_event();
    EXPECT_FALSE(e5.has_value());
}

TEST(QueueInputTest, Clear) {
    QueueInput input;

    input.push_key(KeyCode::Space, true);
    input.push_key(KeyCode::Space, false);
    EXPECT_EQ(input.queue_size(), 2u);

    input.clear();
    EXPECT_FALSE(input.has_events());
    EXPECT_EQ(input.queue_size(), 0u);
}

TEST(QueueInputTest, MouseCapture) {
    QueueInput input;

    EXPECT_FALSE(input.is_mouse_captured());

    input.set_mouse_captured(true);
    EXPECT_TRUE(input.is_mouse_captured());

    input.set_mouse_captured(false);
    EXPECT_FALSE(input.is_mouse_captured());
}

TEST(QueueInputTest, Modifiers) {
    QueueInput input;

    EXPECT_EQ(input.get_modifiers(), KeyMod::None);

    input.set_modifiers(KeyMod::LeftShift | KeyMod::LeftCtrl);
    EXPECT_TRUE(has_mod(input.get_modifiers(), KeyMod::LeftShift));
    EXPECT_TRUE(has_mod(input.get_modifiers(), KeyMod::LeftCtrl));
}

// ═══════════════════════════════════════════════════════════════════════════════
// VirtualTiming Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(VirtualTimingTest, InitialState) {
    VirtualTiming timing;

    EXPECT_EQ(timing.get_ticks(), 0u);
    EXPECT_EQ(timing.get_ticks_us(), 0u);
    EXPECT_TRUE(timing.is_deterministic());
}

TEST(VirtualTimingTest, AdvanceTime) {
    VirtualTiming timing;

    timing.advance_time(100);  // 100ms
    EXPECT_EQ(timing.get_ticks(), 100u);
    EXPECT_EQ(timing.get_ticks_us(), 100000u);

    timing.advance_time(50);
    EXPECT_EQ(timing.get_ticks(), 150u);
}

TEST(VirtualTimingTest, AdvanceTimeUs) {
    VirtualTiming timing;

    timing.advance_time_us(1500);  // 1.5ms
    EXPECT_EQ(timing.get_ticks_us(), 1500u);
    EXPECT_EQ(timing.get_ticks(), 1u);  // Truncated to ms

    timing.advance_time_us(500);
    EXPECT_EQ(timing.get_ticks_us(), 2000u);
    EXPECT_EQ(timing.get_ticks(), 2u);
}

TEST(VirtualTimingTest, DelayIsNoop) {
    VirtualTiming timing;

    timing.advance_time(100);
    timing.delay(1000);  // Should not advance time
    EXPECT_EQ(timing.get_ticks(), 100u);

    timing.delay_us(500000);
    EXPECT_EQ(timing.get_ticks(), 100u);
}

TEST(VirtualTimingTest, Reset) {
    VirtualTiming timing;

    timing.advance_time(500);
    EXPECT_EQ(timing.get_ticks(), 500u);

    timing.reset();
    EXPECT_EQ(timing.get_ticks(), 0u);
}

TEST(VirtualTimingTest, SetTicks) {
    VirtualTiming timing;

    timing.set_ticks_us(123456789);
    EXPECT_EQ(timing.get_ticks_us(), 123456789u);
    EXPECT_EQ(timing.get_ticks(), 123456u);
}

TEST(VirtualTimingTest, PerformanceCounter) {
    VirtualTiming timing;

    EXPECT_EQ(timing.get_performance_frequency(), 1000000u);  // Microseconds

    timing.advance_time_us(5000);
    EXPECT_EQ(timing.get_performance_counter(), 5000u);

    uint64_t us = timing.counter_to_us(1000);
    EXPECT_EQ(us, 1000u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// HostTiming Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HostTimingTest, NotDeterministic) {
    HostTiming timing;
    EXPECT_FALSE(timing.is_deterministic());
}

TEST(HostTimingTest, TicksIncrement) {
    HostTiming timing;

    uint32_t t1 = timing.get_ticks();
    // Small delay to ensure time passes
    std::this_thread::sleep_for(std::chrono::milliseconds(10));
    uint32_t t2 = timing.get_ticks();

    EXPECT_GE(t2, t1);  // Time should not go backwards
}

TEST(HostTimingTest, PerformanceCounter) {
    HostTiming timing;

    uint64_t freq = timing.get_performance_frequency();
    EXPECT_GT(freq, 0u);

    uint64_t c1 = timing.get_performance_counter();
    std::this_thread::sleep_for(std::chrono::milliseconds(1));
    uint64_t c2 = timing.get_performance_counter();

    EXPECT_GT(c2, c1);
}

TEST(HostTimingTest, CounterToTime) {
    HostTiming timing;

    uint64_t freq = timing.get_performance_frequency();
    uint64_t delta = freq;  // 1 second worth of ticks

    uint64_t us = timing.counter_to_us(delta);
    // Should be approximately 1 second (1,000,000 us)
    // Allow some tolerance due to precision
    EXPECT_NEAR(us, 1000000u, 1000u);  // Within 1ms
}

// ═══════════════════════════════════════════════════════════════════════════════
// Platform Backend Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(PlatformBackendTest, Validity) {
    PlatformBackend backend;
    EXPECT_FALSE(backend.is_valid());

    NullDisplay display;
    VirtualTiming timing;

    backend.display = &display;
    EXPECT_FALSE(backend.is_valid());  // Still needs timing

    backend.timing = &timing;
    EXPECT_TRUE(backend.is_valid());
}

TEST(PlatformBackendTest, HeadlessBackend) {
    auto backend = create_headless_backend();

    EXPECT_TRUE(backend.is_valid());
    EXPECT_NE(backend.display, nullptr);
    EXPECT_NE(backend.audio, nullptr);
    EXPECT_NE(backend.input, nullptr);
    EXPECT_NE(backend.timing, nullptr);

    // Should be deterministic
    EXPECT_TRUE(backend.timing->is_deterministic());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Integration Test: Simulated Frame Loop
// ═══════════════════════════════════════════════════════════════════════════════

TEST(IntegrationTest, SimulatedFrameLoop) {
    auto backend = create_headless_backend();

    // Configure display
    backend.display->set_mode(320, 200, PixelFormat::Indexed8, false);

    // Simulate 3 frames
    std::vector<uint8_t> pixels(320 * 200, 0);
    FrameInfo info;
    info.width = 320;
    info.height = 200;
    info.format = PixelFormat::Indexed8;
    info.pitch = 320;

    for (int frame = 0; frame < 3; ++frame) {
        // Inject some input
        backend.input->push_key(KeyCode::Space, true);
        backend.input->push_key(KeyCode::Space, false);

        // Process input
        while (auto event = backend.input->poll_event()) {
            // Handle event (no-op for test)
            (void)event;
        }

        // Generate audio (stereo, 1024 samples)
        std::vector<int16_t> audio_samples(2048, 0);
        static_cast<NullAudio*>(backend.audio)->push_samples(audio_samples);

        // Render frame
        backend.display->upload_frame(pixels, info);
        backend.display->present();

        // Advance time (16.67ms per frame @ 60fps)
        backend.timing->advance_time_us(16667);
    }

    // Verify timing advanced correctly
    EXPECT_GE(backend.timing->get_ticks(), 49u);  // ~50ms for 3 frames
}
