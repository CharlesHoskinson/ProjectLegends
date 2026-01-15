/**
 * @file test_headless_backend.cpp
 * @brief Unit tests for headless platform backend (PR #16).
 *
 * Tests:
 * - HeadlessDisplay: frame capture, RGBA conversion, palette handling
 * - BufferAudio: ring buffer, RMS calculation, silence detection
 * - ThreadSafeInput: concurrent access, queue operations
 * - HeadlessBackend: factory and integration
 */

#include <gtest/gtest.h>
#include "dosbox/platform/headless.h"
#include <thread>
#include <atomic>

using namespace dosbox::platform;

// ═══════════════════════════════════════════════════════════════════════════════
// HeadlessDisplay Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessDisplayTest, SetMode) {
    HeadlessDisplay display;
    display.set_mode(640, 480, PixelFormat::BGRA8888, false);

    auto info = display.get_frame_info();
    EXPECT_EQ(info.width, 640);
    EXPECT_EQ(info.height, 480);
    EXPECT_EQ(info.format, PixelFormat::BGRA8888);
    EXPECT_EQ(info.pitch, 640 * 4);
}

TEST(HeadlessDisplayTest, UploadAndCapture) {
    HeadlessDisplay display;
    display.set_mode(4, 4, PixelFormat::Indexed8, false);

    // Create a simple 4x4 pattern
    std::vector<uint8_t> pixels(16);
    for (int i = 0; i < 16; ++i) {
        pixels[i] = static_cast<uint8_t>(i * 16);
    }

    FrameInfo info;
    info.width = 4;
    info.height = 4;
    info.format = PixelFormat::Indexed8;
    info.pitch = 4;

    EXPECT_FALSE(display.has_frame());

    display.upload_frame(pixels, info);

    EXPECT_TRUE(display.has_frame());
    EXPECT_EQ(display.frame_count(), 1u);

    auto captured = display.capture_frame();
    ASSERT_EQ(captured.size(), 16u);
    EXPECT_EQ(captured[0], 0);
    EXPECT_EQ(captured[15], 240);
}

TEST(HeadlessDisplayTest, FrameCount) {
    HeadlessDisplay display;
    display.set_mode(8, 8, PixelFormat::Indexed8, false);

    std::vector<uint8_t> pixels(64, 0);
    FrameInfo info{8, 8, PixelFormat::Indexed8, 8, false};

    display.upload_frame(pixels, info);
    display.upload_frame(pixels, info);
    display.upload_frame(pixels, info);

    EXPECT_EQ(display.frame_count(), 3u);
}

TEST(HeadlessDisplayTest, PresentCount) {
    HeadlessDisplay display;
    display.set_mode(8, 8, PixelFormat::Indexed8, false);

    display.present();
    display.present();

    EXPECT_EQ(display.present_count(), 2u);
}

TEST(HeadlessDisplayTest, CaptureDisabled) {
    HeadlessDisplay display;
    display.set_capture_enabled(false);
    display.set_mode(8, 8, PixelFormat::Indexed8, false);

    std::vector<uint8_t> pixels(64, 0xFF);
    FrameInfo info{8, 8, PixelFormat::Indexed8, 8, false};

    display.upload_frame(pixels, info);

    // Frame count should still increment
    EXPECT_EQ(display.frame_count(), 1u);

    // But capture should return empty
    EXPECT_FALSE(display.has_frame());
    EXPECT_TRUE(display.capture_frame().empty());
}

TEST(HeadlessDisplayTest, Palette) {
    HeadlessDisplay display;
    display.set_mode(4, 4, PixelFormat::Indexed8, false);

    // Set a custom palette (first entry = red)
    std::vector<uint8_t> palette(1024, 0);
    palette[0] = 255;  // R
    palette[1] = 0;    // G
    palette[2] = 0;    // B
    palette[3] = 255;  // A

    display.set_palette(palette);

    auto got_palette = display.get_palette();
    ASSERT_EQ(got_palette.size(), 1024u);
    EXPECT_EQ(got_palette[0], 255);  // Red
}

TEST(HeadlessDisplayTest, CaptureFrameRgbaIndexed) {
    HeadlessDisplay display;
    display.set_mode(2, 2, PixelFormat::Indexed8, false);

    // Set palette: index 0 = red, index 1 = green
    std::vector<uint8_t> palette(1024, 0);
    palette[0] = 255; palette[1] = 0; palette[2] = 0; palette[3] = 255;  // Red
    palette[4] = 0; palette[5] = 255; palette[6] = 0; palette[7] = 255;  // Green
    display.set_palette(palette);

    // 2x2 image: index 0, 1, 1, 0
    std::vector<uint8_t> pixels = {0, 1, 1, 0};
    FrameInfo info{2, 2, PixelFormat::Indexed8, 2, false};
    display.upload_frame(pixels, info);

    auto rgba = display.capture_frame_rgba();
    ASSERT_EQ(rgba.size(), 16u);  // 2x2 * 4 bytes

    // First pixel: red
    EXPECT_EQ(rgba[0], 255);  // R
    EXPECT_EQ(rgba[1], 0);    // G
    EXPECT_EQ(rgba[2], 0);    // B
    EXPECT_EQ(rgba[3], 255);  // A

    // Second pixel: green
    EXPECT_EQ(rgba[4], 0);    // R
    EXPECT_EQ(rgba[5], 255);  // G
    EXPECT_EQ(rgba[6], 0);    // B
    EXPECT_EQ(rgba[7], 255);  // A
}

TEST(HeadlessDisplayTest, CaptureFrameRgbaBgra) {
    HeadlessDisplay display;
    display.set_mode(2, 1, PixelFormat::BGRA8888, false);

    // BGRA: Blue=255, Green=128, Red=64, Alpha=255
    std::vector<uint8_t> pixels = {255, 128, 64, 255, 0, 0, 0, 255};
    FrameInfo info{2, 1, PixelFormat::BGRA8888, 8, false};
    display.upload_frame(pixels, info);

    auto rgba = display.capture_frame_rgba();
    ASSERT_EQ(rgba.size(), 8u);

    // First pixel converted from BGRA to RGBA
    EXPECT_EQ(rgba[0], 64);   // R (was B position in BGRA)
    EXPECT_EQ(rgba[1], 128);  // G
    EXPECT_EQ(rgba[2], 255);  // B (was R position in BGRA)
    EXPECT_EQ(rgba[3], 255);  // A
}

TEST(HeadlessDisplayTest, ClearFrame) {
    HeadlessDisplay display;
    display.set_mode(4, 4, PixelFormat::Indexed8, false);

    std::vector<uint8_t> pixels(16, 0xFF);
    FrameInfo info{4, 4, PixelFormat::Indexed8, 4, false};
    display.upload_frame(pixels, info);

    EXPECT_TRUE(display.has_frame());

    display.clear_frame();

    EXPECT_FALSE(display.has_frame());
    EXPECT_TRUE(display.capture_frame().empty());
}

// ═══════════════════════════════════════════════════════════════════════════════
// BufferAudio Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(BufferAudioTest, OpenClose) {
    BufferAudio audio(0.5f);

    EXPECT_FALSE(audio.is_open());

    AudioSpec spec{44100, 2, 1024, AudioFormat::S16};
    EXPECT_TRUE(audio.open(spec));
    EXPECT_TRUE(audio.is_open());

    auto actual = audio.get_spec();
    EXPECT_EQ(actual.sample_rate, 44100u);
    EXPECT_EQ(actual.channels, 2);

    audio.close();
    EXPECT_FALSE(audio.is_open());
}

TEST(BufferAudioTest, PushAndPop) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    std::vector<int16_t> samples = {100, -100, 200, -200, 300, -300};
    size_t pushed = audio.push_samples(samples);
    EXPECT_EQ(pushed, 6u);

    EXPECT_EQ(audio.get_queued_samples(), 6u);

    auto popped = audio.pop_samples(4);
    ASSERT_EQ(popped.size(), 4u);
    EXPECT_EQ(popped[0], 100);
    EXPECT_EQ(popped[1], -100);
    EXPECT_EQ(popped[2], 200);
    EXPECT_EQ(popped[3], -200);

    EXPECT_EQ(audio.get_queued_samples(), 2u);
}

TEST(BufferAudioTest, PeekSamples) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    std::vector<int16_t> samples = {1, 2, 3, 4, 5};
    audio.push_samples(samples);

    auto peeked = audio.peek_samples(3);
    ASSERT_EQ(peeked.size(), 3u);
    EXPECT_EQ(peeked[0], 1);
    EXPECT_EQ(peeked[1], 2);
    EXPECT_EQ(peeked[2], 3);

    // Peek doesn't consume
    EXPECT_EQ(audio.get_queued_samples(), 5u);
}

TEST(BufferAudioTest, RingBufferWrap) {
    BufferAudio audio(0.01f);  // Small buffer for testing
    audio.open({1000, 1, 10, AudioFormat::S16});  // ~10 samples capacity

    // Push near capacity
    std::vector<int16_t> samples1(8, 100);
    audio.push_samples(samples1);
    EXPECT_EQ(audio.get_queued_samples(), 8u);

    // Pop some
    audio.pop_samples(5);
    EXPECT_EQ(audio.get_queued_samples(), 3u);

    // Push more (should wrap around)
    std::vector<int16_t> samples2(5, 200);
    audio.push_samples(samples2);
    EXPECT_EQ(audio.get_queued_samples(), 8u);

    // Verify wraparound worked correctly
    auto all = audio.get_all_samples();
    ASSERT_EQ(all.size(), 8u);
    EXPECT_EQ(all[0], 100);  // Remaining from first push
    EXPECT_EQ(all[1], 100);
    EXPECT_EQ(all[2], 100);
    EXPECT_EQ(all[3], 200);  // From second push
}

TEST(BufferAudioTest, BufferFull) {
    BufferAudio audio(0.001f);  // Very small buffer
    audio.open({1000, 1, 10, AudioFormat::S16});

    size_t capacity = audio.get_buffer_capacity();

    // Fill the buffer
    std::vector<int16_t> samples(capacity + 10, 100);
    size_t pushed = audio.push_samples(samples);

    // Should only push up to capacity
    EXPECT_EQ(pushed, capacity);
    EXPECT_EQ(audio.get_queued_samples(), capacity);
}

TEST(BufferAudioTest, PauseRejectsSamples) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    std::vector<int16_t> samples(100, 0);
    audio.push_samples(samples);
    EXPECT_EQ(audio.get_queued_samples(), 100u);

    audio.pause(true);
    EXPECT_TRUE(audio.is_paused());

    size_t pushed = audio.push_samples(samples);
    EXPECT_EQ(pushed, 0u);
    EXPECT_EQ(audio.get_queued_samples(), 100u);

    audio.pause(false);
    pushed = audio.push_samples(samples);
    EXPECT_EQ(pushed, 100u);
}

TEST(BufferAudioTest, Clear) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    std::vector<int16_t> samples(500, 100);
    audio.push_samples(samples);
    EXPECT_EQ(audio.get_queued_samples(), 500u);

    audio.clear();
    EXPECT_EQ(audio.get_queued_samples(), 0u);
}

TEST(BufferAudioTest, TotalCounters) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    std::vector<int16_t> samples(100, 0);
    audio.push_samples(samples);
    audio.push_samples(samples);

    EXPECT_EQ(audio.total_samples_pushed(), 200u);
    EXPECT_EQ(audio.total_samples_popped(), 0u);

    audio.pop_samples(50);
    EXPECT_EQ(audio.total_samples_popped(), 50u);
}

TEST(BufferAudioTest, CalculateRMS) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    // Push silence
    std::vector<int16_t> silence(100, 0);
    audio.push_samples(silence);
    EXPECT_FLOAT_EQ(audio.calculate_rms(), 0.0f);

    audio.clear();

    // Push max amplitude square wave
    std::vector<int16_t> loud(100);
    for (size_t i = 0; i < 100; ++i) {
        loud[i] = (i % 2 == 0) ? 32767 : -32767;
    }
    audio.push_samples(loud);

    float rms = audio.calculate_rms();
    EXPECT_GT(rms, 0.9f);  // Should be close to 1.0
}

TEST(BufferAudioTest, IsSilent) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    // Silence
    std::vector<int16_t> silence(100, 0);
    audio.push_samples(silence);
    EXPECT_TRUE(audio.is_silent());

    audio.clear();

    // Very quiet (should still be silent)
    std::vector<int16_t> quiet(100, 10);
    audio.push_samples(quiet);
    EXPECT_TRUE(audio.is_silent(0.01f));

    audio.clear();

    // Loud
    std::vector<int16_t> loud(100, 16000);
    audio.push_samples(loud);
    EXPECT_FALSE(audio.is_silent());
}

TEST(BufferAudioTest, PushFloat) {
    BufferAudio audio(1.0f);
    audio.open({44100, 2, 1024, AudioFormat::S16});

    std::vector<float> samples = {0.5f, -0.5f, 1.0f, -1.0f};
    size_t pushed = audio.push_samples_float(samples);
    EXPECT_EQ(pushed, 4u);

    auto popped = audio.pop_samples(4);
    ASSERT_EQ(popped.size(), 4u);

    // Check conversion
    EXPECT_NEAR(popped[0], 16383, 1);   // 0.5 * 32767
    EXPECT_NEAR(popped[1], -16383, 1);  // -0.5 * 32767
    EXPECT_EQ(popped[2], 32767);        // 1.0 (clamped)
    EXPECT_EQ(popped[3], -32767);       // -1.0 (clamped)
}

// ═══════════════════════════════════════════════════════════════════════════════
// ThreadSafeInput Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ThreadSafeInputTest, PushAndPoll) {
    ThreadSafeInput input;

    input.push_key(KeyCode::A, true);
    EXPECT_TRUE(input.has_events());
    EXPECT_EQ(input.queue_size(), 1u);

    auto event = input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->type, InputEventType::KeyDown);
    EXPECT_EQ(event->key.code, KeyCode::A);

    EXPECT_FALSE(input.has_events());
}

TEST(ThreadSafeInputTest, Clear) {
    ThreadSafeInput input;

    input.push_key(KeyCode::W, true);
    input.push_key(KeyCode::A, true);
    input.push_key(KeyCode::S, true);
    EXPECT_EQ(input.queue_size(), 3u);

    input.clear();
    EXPECT_EQ(input.queue_size(), 0u);
    EXPECT_FALSE(input.has_events());
}

TEST(ThreadSafeInputTest, MouseCapture) {
    ThreadSafeInput input;

    EXPECT_FALSE(input.is_mouse_captured());
    input.set_mouse_captured(true);
    EXPECT_TRUE(input.is_mouse_captured());
}

TEST(ThreadSafeInputTest, Modifiers) {
    ThreadSafeInput input;

    EXPECT_EQ(input.get_modifiers(), KeyMod::None);
    input.set_modifiers(KeyMod::LeftShift | KeyMod::LeftCtrl);
    EXPECT_TRUE(has_mod(input.get_modifiers(), KeyMod::LeftShift));
    EXPECT_TRUE(has_mod(input.get_modifiers(), KeyMod::LeftCtrl));
}

TEST(ThreadSafeInputTest, ConcurrentAccess) {
    ThreadSafeInput input;
    std::atomic<int> push_count{0};
    std::atomic<int> poll_count{0};

    // Producer thread
    std::thread producer([&]() {
        for (int i = 0; i < 1000; ++i) {
            input.push_key(KeyCode::A, true);
            push_count.fetch_add(1);
        }
    });

    // Consumer thread
    std::thread consumer([&]() {
        while (poll_count.load() < 1000) {
            if (auto event = input.poll_event()) {
                poll_count.fetch_add(1);
            } else {
                std::this_thread::yield();
            }
        }
    });

    producer.join();
    consumer.join();

    EXPECT_EQ(push_count.load(), 1000);
    EXPECT_EQ(poll_count.load(), 1000);
    EXPECT_EQ(input.queue_size(), 0u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// HeadlessBackend Factory Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessBackendTest, Create) {
    auto backend = make_headless_backend();

    EXPECT_NE(backend, nullptr);

    auto platform = backend->as_platform_backend();
    EXPECT_TRUE(platform.is_valid());
    EXPECT_NE(platform.display, nullptr);
    EXPECT_NE(platform.audio, nullptr);
    EXPECT_NE(platform.input, nullptr);
    EXPECT_NE(platform.timing, nullptr);
}

TEST(HeadlessBackendTest, Reset) {
    auto backend = make_headless_backend();

    // Use the backend
    backend->display.set_mode(320, 200, PixelFormat::Indexed8, false);
    std::vector<uint8_t> pixels(320 * 200, 0);
    FrameInfo info{320, 200, PixelFormat::Indexed8, 320, false};
    backend->display.upload_frame(pixels, info);

    backend->audio.open({44100, 2, 1024, AudioFormat::S16});
    std::vector<int16_t> samples(100, 0);
    backend->audio.push_samples(samples);

    backend->input.push_key(KeyCode::Space, true);

    backend->timing.advance_time(100);

    // Reset
    backend->reset();

    EXPECT_FALSE(backend->display.has_frame());
    EXPECT_EQ(backend->audio.get_queued_samples(), 0u);
    EXPECT_FALSE(backend->input.has_events());
    EXPECT_EQ(backend->timing.get_ticks(), 0u);
}

TEST(HeadlessBackendTest, DeterministicTiming) {
    auto backend = make_headless_backend();

    EXPECT_TRUE(backend->timing.is_deterministic());

    backend->timing.advance_time(50);
    EXPECT_EQ(backend->timing.get_ticks(), 50u);

    // Delay should be no-op
    backend->timing.delay(1000);
    EXPECT_EQ(backend->timing.get_ticks(), 50u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Integration Test: Full Frame Loop
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessIntegrationTest, FullFrameLoop) {
    auto backend = make_headless_backend();

    // Configure display
    backend->display.set_mode(320, 200, PixelFormat::Indexed8, false);

    // Set a simple palette
    std::vector<uint8_t> palette(1024, 0);
    for (int i = 0; i < 256; ++i) {
        palette[i * 4 + 0] = static_cast<uint8_t>(i);
        palette[i * 4 + 1] = static_cast<uint8_t>(255 - i);
        palette[i * 4 + 2] = static_cast<uint8_t>(i / 2);
        palette[i * 4 + 3] = 255;
    }
    backend->display.set_palette(palette);

    // Open audio
    backend->audio.open({44100, 2, 1024, AudioFormat::S16});

    // Simulate 60 frames at 60fps
    for (int frame = 0; frame < 60; ++frame) {
        // Inject input
        if (frame == 30) {
            backend->input.push_key(KeyCode::Space, true);
        }
        if (frame == 35) {
            backend->input.push_key(KeyCode::Space, false);
        }

        // Process input
        while (auto event = backend->input.poll_event()) {
            // Handle event (no-op for test)
            (void)event;
        }

        // Generate frame (gradient)
        std::vector<uint8_t> pixels(320 * 200);
        for (int y = 0; y < 200; ++y) {
            for (int x = 0; x < 320; ++x) {
                pixels[y * 320 + x] = static_cast<uint8_t>((x + frame) % 256);
            }
        }
        FrameInfo info{320, 200, PixelFormat::Indexed8, 320, false};
        backend->display.upload_frame(pixels, info);
        backend->display.present();

        // Generate audio (simple tone)
        std::vector<int16_t> audio_samples(1470);  // ~1/30th second at 44100Hz stereo
        for (size_t i = 0; i < audio_samples.size(); i += 2) {
            int16_t sample = static_cast<int16_t>(10000 * std::sin(i * 0.1));
            audio_samples[i] = sample;      // Left
            audio_samples[i + 1] = sample;  // Right
        }
        backend->audio.push_samples(audio_samples);

        // Advance time (16.67ms per frame)
        backend->timing.advance_time_us(16667);
    }

    // Verify results
    EXPECT_EQ(backend->display.frame_count(), 60u);
    EXPECT_EQ(backend->display.present_count(), 60u);
    EXPECT_GT(backend->audio.total_samples_pushed(), 0u);
    EXPECT_GE(backend->timing.get_ticks(), 999u);  // ~1 second

    // Capture final frame as RGBA
    auto rgba = backend->display.capture_frame_rgba();
    EXPECT_EQ(rgba.size(), 320u * 200u * 4u);

    // Verify audio is not silent
    EXPECT_FALSE(backend->audio.is_silent());
}
