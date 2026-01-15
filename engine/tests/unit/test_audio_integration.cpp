/**
 * @file test_audio_integration.cpp
 * @brief Unit tests for platform audio integration (PR #20).
 *
 * Tests:
 * - Headless stub audio provider integration
 * - DOSBoxContext audio provider configuration
 * - BufferAudio through context
 * - Custom audio provider injection
 * - Audio sample pushing and buffering
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/platform/audio.h"
#include "dosbox/platform/headless.h"
#include "aibox/headless_stub.h"
#include <vector>

using namespace dosbox;
using namespace dosbox::platform;

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Stub Audio Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessAudioTest, DefaultNoProvider) {
    // Clear any existing provider
    aibox::headless::SetAudioProvider(nullptr);

    EXPECT_FALSE(aibox::headless::HasAudioProvider());
    EXPECT_EQ(aibox::headless::GetAudioProvider(), nullptr);
}

TEST(HeadlessAudioTest, SetAudioProvider) {
    BufferAudio audio;
    audio.open({44100, 2, 1024});

    aibox::headless::SetAudioProvider(&audio);

    EXPECT_TRUE(aibox::headless::HasAudioProvider());
    EXPECT_EQ(aibox::headless::GetAudioProvider(), &audio);

    // Clean up
    aibox::headless::SetAudioProvider(nullptr);
}

TEST(HeadlessAudioTest, PushAudioSamplesUsesProvider) {
    BufferAudio audio;
    audio.open({44100, 2, 1024});

    aibox::headless::SetAudioProvider(&audio);

    // Create test samples
    std::vector<int16_t> samples(1024, 0x1234);

    // Push samples through headless stub
    size_t pushed = aibox::headless::PushAudioSamples(samples.data(), samples.size());

    EXPECT_EQ(pushed, samples.size());
    EXPECT_GT(audio.get_queued_samples(), 0u);

    // Clean up
    aibox::headless::SetAudioProvider(nullptr);
}

TEST(HeadlessAudioTest, GetQueuedAudioSamples) {
    BufferAudio audio;
    audio.open({44100, 2, 1024});

    aibox::headless::SetAudioProvider(&audio);

    // Initially empty
    EXPECT_EQ(aibox::headless::GetQueuedAudioSamples(), 0u);

    // Push samples
    std::vector<int16_t> samples(512, 0x5678);
    aibox::headless::PushAudioSamples(samples.data(), samples.size());

    EXPECT_EQ(aibox::headless::GetQueuedAudioSamples(), 512u);

    // Clean up
    aibox::headless::SetAudioProvider(nullptr);
}

TEST(HeadlessAudioTest, ClearAudioBuffer) {
    BufferAudio audio;
    audio.open({44100, 2, 1024});

    aibox::headless::SetAudioProvider(&audio);

    // Push samples
    std::vector<int16_t> samples(256, 0xABCD);
    aibox::headless::PushAudioSamples(samples.data(), samples.size());
    EXPECT_GT(aibox::headless::GetQueuedAudioSamples(), 0u);

    // Clear buffer
    aibox::headless::ClearAudioBuffer();
    EXPECT_EQ(aibox::headless::GetQueuedAudioSamples(), 0u);

    // Clean up
    aibox::headless::SetAudioProvider(nullptr);
}

TEST(HeadlessAudioTest, PauseAudio) {
    BufferAudio audio;
    audio.open({44100, 2, 1024});

    aibox::headless::SetAudioProvider(&audio);

    EXPECT_FALSE(audio.is_paused());

    aibox::headless::PauseAudio(true);
    EXPECT_TRUE(audio.is_paused());

    aibox::headless::PauseAudio(false);
    EXPECT_FALSE(audio.is_paused());

    // Clean up
    aibox::headless::SetAudioProvider(nullptr);
}

TEST(HeadlessAudioTest, PushFailsWithNoProvider) {
    aibox::headless::SetAudioProvider(nullptr);

    std::vector<int16_t> samples(256, 0);
    size_t pushed = aibox::headless::PushAudioSamples(samples.data(), samples.size());

    EXPECT_EQ(pushed, 0u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// DOSBoxContext Audio Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextAudioTest, HasBuiltInBufferAudio) {
    DOSBoxContext ctx;

    // Context has its own buffer audio
    auto& audio = ctx.buffer_audio();

    // Should not be open initially
    EXPECT_FALSE(audio.is_open());
}

TEST(ContextAudioTest, DefaultNoCustomProvider) {
    DOSBoxContext ctx;

    EXPECT_EQ(ctx.get_audio_provider(), nullptr);
}

TEST(ContextAudioTest, SetCustomAudioProvider) {
    DOSBoxContext ctx;
    BufferAudio custom_audio;

    ctx.set_audio_provider(&custom_audio);

    EXPECT_EQ(ctx.get_audio_provider(), &custom_audio);
}

TEST(ContextAudioTest, CurrentContextUsesBuiltInAudio) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Clear any previous state
    aibox::headless::SetAudioProvider(nullptr);

    // Set as current context
    ContextGuard guard(ctx);

    // Should have wired up the built-in buffer audio
    EXPECT_TRUE(aibox::headless::HasAudioProvider());
    EXPECT_EQ(aibox::headless::GetAudioProvider(), &ctx.buffer_audio());
}

TEST(ContextAudioTest, CurrentContextUsesCustomProvider) {
    DOSBoxContext ctx;
    ctx.initialize();
    BufferAudio custom_audio;

    // Set custom provider
    ctx.set_audio_provider(&custom_audio);

    // Set as current context
    ContextGuard guard(ctx);

    // Should use custom provider
    EXPECT_EQ(aibox::headless::GetAudioProvider(), &custom_audio);
}

TEST(ContextAudioTest, ContextSwitchingUpdatesProvider) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Open audio on both contexts
    ctx1.buffer_audio().open({44100, 2, 512});
    ctx2.buffer_audio().open({48000, 2, 1024});

    // Push samples to ctx1
    std::vector<int16_t> samples1(256, 0x1111);
    {
        ContextGuard guard1(ctx1);
        aibox::headless::PushAudioSamples(samples1.data(), samples1.size());
    }

    // Push samples to ctx2
    std::vector<int16_t> samples2(128, 0x2222);
    {
        ContextGuard guard2(ctx2);
        aibox::headless::PushAudioSamples(samples2.data(), samples2.size());
    }

    // Verify each context has its own samples
    EXPECT_EQ(ctx1.buffer_audio().get_queued_samples(), 256u);
    EXPECT_EQ(ctx2.buffer_audio().get_queued_samples(), 128u);
}

TEST(ContextAudioTest, ClearCurrentContextClearsProvider) {
    DOSBoxContext ctx;
    ctx.initialize();

    set_current_context(&ctx);
    EXPECT_TRUE(aibox::headless::HasAudioProvider());

    set_current_context(nullptr);
    EXPECT_FALSE(aibox::headless::HasAudioProvider());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Backend Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessBackendAudioTest, BackendAudioIntegration) {
    auto backend = make_headless_backend();
    DOSBoxContext ctx;
    ctx.initialize();

    // Open backend audio
    backend->audio.open({44100, 2, 1024});

    // Use headless backend audio with context
    ctx.set_audio_provider(&backend->audio);

    ContextGuard guard(ctx);

    // Audio should flow through backend
    std::vector<int16_t> samples(512, 0x3333);
    size_t pushed = aibox::headless::PushAudioSamples(samples.data(), samples.size());

    EXPECT_EQ(pushed, 512u);
    EXPECT_EQ(backend->audio.get_queued_samples(), 512u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Audio Buffer Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(AudioBufferTest, BufferFillRatio) {
    DOSBoxContext ctx;
    ctx.initialize();
    ctx.buffer_audio().open({44100, 2, 1024});

    ContextGuard guard(ctx);

    auto& audio = ctx.buffer_audio();
    size_t capacity = audio.get_buffer_capacity();

    // Initially empty
    EXPECT_FLOAT_EQ(audio.get_buffer_fill_ratio(), 0.0f);

    // Fill half
    std::vector<int16_t> samples(capacity / 2, 0);
    aibox::headless::PushAudioSamples(samples.data(), samples.size());

    float ratio = audio.get_buffer_fill_ratio();
    EXPECT_GT(ratio, 0.0f);
    EXPECT_LT(ratio, 1.0f);
}

TEST(AudioBufferTest, AudioPreservedAcrossContextSwitch) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Open audio
    ctx1.buffer_audio().open({44100, 2, 512});
    ctx2.buffer_audio().open({44100, 2, 512});

    // Push samples to ctx1
    {
        ContextGuard guard1(ctx1);
        std::vector<int16_t> samples(100, 0x4444);
        aibox::headless::PushAudioSamples(samples.data(), samples.size());
    }

    // Push samples to ctx2
    {
        ContextGuard guard2(ctx2);
        std::vector<int16_t> samples(200, 0x5555);
        aibox::headless::PushAudioSamples(samples.data(), samples.size());
    }

    // Verify samples preserved
    EXPECT_EQ(ctx1.buffer_audio().get_queued_samples(), 100u);
    EXPECT_EQ(ctx2.buffer_audio().get_queued_samples(), 200u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// NullAudio Tests (for headless benchmarking)
// ═══════════════════════════════════════════════════════════════════════════════

TEST(NullAudioTest, DiscardsSamples) {
    NullAudio audio;
    audio.open({44100, 2, 1024});

    aibox::headless::SetAudioProvider(&audio);

    // Push samples - should be accepted but discarded
    std::vector<int16_t> samples(1000, 0x6666);
    size_t pushed = aibox::headless::PushAudioSamples(samples.data(), samples.size());

    EXPECT_EQ(pushed, 1000u);
    EXPECT_EQ(audio.total_samples(), 1000u);  // Counted
    EXPECT_EQ(audio.get_queued_samples(), 0u);  // But not buffered

    // Clean up
    aibox::headless::SetAudioProvider(nullptr);
}

TEST(NullAudioTest, UsefulForBenchmarking) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Use NullAudio for fastest possible audio handling
    NullAudio null_audio;
    null_audio.open({44100, 2, 1024});
    ctx.set_audio_provider(&null_audio);

    ContextGuard guard(ctx);

    // Simulate pushing lots of audio
    std::vector<int16_t> samples(4096, 0);
    for (int i = 0; i < 100; ++i) {
        aibox::headless::PushAudioSamples(samples.data(), samples.size());
    }

    EXPECT_EQ(null_audio.total_samples(), 4096u * 100);
}
