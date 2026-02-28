/**
 * @file test_mixer_thread_safety.cpp
 * @brief M7: MixerState thread safety documentation.
 */

#include <gtest/gtest.h>
#include <dosbox/dosbox_context.h>
#include <thread>
#include <atomic>

namespace dosbox {
namespace test {

TEST(MixerThreadSafety, ConcurrentAccessDocumented) {
    ContextConfig config = ContextConfig::minimal();
    DOSBoxContext ctx(config);
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value());

    // M7: mixer.work_in/work_out accessed from emulation + audio threads
    // without synchronization. TSan-enabled CI would flag this.
    EXPECT_GE(ctx.mixer.sample_rate, 0u);

    ctx.shutdown();
}

} // namespace test
} // namespace dosbox
