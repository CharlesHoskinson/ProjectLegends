#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>

class ConfigDeepCopyTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
    }
    void TearDown() override { pal::Platform::shutdown(); }
};

TEST_F(ConfigDeepCopyTest, ConfigPathSurvivesStackDestruction) {
    legends_handle handle = nullptr;
    {
        char path[64];
        std::strcpy(path, "/tmp/test_legends.conf");
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.config_path = path;
        auto err = legends_create(&cfg, &handle);
        ASSERT_EQ(err, LEGENDS_OK);
        // Overwrite stack buffer to prove we don't hold a dangling pointer
        std::memset(path, 'X', sizeof(path));
    }
    // Instance should still be valid after source buffer is destroyed
    legends_step_result_t result;
    auto err = legends_step_cycles(handle, 100, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    legends_destroy(handle);
}

TEST_F(ConfigDeepCopyTest, NullConfigPathIsHandled) {
    legends_handle handle = nullptr;
    legends_config_t cfg = LEGENDS_CONFIG_INIT;
    cfg.config_path = nullptr;
    auto err = legends_create(&cfg, &handle);
    ASSERT_EQ(err, LEGENDS_OK);
    legends_destroy(handle);
}
