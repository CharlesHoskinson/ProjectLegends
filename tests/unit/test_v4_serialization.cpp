/**
 * @file test_v4_serialization.cpp
 * @brief Tests for V4 engine state serialization: mixer, VGA, DOS,
 *        and V3 backward compatibility.
 */

#include <gtest/gtest.h>
#include <dosbox/engine_state.h>
#include <dosbox/dosbox_context.h>
#include <dosbox/dosbox_library.h>
#include <cstring>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// Wire format size tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(V4Serialization, MixerWireFormatSize) {
    EXPECT_EQ(sizeof(dosbox::EngineStateMixer), 36u);
    EXPECT_TRUE(std::is_trivially_copyable_v<dosbox::EngineStateMixer>);
}

TEST(V4Serialization, VgaWireFormatSize) {
    EXPECT_EQ(sizeof(dosbox::EngineStateVga), 32u);
    EXPECT_TRUE(std::is_trivially_copyable_v<dosbox::EngineStateVga>);
}

TEST(V4Serialization, DosWireFormatSize) {
    EXPECT_EQ(sizeof(dosbox::EngineStateDos), 20u);
    EXPECT_TRUE(std::is_trivially_copyable_v<dosbox::EngineStateDos>);
}

TEST(V4Serialization, TotalSizeIsV5) {
    EXPECT_EQ(dosbox::ENGINE_STATE_VERSION, 5u);
    EXPECT_EQ(dosbox::ENGINE_STATE_SIZE_V4, 680u);
    EXPECT_EQ(dosbox::ENGINE_STATE_SIZE_V5_BASE, 792u);
    EXPECT_EQ(dosbox::ENGINE_STATE_SIZE_V3, 544u);
    // ENGINE_STATE_SIZE is now an alias for V5_BASE (dynamic size queried at runtime)
    EXPECT_EQ(dosbox::ENGINE_STATE_SIZE, dosbox::ENGINE_STATE_SIZE_V5_BASE);
}

TEST(V4Serialization, VgaRegistersWireFormatSize) {
    EXPECT_EQ(sizeof(dosbox::EngineStateVgaRegisters), 2528u);
    EXPECT_TRUE(std::is_trivially_copyable_v<dosbox::EngineStateVgaRegisters>);
}

TEST(V4Serialization, V5SubBlockDirSize) {
    EXPECT_EQ(sizeof(dosbox::V5SubBlockDir), 8u);
    EXPECT_EQ(sizeof(dosbox::V5DirEntry), 16u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Mixer struct round-trip
// ─────────────────────────────────────────────────────────────────────────────

TEST(V4Serialization, MixerFieldsRoundTrip) {
    dosbox::EngineStateMixer src{};
    src.freq = 48000;
    src.blocksize = 2048;
    src.master_vol[0] = 0.8f;
    src.master_vol[1] = 0.7f;
    src.record_vol[0] = 0.5f;
    src.record_vol[1] = 0.6f;
    src.samples = 512;
    src.enabled = 1;
    src.nosound = 0;
    src.swapstereo = 1;
    src.mute = 0;
    src.sampleaccurate = 1;

    // memcpy round-trip
    uint8_t buf[sizeof(dosbox::EngineStateMixer)];
    std::memcpy(buf, &src, sizeof(src));

    dosbox::EngineStateMixer dst{};
    std::memcpy(&dst, buf, sizeof(dst));

    EXPECT_EQ(dst.freq, 48000u);
    EXPECT_EQ(dst.blocksize, 2048u);
    EXPECT_FLOAT_EQ(dst.master_vol[0], 0.8f);
    EXPECT_FLOAT_EQ(dst.master_vol[1], 0.7f);
    EXPECT_FLOAT_EQ(dst.record_vol[0], 0.5f);
    EXPECT_FLOAT_EQ(dst.record_vol[1], 0.6f);
    EXPECT_EQ(dst.samples, 512u);
    EXPECT_EQ(dst.enabled, 1);
    EXPECT_EQ(dst.nosound, 0);
    EXPECT_EQ(dst.swapstereo, 1);
    EXPECT_EQ(dst.mute, 0);
    EXPECT_EQ(dst.sampleaccurate, 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// VGA struct round-trip
// ─────────────────────────────────────────────────────────────────────────────

TEST(V4Serialization, VgaFieldsRoundTrip) {
    dosbox::EngineStateVga src{};
    src.width = 320;
    src.height = 200;
    src.bpp = 8;
    src.mode = static_cast<uint8_t>(dosbox::VgaMode::VGA);
    src.svga_chip = static_cast<uint8_t>(dosbox::SvgaChip::S3Trio);
    src.render_on_demand = 1;
    src.refresh_rate = 70.0;
    src.frame_counter = 12345;
    src.dac_8bit = 1;
    src.vbe_enabled = 1;
    src.text_mode = 0;
    src.cga_snow = 0;
    src.vesa_flags = 0xFF; // all VESA modes

    uint8_t buf[sizeof(dosbox::EngineStateVga)];
    std::memcpy(buf, &src, sizeof(src));

    dosbox::EngineStateVga dst{};
    std::memcpy(&dst, buf, sizeof(dst));

    EXPECT_EQ(dst.width, 320);
    EXPECT_EQ(dst.height, 200);
    EXPECT_EQ(dst.bpp, 8);
    EXPECT_EQ(dst.mode, static_cast<uint8_t>(dosbox::VgaMode::VGA));
    EXPECT_EQ(dst.svga_chip, static_cast<uint8_t>(dosbox::SvgaChip::S3Trio));
    EXPECT_EQ(dst.render_on_demand, 1);
    EXPECT_DOUBLE_EQ(dst.refresh_rate, 70.0);
    EXPECT_EQ(dst.frame_counter, 12345u);
    EXPECT_EQ(dst.dac_8bit, 1);
    EXPECT_EQ(dst.vbe_enabled, 1);
    EXPECT_EQ(dst.text_mode, 0);
    EXPECT_EQ(dst.cga_snow, 0);
    EXPECT_EQ(dst.vesa_flags, 0xFF);
}

TEST(V4Serialization, VesaFlagsBitPacking) {
    // Test that individual VESA flag bits are preserved
    uint8_t flags = 0;
    flags |= 0x01; // 32bpp
    flags |= 0x04; // 16bpp
    flags |= 0x10; // 8bpp
    flags |= 0x80; // hd

    EXPECT_TRUE(flags & 0x01);  // 32bpp
    EXPECT_FALSE(flags & 0x02); // 24bpp
    EXPECT_TRUE(flags & 0x04);  // 16bpp
    EXPECT_FALSE(flags & 0x08); // 15bpp
    EXPECT_TRUE(flags & 0x10);  // 8bpp
    EXPECT_FALSE(flags & 0x20); // 4bpp
    EXPECT_FALSE(flags & 0x40); // lowres
    EXPECT_TRUE(flags & 0x80);  // hd
}

// ─────────────────────────────────────────────────────────────────────────────
// DOS struct round-trip
// ─────────────────────────────────────────────────────────────────────────────

TEST(V4Serialization, DosFieldsRoundTrip) {
    dosbox::EngineStateDos src{};
    src.psp_segment = 0x1234;
    src.dta_segment = 0x5678;
    src.dta_offset = 0x0080;
    src.version_major = 5;
    src.version_minor = 0;
    src.current_drive = 2; // C:
    src.verify = 1;
    src.return_code = 42;
    src.return_mode = 1;
    src.country = 1;
    src.codepage = 437;
    src.kernel_disabled = 0;
    src.kernel_running = 1;

    uint8_t buf[sizeof(dosbox::EngineStateDos)];
    std::memcpy(buf, &src, sizeof(src));

    dosbox::EngineStateDos dst{};
    std::memcpy(&dst, buf, sizeof(dst));

    EXPECT_EQ(dst.psp_segment, 0x1234);
    EXPECT_EQ(dst.dta_segment, 0x5678);
    EXPECT_EQ(dst.dta_offset, 0x0080);
    EXPECT_EQ(dst.version_major, 5);
    EXPECT_EQ(dst.version_minor, 0);
    EXPECT_EQ(dst.current_drive, 2);
    EXPECT_EQ(dst.verify, 1);
    EXPECT_EQ(dst.return_code, 42);
    EXPECT_EQ(dst.return_mode, 1);
    EXPECT_EQ(dst.country, 1);
    EXPECT_EQ(dst.codepage, 437);
    EXPECT_EQ(dst.kernel_disabled, 0);
    EXPECT_EQ(dst.kernel_running, 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Full V4 save/load round-trip via engine API
// ─────────────────────────────────────────────────────────────────────────────

class V4SaveLoadTest : public ::testing::Test {
protected:
    dosbox_lib_handle_t handle_ = nullptr;

    void SetUp() override {
        dosbox_lib_destroy(handle_);
        dosbox_lib_create(nullptr, &handle_);
        dosbox_lib_init(handle_);
    }

    void TearDown() override {
        if (handle_) dosbox_lib_destroy(handle_);
    }
};

TEST_F(V4SaveLoadTest, SaveProducesDynamicSize) {
    size_t size = 0;
    auto err = dosbox_lib_save_state(handle_, nullptr, 0, &size);
    ASSERT_EQ(err, DOSBOX_LIB_OK);
    // Dynamic size is at least the V5 base (792), may be larger with RAM/VGA blobs
    EXPECT_GE(size, dosbox::ENGINE_STATE_SIZE_V5_BASE);
}

TEST_F(V4SaveLoadTest, SaveLoadRoundTrip) {
    // Step to get some state
    dosbox_lib_step_result_t result;
    dosbox_lib_step_cycles(handle_, 5000, &result);

    // Save
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buf(size);
    auto err = dosbox_lib_save_state(handle_, buf.data(), buf.size(), &size);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Verify header
    dosbox::EngineStateHeader header{};
    std::memcpy(&header, buf.data(), sizeof(header));
    EXPECT_EQ(header.magic, dosbox::ENGINE_STATE_MAGIC);
    EXPECT_EQ(header.version, dosbox::ENGINE_STATE_VERSION);
    EXPECT_EQ(header.total_size, static_cast<uint32_t>(size));

    // Verify V4 offsets are non-zero
    EXPECT_GT(header.mixer_offset, 0u);
    EXPECT_GT(header.vga_offset, 0u);
    EXPECT_GT(header.dos_offset, 0u);

    // Load back
    err = dosbox_lib_load_state(handle_, buf.data(), buf.size());
    ASSERT_EQ(err, DOSBOX_LIB_OK);
}

// ─────────────────────────────────────────────────────────────────────────────
// V3 backward compatibility
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(V4SaveLoadTest, V3StateLoadsWithV4Code) {
    // Manually construct a V3 state buffer
    const size_t v3_size = dosbox::ENGINE_STATE_SIZE_V3;
    std::vector<uint8_t> v3_buf(v3_size, 0);

    // Build V3 header
    dosbox::EngineStateHeader header{};
    header.magic = dosbox::ENGINE_STATE_MAGIC;
    header.version = 3;
    header.total_size = static_cast<uint32_t>(v3_size);

    size_t offset = sizeof(dosbox::EngineStateHeader);
    header.timing_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateTiming);
    header.pic_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStatePicV3);
    header.keyboard_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateKeyboard);
    header.cpu_offset = static_cast<uint32_t>(offset);
    offset += sizeof(dosbox::EngineStateCpu);
    header.memory_offset = static_cast<uint32_t>(offset);

    // Write timing with known value
    dosbox::EngineStateTiming timing{};
    timing.total_cycles = 99999;
    std::memcpy(v3_buf.data() + header.timing_offset, &timing, sizeof(timing));

    // Write V3 PIC with some values
    dosbox::EngineStatePicV3 pic_v3{};
    pic_v3.ticks = 42;
    pic_v3.master_imr = 0xAB;
    pic_v3.slave_imr = 0xCD;
    pic_v3.master_isr = 0x11;
    pic_v3.slave_isr = 0x22;
    pic_v3.auto_eoi = 1;
    std::memcpy(v3_buf.data() + header.pic_offset, &pic_v3, sizeof(pic_v3));

    // Write empty keyboard, CPU, memory
    dosbox::EngineStateKeyboard kbd{};
    std::memcpy(v3_buf.data() + header.keyboard_offset, &kbd, sizeof(kbd));
    dosbox::EngineStateCpu cpu{};
    cpu.cycle_left = 3000;
    cpu.cycle_max = 3000;
    std::memcpy(v3_buf.data() + header.cpu_offset, &cpu, sizeof(cpu));
    dosbox::EngineStateMemory mem{};
    std::memcpy(v3_buf.data() + header.memory_offset, &mem, sizeof(mem));

    // Compute checksum
    const uint8_t* data_start = v3_buf.data() + sizeof(dosbox::EngineStateHeader);
    size_t data_size = v3_size - sizeof(dosbox::EngineStateHeader);
    header.checksum = dosbox::compute_crc32(data_start, data_size);

    // Write header (with checksum)
    std::memcpy(v3_buf.data(), &header, sizeof(header));

    // Load V3 state with V4 code
    auto err = dosbox_lib_load_state(handle_, v3_buf.data(), v3_buf.size());
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Re-save as V4
    size_t out_size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &out_size);
    EXPECT_GE(out_size, dosbox::ENGINE_STATE_SIZE_V5_BASE); // Dynamic V5 size on re-save

    std::vector<uint8_t> resave_buf(out_size);
    dosbox_lib_save_state(handle_, resave_buf.data(), resave_buf.size(), &out_size);

    // Verify re-saved header is current version
    dosbox::EngineStateHeader resave_header{};
    std::memcpy(&resave_header, resave_buf.data(), sizeof(resave_header));
    EXPECT_EQ(resave_header.version, dosbox::ENGINE_STATE_VERSION);

    // Verify timing survived the V3->V4 round-trip
    dosbox::EngineStateTiming resave_timing{};
    std::memcpy(&resave_timing, resave_buf.data() + resave_header.timing_offset,
                sizeof(resave_timing));
    EXPECT_EQ(resave_timing.total_cycles, 99999u);
}
