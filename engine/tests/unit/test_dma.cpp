/**
 * @file test_dma.cpp
 * @brief Unit tests for DMA controller RAII wrappers.
 */

#include <gtest/gtest.h>
#include <aibox/dma.h>

using namespace aibox;

// ─────────────────────────────────────────────────────────────────────────────
// DmaChannel Tests
// ─────────────────────────────────────────────────────────────────────────────

class DmaChannelTest : public ::testing::Test {
protected:
    void SetUp() override {
        channel_ = std::make_unique<DmaChannel>(0);
    }

    std::unique_ptr<DmaChannel> channel_;
};

TEST_F(DmaChannelTest, ConstructorInitializesState) {
    DmaChannel ch(2);

    EXPECT_EQ(ch.channel(), 2);
    EXPECT_FALSE(ch.is_enabled());
    EXPECT_TRUE(ch.is_masked());
    EXPECT_FALSE(ch.is_ready());
    EXPECT_EQ(ch.mode(), DmaMode::Single);
    EXPECT_EQ(ch.direction(), DmaDirection::Write);
    EXPECT_FALSE(ch.auto_init());
}

TEST_F(DmaChannelTest, EnableDisable) {
    channel_->enable();
    EXPECT_TRUE(channel_->is_enabled());

    channel_->disable();
    EXPECT_FALSE(channel_->is_enabled());
}

TEST_F(DmaChannelTest, MaskUnmask) {
    EXPECT_TRUE(channel_->is_masked());

    channel_->unmask();
    EXPECT_FALSE(channel_->is_masked());

    channel_->mask();
    EXPECT_TRUE(channel_->is_masked());
}

TEST_F(DmaChannelTest, IsReadyRequiresBothEnabledAndUnmasked) {
    EXPECT_FALSE(channel_->is_ready());  // Neither

    channel_->enable();
    EXPECT_FALSE(channel_->is_ready());  // Enabled but masked

    channel_->unmask();
    EXPECT_TRUE(channel_->is_ready());   // Both

    channel_->disable();
    EXPECT_FALSE(channel_->is_ready());  // Unmasked but disabled
}

TEST_F(DmaChannelTest, SetMode) {
    channel_->set_mode(DmaMode::Block);
    EXPECT_EQ(channel_->mode(), DmaMode::Block);

    channel_->set_mode(DmaMode::Cascade);
    EXPECT_EQ(channel_->mode(), DmaMode::Cascade);
}

TEST_F(DmaChannelTest, SetDirection) {
    channel_->set_direction(DmaDirection::Read);
    EXPECT_EQ(channel_->direction(), DmaDirection::Read);

    channel_->set_direction(DmaDirection::Verify);
    EXPECT_EQ(channel_->direction(), DmaDirection::Verify);
}

TEST_F(DmaChannelTest, SetAutoInit) {
    EXPECT_FALSE(channel_->auto_init());

    channel_->set_auto_init(true);
    EXPECT_TRUE(channel_->auto_init());

    channel_->set_auto_init(false);
    EXPECT_FALSE(channel_->auto_init());
}

TEST_F(DmaChannelTest, SetBaseAddress) {
    channel_->set_base_address(0x1234);

    EXPECT_EQ(channel_->base_address(), 0x1234);
    EXPECT_EQ(channel_->current_address(), 0x1234);
}

TEST_F(DmaChannelTest, SetBaseCount) {
    channel_->set_base_count(0x00FF);

    EXPECT_EQ(channel_->base_count(), 0x00FF);
    EXPECT_EQ(channel_->current_count(), 0x00FF);
}

TEST_F(DmaChannelTest, SetPage) {
    channel_->set_page(0x12);
    EXPECT_EQ(channel_->page(), 0x12);
}

TEST_F(DmaChannelTest, PhysicalAddress8BitChannel) {
    // Channel 0 is 8-bit
    DmaChannel ch(0);
    ch.set_page(0x12);
    ch.set_base_address(0x3456);

    // 8-bit: page << 16 | address = 0x12 << 16 | 0x3456 = 0x123456
    EXPECT_EQ(ch.physical_address(), 0x00123456u);
}

TEST_F(DmaChannelTest, PhysicalAddress16BitChannel) {
    // Channel 5 is 16-bit (controller 1)
    DmaChannel ch(5);
    ch.set_page(0x12);
    ch.set_base_address(0x3456);

    // 16-bit: page << 17 | (address << 1) = 0x12 << 17 | (0x3456 << 1)
    // = 0x240000 | 0x68AC = 0x2468AC
    EXPECT_EQ(ch.physical_address(), 0x002468ACu);
}

TEST_F(DmaChannelTest, RemainingCount) {
    channel_->set_base_count(0x00FF);  // 256 bytes (count - 1)
    EXPECT_EQ(channel_->remaining(), 256u);

    channel_->set_base_count(0x0000);  // 1 byte
    EXPECT_EQ(channel_->remaining(), 1u);
}

TEST_F(DmaChannelTest, Reset) {
    channel_->enable();
    channel_->unmask();
    channel_->set_base_address(0x1000);
    channel_->set_base_count(0x00FF);

    // Simulate transfer changing current values
    // (done internally by update_counters which is private)

    channel_->reset();

    EXPECT_FALSE(channel_->is_enabled());
    EXPECT_TRUE(channel_->is_masked());
    EXPECT_EQ(channel_->current_address(), channel_->base_address());
    EXPECT_EQ(channel_->current_count(), channel_->base_count());
}

// ─────────────────────────────────────────────────────────────────────────────
// DmaChannel Transfer Tests
// ─────────────────────────────────────────────────────────────────────────────

class DmaTransferTest : public ::testing::Test {
protected:
    void SetUp() override {
        mem_ = std::make_unique<GuestMemory>(64 * 1024);  // 64KB
        channel_ = std::make_unique<DmaChannel>(0);

        // Configure channel
        channel_->set_page(0);          // Page 0
        channel_->set_base_address(0x1000);
        channel_->set_base_count(0x00FF);  // 256 bytes
        channel_->enable();
        channel_->unmask();
    }

    std::unique_ptr<GuestMemory> mem_;
    std::unique_ptr<DmaChannel> channel_;
};

TEST_F(DmaTransferTest, TransferWhenNotReady) {
    channel_->mask();
    size_t transferred = channel_->transfer(*mem_, 16);
    EXPECT_EQ(transferred, 0u);
}

TEST_F(DmaTransferTest, TransferWithCallback) {
    size_t callback_length = 0;
    uint8_t* callback_buffer = nullptr;

    channel_->set_callback([&](uint8_t ch, uint8_t* buf, size_t len) {
        callback_length = len;
        callback_buffer = buf;
        return len;
    });

    size_t transferred = channel_->transfer(*mem_, 32);

    EXPECT_EQ(transferred, 32u);
    EXPECT_EQ(callback_length, 32u);
    EXPECT_EQ(callback_buffer, mem_->data() + 0x1000);
}

TEST_F(DmaTransferTest, TransferUpdatesCounters) {
    channel_->set_callback([](uint8_t, uint8_t*, size_t len) { return len; });

    uint16_t initial_addr = channel_->current_address();
    uint16_t initial_count = channel_->current_count();

    channel_->transfer(*mem_, 16);

    EXPECT_EQ(channel_->current_address(), initial_addr + 16);
    EXPECT_EQ(channel_->current_count(), initial_count - 16);
}

TEST_F(DmaTransferTest, TransferWithAddressDecrement) {
    channel_->set_address_decrement(true);
    channel_->set_callback([](uint8_t, uint8_t*, size_t len) { return len; });

    uint16_t initial_addr = channel_->current_address();
    channel_->transfer(*mem_, 16);

    EXPECT_EQ(channel_->current_address(), initial_addr - 16);
}

TEST_F(DmaTransferTest, TransferAutoInit) {
    // Set up small transfer
    channel_->set_base_count(0x0003);  // 4 bytes
    channel_->set_auto_init(true);
    channel_->set_callback([](uint8_t, uint8_t*, size_t len) { return len; });

    // Transfer all bytes
    channel_->transfer(*mem_, 4);

    // Should reload from base
    EXPECT_EQ(channel_->current_address(), channel_->base_address());
    EXPECT_EQ(channel_->current_count(), channel_->base_count());
}

TEST_F(DmaTransferTest, TransferBoundsValidation) {
    // Set up transfer beyond memory bounds
    channel_->set_page(0xFF);  // High page
    channel_->set_base_address(0xFF00);  // Near end of page

    // This should throw since 0xFF0000 + 0xFF00 > 64KB
    EXPECT_THROW(channel_->transfer(*mem_, 256), MemoryAccessException);
}

TEST_F(DmaTransferTest, ReadByte) {
    // Write a known value to memory
    mem_->write8(0x1000, 0xAB);

    uint8_t value = channel_->read_byte(*mem_);

    EXPECT_EQ(value, 0xAB);
    EXPECT_EQ(channel_->current_address(), 0x1001);  // Incremented
}

TEST_F(DmaTransferTest, WriteByte) {
    channel_->write_byte(*mem_, 0xCD);

    EXPECT_EQ(mem_->read8(0x1000), 0xCD);
    EXPECT_EQ(channel_->current_address(), 0x1001);
}

TEST_F(DmaTransferTest, ReadByteWhenNotReady) {
    channel_->mask();
    uint8_t value = channel_->read_byte(*mem_);
    EXPECT_EQ(value, 0);
}

TEST_F(DmaTransferTest, WriteByteWhenNotReady) {
    channel_->mask();
    mem_->write8(0x1000, 0x00);
    channel_->write_byte(*mem_, 0xFF);
    EXPECT_EQ(mem_->read8(0x1000), 0x00);  // Unchanged
}

// ─────────────────────────────────────────────────────────────────────────────
// DmaController Tests
// ─────────────────────────────────────────────────────────────────────────────

class DmaControllerTest : public ::testing::Test {
protected:
    void SetUp() override {
        ctrl_ = std::make_unique<DmaController>(0);
    }

    std::unique_ptr<DmaController> ctrl_;
};

TEST_F(DmaControllerTest, ConstructorCreatesChannels) {
    EXPECT_EQ(ctrl_->controller_num(), 0);

    for (uint8_t i = 0; i < DmaController::NUM_CHANNELS; i++) {
        DmaChannel* ch = ctrl_->channel(i);
        ASSERT_NE(ch, nullptr);
        EXPECT_EQ(ch->channel(), i);  // Global channel = local for controller 0
    }
}

TEST_F(DmaControllerTest, Controller1HasCorrectChannelNumbers) {
    DmaController ctrl1(1);

    for (uint8_t i = 0; i < DmaController::NUM_CHANNELS; i++) {
        DmaChannel* ch = ctrl1.channel(i);
        ASSERT_NE(ch, nullptr);
        EXPECT_EQ(ch->channel(), 4 + i);  // Global channel 4-7
    }
}

TEST_F(DmaControllerTest, InvalidChannelIndexReturnsNull) {
    EXPECT_EQ(ctrl_->channel(4), nullptr);
    EXPECT_EQ(ctrl_->channel(255), nullptr);
}

TEST_F(DmaControllerTest, Reset) {
    // Configure channels
    for (uint8_t i = 0; i < DmaController::NUM_CHANNELS; i++) {
        ctrl_->channel(i)->enable();
        ctrl_->channel(i)->unmask();
    }

    ctrl_->reset();

    for (uint8_t i = 0; i < DmaController::NUM_CHANNELS; i++) {
        EXPECT_FALSE(ctrl_->channel(i)->is_enabled());
        EXPECT_TRUE(ctrl_->channel(i)->is_masked());
    }
}

TEST_F(DmaControllerTest, WriteMode) {
    // Mode register format: MM_AA_TD_CC
    // MM = mode, AA = address dec + auto-init, TD = transfer dir, CC = channel
    // Example: 0x58 = 01_01_10_00 = Single mode, auto-init, read, channel 0
    ctrl_->write_mode(0x58);

    DmaChannel* ch = ctrl_->channel(0);
    EXPECT_EQ(ch->mode(), DmaMode::Single);
    EXPECT_EQ(ch->direction(), DmaDirection::Read);
    EXPECT_TRUE(ch->auto_init());
}

TEST_F(DmaControllerTest, WriteSingleMask) {
    // Format: ----_M_CC (M=mask bit, CC=channel)
    ctrl_->channel(2)->unmask();
    EXPECT_FALSE(ctrl_->channel(2)->is_masked());

    ctrl_->write_single_mask(0x06);  // Mask channel 2 (0b110)
    EXPECT_TRUE(ctrl_->channel(2)->is_masked());

    ctrl_->write_single_mask(0x02);  // Unmask channel 2 (0b010)
    EXPECT_FALSE(ctrl_->channel(2)->is_masked());
}

TEST_F(DmaControllerTest, WriteAllMask) {
    ctrl_->write_all_mask(0x0F);  // Mask all
    for (uint8_t i = 0; i < DmaController::NUM_CHANNELS; i++) {
        EXPECT_TRUE(ctrl_->channel(i)->is_masked());
    }

    ctrl_->write_all_mask(0x05);  // Mask channels 0 and 2 only
    EXPECT_TRUE(ctrl_->channel(0)->is_masked());
    EXPECT_FALSE(ctrl_->channel(1)->is_masked());
    EXPECT_TRUE(ctrl_->channel(2)->is_masked());
    EXPECT_FALSE(ctrl_->channel(3)->is_masked());
}

TEST_F(DmaControllerTest, FlipFlop) {
    ctrl_->clear_flip_flop();

    EXPECT_FALSE(ctrl_->flip_flop());  // First read: false, toggles to true
    EXPECT_TRUE(ctrl_->flip_flop());   // Second read: true, toggles to false
    EXPECT_FALSE(ctrl_->flip_flop());  // Third read: false again
}

TEST_F(DmaControllerTest, MoveSemantics) {
    DmaController moved(std::move(*ctrl_));

    EXPECT_EQ(moved.controller_num(), 0);
    for (uint8_t i = 0; i < DmaController::NUM_CHANNELS; i++) {
        EXPECT_NE(moved.channel(i), nullptr);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// DmaSubsystem Tests
// ─────────────────────────────────────────────────────────────────────────────

class DmaSubsystemTest : public ::testing::Test {
protected:
    void SetUp() override {
        dma_ = std::make_unique<DmaSubsystem>();
    }

    std::unique_ptr<DmaSubsystem> dma_;
};

TEST_F(DmaSubsystemTest, ConstructorCreatesBothControllers) {
    EXPECT_NE(dma_->controller(0), nullptr);
    EXPECT_NE(dma_->controller(1), nullptr);
    EXPECT_EQ(dma_->controller(2), nullptr);  // Invalid
}

TEST_F(DmaSubsystemTest, ControllerNumbers) {
    EXPECT_EQ(dma_->controller(0)->controller_num(), 0);
    EXPECT_EQ(dma_->controller(1)->controller_num(), 1);
}

TEST_F(DmaSubsystemTest, GlobalChannelAccess) {
    // Channels 0-3 are on controller 0
    for (uint8_t i = 0; i < 4; i++) {
        DmaChannel* ch = dma_->channel(i);
        ASSERT_NE(ch, nullptr) << "Channel " << static_cast<int>(i) << " is null";
        EXPECT_EQ(ch->channel(), i);
    }

    // Channels 4-7 are on controller 1
    for (uint8_t i = 4; i < 8; i++) {
        DmaChannel* ch = dma_->channel(i);
        ASSERT_NE(ch, nullptr) << "Channel " << static_cast<int>(i) << " is null";
        EXPECT_EQ(ch->channel(), i);
    }
}

TEST_F(DmaSubsystemTest, InvalidGlobalChannelReturnsNull) {
    EXPECT_EQ(dma_->channel(8), nullptr);
    EXPECT_EQ(dma_->channel(255), nullptr);
}

TEST_F(DmaSubsystemTest, GlobalChannelAccessMatchesController) {
    // Verify that global access returns same pointer as controller access
    for (uint8_t i = 0; i < 8; i++) {
        uint8_t ctrl_idx = i / 4;
        uint8_t chan_idx = i % 4;

        DmaChannel* global = dma_->channel(i);
        DmaChannel* via_ctrl = dma_->controller(ctrl_idx)->channel(chan_idx);

        EXPECT_EQ(global, via_ctrl) << "Channel " << static_cast<int>(i);
    }
}

TEST_F(DmaSubsystemTest, Reset) {
    // Configure some channels
    for (uint8_t i = 0; i < 8; i++) {
        dma_->channel(i)->enable();
        dma_->channel(i)->unmask();
    }

    dma_->reset();

    // All channels should be reset
    for (uint8_t i = 0; i < 8; i++) {
        EXPECT_FALSE(dma_->channel(i)->is_enabled()) << "Channel " << static_cast<int>(i);
        EXPECT_TRUE(dma_->channel(i)->is_masked()) << "Channel " << static_cast<int>(i);
    }
}

TEST_F(DmaSubsystemTest, MoveSemantics) {
    DmaSubsystem moved(std::move(*dma_));

    EXPECT_NE(moved.controller(0), nullptr);
    EXPECT_NE(moved.controller(1), nullptr);

    for (uint8_t i = 0; i < 8; i++) {
        EXPECT_NE(moved.channel(i), nullptr);
    }
}

TEST_F(DmaSubsystemTest, ChannelTypes) {
    // Channels 0-3 are 8-bit (controller 0)
    // Channels 4-7 are 16-bit (controller 1)

    // 8-bit channel physical address calculation
    DmaChannel* ch0 = dma_->channel(0);
    ch0->set_page(0x01);
    ch0->set_base_address(0x2000);
    EXPECT_EQ(ch0->physical_address(), 0x00012000u);  // page << 16 | addr

    // 16-bit channel physical address calculation
    DmaChannel* ch5 = dma_->channel(5);
    ch5->set_page(0x01);
    ch5->set_base_address(0x2000);
    EXPECT_EQ(ch5->physical_address(), 0x00024000u);  // page << 17 | (addr << 1)
}

// ─────────────────────────────────────────────────────────────────────────────
// DMA Integration Tests
// ─────────────────────────────────────────────────────────────────────────────

class DmaIntegrationTest : public ::testing::Test {
protected:
    void SetUp() override {
        mem_ = std::make_unique<GuestMemory>(1024 * 1024);  // 1MB
        dma_ = std::make_unique<DmaSubsystem>();
    }

    std::unique_ptr<GuestMemory> mem_;
    std::unique_ptr<DmaSubsystem> dma_;
};

TEST_F(DmaIntegrationTest, FloppyDmaSimulation) {
    // Simulate floppy DMA setup (channel 2)
    DmaChannel* ch = dma_->channel(2);

    // Configure for read operation (device to memory)
    ch->set_direction(DmaDirection::Write);
    ch->set_mode(DmaMode::Single);
    ch->set_base_address(0x0000);
    ch->set_base_count(511);  // 512 bytes
    ch->set_page(0x00);       // Low memory
    ch->enable();
    ch->unmask();

    EXPECT_TRUE(ch->is_ready());
    EXPECT_EQ(ch->remaining(), 512u);
    EXPECT_EQ(ch->physical_address(), 0x0000u);
}

TEST_F(DmaIntegrationTest, SoundBlasterDmaSimulation) {
    // Simulate Sound Blaster DMA setup (channel 1)
    DmaChannel* ch = dma_->channel(1);

    ch->set_direction(DmaDirection::Read);  // Memory to device (playback)
    ch->set_mode(DmaMode::Single);
    ch->set_auto_init(true);  // Continuous playback
    ch->set_base_address(0x8000);
    ch->set_base_count(0x7FFF);  // 32KB buffer
    ch->set_page(0x00);
    ch->enable();
    ch->unmask();

    EXPECT_TRUE(ch->is_ready());
    EXPECT_TRUE(ch->auto_init());
}

TEST_F(DmaIntegrationTest, MultipleTransfers) {
    DmaChannel* ch = dma_->channel(1);
    ch->set_base_address(0x0000);
    ch->set_base_count(0x00FF);  // 256 bytes
    ch->set_page(0x00);
    ch->enable();
    ch->unmask();

    // Prepare test data
    for (size_t i = 0; i < 256; i++) {
        mem_->write8(static_cast<uint32_t>(i), static_cast<uint8_t>(i));
    }

    // Read bytes one at a time
    std::vector<uint8_t> read_data;
    for (int i = 0; i < 256; i++) {
        read_data.push_back(ch->read_byte(*mem_));
    }

    // Verify
    for (size_t i = 0; i < 256; i++) {
        EXPECT_EQ(read_data[i], static_cast<uint8_t>(i));
    }
}

TEST_F(DmaIntegrationTest, WriteTransfer) {
    DmaChannel* ch = dma_->channel(1);
    ch->set_base_address(0x1000);
    ch->set_base_count(0x000F);  // 16 bytes
    ch->set_page(0x00);
    ch->set_direction(DmaDirection::Write);
    ch->enable();
    ch->unmask();

    // Write bytes
    for (uint8_t i = 0; i < 16; i++) {
        ch->write_byte(*mem_, i * 2);
    }

    // Verify memory
    for (uint32_t i = 0; i < 16; i++) {
        EXPECT_EQ(mem_->read8(0x1000 + i), static_cast<uint8_t>(i * 2));
    }
}

