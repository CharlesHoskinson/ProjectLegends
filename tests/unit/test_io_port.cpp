/**
 * @file test_io_port.cpp
 * @brief Unit tests for IoPortRegistration RAII wrapper.
 */

#include <gtest/gtest.h>
#include <legends/io_port.h>
#include <map>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// Mock I/O Port Registration System
// ─────────────────────────────────────────────────────────────────────────────

namespace legends::internal {

// Mock port registry for testing
static std::map<uint16_t, std::pair<IoReadHandler, IoWriteHandler>> g_registered_ports;

bool register_io_port(uint16_t port, IoReadHandler read, IoWriteHandler write) {
    if (g_registered_ports.count(port)) {
        return false;  // Already registered
    }
    g_registered_ports[port] = {std::move(read), std::move(write)};
    return true;
}

void unregister_io_port(uint16_t port) {
    g_registered_ports.erase(port);
}

bool is_port_registered(uint16_t port) {
    return g_registered_ports.count(port) > 0;
}

// Test helpers
void clear_all_ports() {
    g_registered_ports.clear();
}

size_t registered_port_count() {
    return g_registered_ports.size();
}

uint32_t invoke_read(uint16_t port, size_t width) {
    auto it = g_registered_ports.find(port);
    if (it != g_registered_ports.end() && it->second.first) {
        return it->second.first(port, width);
    }
    return 0xFFFFFFFF;
}

void invoke_write(uint16_t port, uint32_t value, size_t width) {
    auto it = g_registered_ports.find(port);
    if (it != g_registered_ports.end() && it->second.second) {
        it->second.second(port, value, width);
    }
}

} // namespace legends::internal

// ─────────────────────────────────────────────────────────────────────────────
// Test Fixture
// ─────────────────────────────────────────────────────────────────────────────

class IoPortRegistrationTest : public ::testing::Test {
protected:
    void SetUp() override {
        internal::clear_all_ports();
    }

    void TearDown() override {
        internal::clear_all_ports();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Construction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, ConstructorRegistersPort) {
    IoPortRegistration reg(0x1234,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    EXPECT_TRUE(reg.is_installed());
    EXPECT_EQ(reg.port(), 0x1234);
    EXPECT_TRUE(internal::is_port_registered(0x1234));
}

TEST_F(IoPortRegistrationTest, DefaultConstructorCreatesInvalid) {
    IoPortRegistration reg;

    EXPECT_FALSE(reg.is_installed());
    EXPECT_EQ(internal::registered_port_count(), 0u);
}

TEST_F(IoPortRegistrationTest, ReadOnlyPort) {
    IoPortRegistration reg(0x5678,
        [](uint16_t, size_t) { return 0x42u; }
    );

    EXPECT_TRUE(reg.is_installed());
    EXPECT_TRUE(reg.has_read_handler());
    EXPECT_FALSE(reg.has_write_handler());
}

// ─────────────────────────────────────────────────────────────────────────────
// Destruction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, DestructorUnregistersPort) {
    {
        IoPortRegistration reg(0xABCD,
            [](uint16_t, size_t) { return 0u; },
            [](uint16_t, uint32_t, size_t) {}
        );
        EXPECT_TRUE(internal::is_port_registered(0xABCD));
    }

    EXPECT_FALSE(internal::is_port_registered(0xABCD));
}

TEST_F(IoPortRegistrationTest, DestructorAfterManualUninstall) {
    {
        IoPortRegistration reg(0x1111,
            [](uint16_t, size_t) { return 0u; },
            [](uint16_t, uint32_t, size_t) {}
        );
        reg.uninstall();
        EXPECT_FALSE(internal::is_port_registered(0x1111));
    }
    // Destructor should be safe even after manual uninstall
    EXPECT_FALSE(internal::is_port_registered(0x1111));
}

// ─────────────────────────────────────────────────────────────────────────────
// Manual Operations Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, ManualUninstall) {
    IoPortRegistration reg(0x2222,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    reg.uninstall();

    EXPECT_FALSE(reg.is_installed());
    EXPECT_FALSE(internal::is_port_registered(0x2222));
}

TEST_F(IoPortRegistrationTest, DoubleUninstallIsSafe) {
    IoPortRegistration reg(0x3333,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    reg.uninstall();
    EXPECT_NO_THROW(reg.uninstall());
    EXPECT_FALSE(reg.is_installed());
}

TEST_F(IoPortRegistrationTest, ReinstallAfterUninstall) {
    IoPortRegistration reg(0x4444,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    reg.uninstall();
    EXPECT_FALSE(reg.is_installed());

    bool success = reg.reinstall();

    EXPECT_TRUE(success);
    EXPECT_TRUE(reg.is_installed());
    EXPECT_TRUE(internal::is_port_registered(0x4444));
}

// ─────────────────────────────────────────────────────────────────────────────
// Move Semantics Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, MoveConstructorTransfersOwnership) {
    IoPortRegistration original(0x5555,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    IoPortRegistration moved(std::move(original));

    EXPECT_FALSE(original.is_installed());
    EXPECT_TRUE(moved.is_installed());
    EXPECT_EQ(moved.port(), 0x5555);
    EXPECT_TRUE(internal::is_port_registered(0x5555));
}

TEST_F(IoPortRegistrationTest, MoveAssignmentTransfersOwnership) {
    IoPortRegistration a(0x6666,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );
    IoPortRegistration b(0x7777,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    a = std::move(b);

    EXPECT_FALSE(internal::is_port_registered(0x6666));  // Old a unregistered
    EXPECT_TRUE(internal::is_port_registered(0x7777));   // b's port kept
    EXPECT_TRUE(a.is_installed());
    EXPECT_FALSE(b.is_installed());
}

TEST_F(IoPortRegistrationTest, MoveToDefaultConstructed) {
    IoPortRegistration source(0x8888,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    IoPortRegistration dest;
    dest = std::move(source);

    EXPECT_FALSE(source.is_installed());
    EXPECT_TRUE(dest.is_installed());
    EXPECT_EQ(dest.port(), 0x8888);
}

// ─────────────────────────────────────────────────────────────────────────────
// Handler Invocation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, ReadHandlerInvoked) {
    uint32_t read_value = 0;
    IoPortRegistration reg(0x9999,
        [&](uint16_t port, size_t width) {
            read_value = 0xCAFEBABE;
            return read_value;
        },
        nullptr
    );

    uint32_t result = internal::invoke_read(0x9999, 4);

    EXPECT_EQ(result, 0xCAFEBABE);
    EXPECT_EQ(read_value, 0xCAFEBABE);
}

TEST_F(IoPortRegistrationTest, WriteHandlerInvoked) {
    uint32_t written_value = 0;
    uint16_t written_port = 0;

    IoPortRegistration reg(0xAAAA,
        nullptr,
        [&](uint16_t port, uint32_t value, size_t width) {
            written_port = port;
            written_value = value;
        }
    );

    internal::invoke_write(0xAAAA, 0x12345678, 4);

    EXPECT_EQ(written_port, 0xAAAA);
    EXPECT_EQ(written_value, 0x12345678);
}

TEST_F(IoPortRegistrationTest, PortNumberPassedToHandler) {
    uint16_t received_port = 0;
    size_t received_width = 0;

    IoPortRegistration reg(0xBBBB,
        [&](uint16_t port, size_t width) {
            received_port = port;
            received_width = width;
            return 0u;
        },
        nullptr
    );

    internal::invoke_read(0xBBBB, 2);

    EXPECT_EQ(received_port, 0xBBBB);
    EXPECT_EQ(received_width, 2u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Boolean Conversion Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, BoolConversionInstalledIsTrue) {
    IoPortRegistration reg(0xCCCC,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    EXPECT_TRUE(static_cast<bool>(reg));
    if (reg) {
        // Should enter this branch
        SUCCEED();
    } else {
        FAIL() << "Boolean conversion should be true";
    }
}

TEST_F(IoPortRegistrationTest, BoolConversionNotInstalledIsFalse) {
    IoPortRegistration reg;

    EXPECT_FALSE(static_cast<bool>(reg));
}

// ─────────────────────────────────────────────────────────────────────────────
// IoPortRange Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, RangeRegistersAllPorts) {
    IoPortRange range(0x3C0, 16,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    EXPECT_EQ(range.installed_count(), 16u);
    EXPECT_TRUE(range.is_fully_installed());

    for (uint16_t i = 0; i < 16; i++) {
        EXPECT_TRUE(internal::is_port_registered(0x3C0 + i))
            << "Port 0x" << std::hex << (0x3C0 + i) << " not registered";
    }
}

TEST_F(IoPortRegistrationTest, RangeUnregistersOnDestruction) {
    {
        IoPortRange range(0x400, 8,
            [](uint16_t, size_t) { return 0u; },
            [](uint16_t, uint32_t, size_t) {}
        );
        EXPECT_EQ(internal::registered_port_count(), 8u);
    }

    EXPECT_EQ(internal::registered_port_count(), 0u);
}

TEST_F(IoPortRegistrationTest, RangeMoveTransfersOwnership) {
    IoPortRange range1(0x500, 4,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    IoPortRange range2(std::move(range1));

    EXPECT_EQ(range1.installed_count(), 0u);
    EXPECT_EQ(range2.installed_count(), 4u);
    EXPECT_EQ(internal::registered_port_count(), 4u);
}

TEST_F(IoPortRegistrationTest, RangeHandlerReceivesCorrectPort) {
    std::vector<uint16_t> ports_read;

    IoPortRange range(0x600, 4,
        [&](uint16_t port, size_t) {
            ports_read.push_back(port);
            return 0u;
        },
        nullptr
    );

    // Invoke each port
    for (uint16_t i = 0; i < 4; i++) {
        internal::invoke_read(0x600 + i, 1);
    }

    ASSERT_EQ(ports_read.size(), 4u);
    EXPECT_EQ(ports_read[0], 0x600);
    EXPECT_EQ(ports_read[1], 0x601);
    EXPECT_EQ(ports_read[2], 0x602);
    EXPECT_EQ(ports_read[3], 0x603);
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(IoPortRegistrationTest, DuplicateRegistrationFails) {
    IoPortRegistration reg1(0xDDDD,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    IoPortRegistration reg2(0xDDDD,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    EXPECT_TRUE(reg1.is_installed());
    EXPECT_FALSE(reg2.is_installed());  // Should fail
}

TEST_F(IoPortRegistrationTest, ZeroPortNumber) {
    IoPortRegistration reg(0x0000,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    EXPECT_TRUE(reg.is_installed());
    EXPECT_EQ(reg.port(), 0x0000);
}

TEST_F(IoPortRegistrationTest, MaxPortNumber) {
    IoPortRegistration reg(0xFFFF,
        [](uint16_t, size_t) { return 0u; },
        [](uint16_t, uint32_t, size_t) {}
    );

    EXPECT_TRUE(reg.is_installed());
    EXPECT_EQ(reg.port(), 0xFFFF);
}

