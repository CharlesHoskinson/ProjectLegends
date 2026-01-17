/**
 * @file test_exceptions.cpp
 * @brief Unit tests for exception hierarchy.
 */

#ifdef _MSC_VER
#pragma warning(disable: 4127) // conditional expression is constant
#endif

#include <gtest/gtest.h>
#include <legends/exceptions.h>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// EmulatorException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(EmulatorExceptionTest, MessageStored) {
    EmulatorException ex("test message");
    EXPECT_STREQ(ex.what(), "test message");
}

TEST(EmulatorExceptionTest, DerivesFromRuntimeError) {
    EXPECT_THROW(
        throw EmulatorException("test"),
        std::runtime_error
    );
}

TEST(EmulatorExceptionTest, DerivesFromException) {
    EXPECT_THROW(
        throw EmulatorException("test"),
        std::exception
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// IllegalCpuStateException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(IllegalCpuStateExceptionTest, SimpleMessage) {
    IllegalCpuStateException ex("Invalid opcode");

    std::string what = ex.what();

    EXPECT_NE(what.find("Illegal CPU state"), std::string::npos);
    EXPECT_NE(what.find("Invalid opcode"), std::string::npos);
}

TEST(IllegalCpuStateExceptionTest, MessageContainsDetails) {
    IllegalCpuStateException ex("Invalid opcode", 0x12345678, 0x0008);

    std::string what = ex.what();

    EXPECT_NE(what.find("12345678"), std::string::npos);
    EXPECT_NE(what.find("0008"), std::string::npos);
    EXPECT_NE(what.find("Invalid opcode"), std::string::npos);
}

TEST(IllegalCpuStateExceptionTest, EipAccessorWorks) {
    IllegalCpuStateException ex("test", 0x1000, 0x0010);

    EXPECT_EQ(ex.eip(), 0x1000u);
}

TEST(IllegalCpuStateExceptionTest, CsAccessorWorks) {
    IllegalCpuStateException ex("test", 0x1000, 0x0010);

    EXPECT_EQ(ex.cs(), 0x0010);
}

TEST(IllegalCpuStateExceptionTest, DefaultEipAndCs) {
    IllegalCpuStateException ex("simple");

    EXPECT_EQ(ex.eip(), 0u);
    EXPECT_EQ(ex.cs(), 0);
}

TEST(IllegalCpuStateExceptionTest, DerivesFromEmulatorException) {
    EXPECT_THROW(
        throw IllegalCpuStateException("test"),
        EmulatorException
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// DmaException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DmaExceptionTest, SimpleMessage) {
    DmaException ex("Transfer failed");

    std::string what = ex.what();

    EXPECT_NE(what.find("DMA error"), std::string::npos);
    EXPECT_NE(what.find("Transfer failed"), std::string::npos);
}

TEST(DmaExceptionTest, MessageContainsChannel) {
    DmaException ex("Transfer failed", 3);

    std::string what = ex.what();

    EXPECT_NE(what.find("channel 3"), std::string::npos);
    EXPECT_NE(what.find("Transfer failed"), std::string::npos);
}

TEST(DmaExceptionTest, ChannelAccessorWorks) {
    DmaException ex("error", 5);

    EXPECT_EQ(ex.channel(), 5);
}

TEST(DmaExceptionTest, DefaultChannelIsNegative) {
    DmaException ex("error");

    EXPECT_EQ(ex.channel(), -1);
}

TEST(DmaExceptionTest, DerivesFromEmulatorException) {
    EXPECT_THROW(
        throw DmaException("test"),
        EmulatorException
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// CallbackException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CallbackExceptionTest, MessageContainsId) {
    CallbackException ex(42);

    std::string what = ex.what();

    EXPECT_NE(what.find("42"), std::string::npos);
}

TEST(CallbackExceptionTest, MessageWithDescription) {
    CallbackException ex(42, "handler null");

    std::string what = ex.what();

    EXPECT_NE(what.find("42"), std::string::npos);
    EXPECT_NE(what.find("handler null"), std::string::npos);
}

TEST(CallbackExceptionTest, IdAccessorWorks) {
    CallbackException ex(123, "handler null");

    EXPECT_EQ(ex.callback_id(), 123u);
}

TEST(CallbackExceptionTest, DerivesFromEmulatorException) {
    EXPECT_THROW(
        throw CallbackException(0),
        EmulatorException
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// MemoryAccessException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MemoryAccessExceptionTest, MessageContainsAddress) {
    MemoryAccessException ex(0xDEADBEEF);

    std::string what = ex.what();

    EXPECT_NE(what.find("DEADBEEF"), std::string::npos);
}

TEST(MemoryAccessExceptionTest, MessageContainsSize) {
    MemoryAccessException ex(0x1000, 4);

    std::string what = ex.what();

    EXPECT_NE(what.find("4 bytes"), std::string::npos);
}

TEST(MemoryAccessExceptionTest, AddressAccessorWorks) {
    MemoryAccessException ex(0x12345678, 4);

    EXPECT_EQ(ex.address(), 0x12345678u);
}

TEST(MemoryAccessExceptionTest, SizeAccessorWorks) {
    MemoryAccessException ex(0x1000, 16);

    EXPECT_EQ(ex.size(), 16u);
}

TEST(MemoryAccessExceptionTest, DefaultSizeIsOne) {
    MemoryAccessException ex(0x1000);

    EXPECT_EQ(ex.size(), 1u);
}

TEST(MemoryAccessExceptionTest, DerivesFromEmulatorException) {
    EXPECT_THROW(
        throw MemoryAccessException(0),
        EmulatorException
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// FatalException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FatalExceptionTest, SimpleMessage) {
    FatalException ex("crash");

    std::string what = ex.what();

    EXPECT_NE(what.find("Fatal error"), std::string::npos);
    EXPECT_NE(what.find("crash"), std::string::npos);
}

TEST(FatalExceptionTest, MessageContainsLocation) {
    FatalException ex("crash", "cpu.cpp", 123);

    std::string what = ex.what();

    EXPECT_NE(what.find("cpu.cpp"), std::string::npos);
    EXPECT_NE(what.find("123"), std::string::npos);
}

TEST(FatalExceptionTest, FileAccessorWorks) {
    FatalException ex("test", "memory.cpp", 456);

    EXPECT_STREQ(ex.file(), "memory.cpp");
}

TEST(FatalExceptionTest, LineAccessorWorks) {
    FatalException ex("test", "memory.cpp", 456);

    EXPECT_EQ(ex.line(), 456);
}

TEST(FatalExceptionTest, DefaultLocationEmpty) {
    FatalException ex("test");

    EXPECT_STREQ(ex.file(), "");
    EXPECT_EQ(ex.line(), 0);
}

TEST(FatalExceptionTest, DerivesFromEmulatorException) {
    EXPECT_THROW(
        throw FatalException("test"),
        EmulatorException
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ConfigException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ConfigExceptionTest, SimpleMessage) {
    ConfigException ex("invalid format");

    std::string what = ex.what();

    EXPECT_NE(what.find("Configuration error"), std::string::npos);
    EXPECT_NE(what.find("invalid format"), std::string::npos);
}

TEST(ConfigExceptionTest, MessageContainsSection) {
    ConfigException ex("dosbox", "unknown key");

    std::string what = ex.what();

    EXPECT_NE(what.find("[dosbox]"), std::string::npos);
    EXPECT_NE(what.find("unknown key"), std::string::npos);
}

TEST(ConfigExceptionTest, SectionAccessorWorks) {
    ConfigException ex("render", "bad value");

    EXPECT_EQ(ex.section(), "render");
}

TEST(ConfigExceptionTest, EmptySectionWhenSimple) {
    ConfigException ex("simple error");

    EXPECT_EQ(ex.section(), "");
}

TEST(ConfigExceptionTest, DerivesFromEmulatorException) {
    EXPECT_THROW(
        throw ConfigException("test"),
        EmulatorException
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// IoPortException Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(IoPortExceptionTest, MessageContainsPort) {
    IoPortException ex(0x3D4, "invalid write");

    std::string what = ex.what();

    EXPECT_NE(what.find("03D4"), std::string::npos);
    EXPECT_NE(what.find("invalid write"), std::string::npos);
}

TEST(IoPortExceptionTest, PortAccessorWorks) {
    IoPortException ex(0x60, "keyboard error");

    EXPECT_EQ(ex.port(), 0x60);
}

TEST(IoPortExceptionTest, DerivesFromEmulatorException) {
    EXPECT_THROW(
        throw IoPortException(0x100, "test"),
        EmulatorException
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Exception Hierarchy Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ExceptionHierarchyTest, AllDeriveFromEmulatorException) {
    EXPECT_THROW(
        throw IllegalCpuStateException("test"),
        EmulatorException
    );
    EXPECT_THROW(
        throw DmaException("test"),
        EmulatorException
    );
    EXPECT_THROW(
        throw CallbackException(0),
        EmulatorException
    );
    EXPECT_THROW(
        throw MemoryAccessException(0),
        EmulatorException
    );
    EXPECT_THROW(
        throw FatalException("test"),
        EmulatorException
    );
    EXPECT_THROW(
        throw ConfigException("test"),
        EmulatorException
    );
    EXPECT_THROW(
        throw IoPortException(0, "test"),
        EmulatorException
    );
}

TEST(ExceptionHierarchyTest, AllDeriveFromStdException) {
    EXPECT_THROW(
        throw IllegalCpuStateException("test"),
        std::exception
    );
    EXPECT_THROW(
        throw DmaException("test"),
        std::exception
    );
    EXPECT_THROW(
        throw CallbackException(0),
        std::exception
    );
    EXPECT_THROW(
        throw MemoryAccessException(0),
        std::exception
    );
    EXPECT_THROW(
        throw FatalException("test"),
        std::exception
    );
    EXPECT_THROW(
        throw ConfigException("test"),
        std::exception
    );
    EXPECT_THROW(
        throw IoPortException(0, "test"),
        std::exception
    );
}

TEST(ExceptionHierarchyTest, CanCatchByBase) {
    bool caught = false;
    try {
        throw IllegalCpuStateException("test", 0x1000, 0x08);
    } catch (const EmulatorException& e) {
        // Should be caught here
        EXPECT_NE(std::string(e.what()).find("CPU state"), std::string::npos);
        caught = true;
    }
    EXPECT_TRUE(caught) << "Exception was not caught by base class";
}

TEST(ExceptionHierarchyTest, CanDistinguishByType) {
    auto thrower = [](int type) {
        switch (type) {
            case 0: throw IllegalCpuStateException("cpu");
            case 1: throw DmaException("dma");
            case 2: throw MemoryAccessException(0x1000);
            default: throw EmulatorException("other");
        }
    };

    // CPU exception
    try {
        thrower(0);
        FAIL();
    } catch (const IllegalCpuStateException&) {
        // Expected
    } catch (...) {
        FAIL() << "Wrong exception type caught";
    }

    // DMA exception
    try {
        thrower(1);
        FAIL();
    } catch (const DmaException&) {
        // Expected
    } catch (...) {
        FAIL() << "Wrong exception type caught";
    }

    // Memory exception
    try {
        thrower(2);
        FAIL();
    } catch (const MemoryAccessException&) {
        // Expected
    } catch (...) {
        FAIL() << "Wrong exception type caught";
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ABORT Macro Tests (Library Mode)
// ─────────────────────────────────────────────────────────────────────────────

#ifdef LEGENDS_LIBRARY_MODE

TEST(AiboxAbortTest, ThrowsFatalException) {
    EXPECT_THROW(
        LEGENDS_ABORT("test abort"),
        FatalException
    );
}

TEST(AiboxAbortTest, MessageIncluded) {
    bool caught = false;
    try {
        LEGENDS_ABORT("custom message");
    } catch (const FatalException& e) {
        EXPECT_NE(std::string(e.what()).find("custom message"), std::string::npos);
        caught = true;
    }
    EXPECT_TRUE(caught) << "Should have thrown";
}

TEST(AiboxAbortTest, LocationIncluded) {
    bool caught = false;
    try {
        LEGENDS_ABORT("test");
    } catch (const FatalException& e) {
        EXPECT_NE(e.file(), nullptr);
        EXPECT_GT(e.line(), 0);
        caught = true;
    }
    EXPECT_TRUE(caught) << "Should have thrown";
}

#endif // LEGENDS_LIBRARY_MODE

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ASSERT Macro Tests (Library Mode)
// ─────────────────────────────────────────────────────────────────────────────

#ifdef LEGENDS_LIBRARY_MODE

TEST(AiboxAssertTest, PassesOnTrue) {
    EXPECT_NO_THROW(LEGENDS_ASSERT(true, "should pass"));
    EXPECT_NO_THROW(LEGENDS_ASSERT(1 == 1, "math works"));
}

TEST(AiboxAssertTest, ThrowsOnFalse) {
    EXPECT_THROW(
        LEGENDS_ASSERT(false, "should fail"),
        FatalException
    );
}

TEST(AiboxAssertTest, MessageIncluded) {
    try {
        LEGENDS_ASSERT(false, "custom assertion message");
        FAIL() << "Should have thrown";
    } catch (const FatalException& e) {
        EXPECT_NE(std::string(e.what()).find("custom assertion message"), std::string::npos);
    }
}

#endif // LEGENDS_LIBRARY_MODE
