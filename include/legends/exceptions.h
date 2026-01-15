/**
 * @file exceptions.h
 * @brief Exception hierarchy for unexpected failures.
 *
 * These exceptions represent programming errors or system failures
 * that cannot be handled through normal control flow.
 *
 * Requirements implemented:
 * - REQ-FND-003: Exceptions for programming errors
 * - REQ-FND-014-016: Specific exception types
 * - REQ-FND-040: FatalException replaces abort()
 */

#pragma once

#include <stdexcept>
#include <string>
#include <cstdint>
#include <format>

namespace legends {

/**
 * @brief Base class for all Legends/DOSBox emulator exceptions.
 *
 * Derives from std::runtime_error for compatibility with
 * standard exception handling.
 */
class EmulatorException : public std::runtime_error {
public:
    explicit EmulatorException(const std::string& msg)
        : std::runtime_error(msg)
    {}

    /**
     * @brief Construct with formatted message using std::format.
     */
    template<typename... Args>
    static std::string format_message(std::format_string<Args...> fmt, Args&&... args) {
        return std::format(fmt, std::forward<Args>(args)...);
    }
};

/**
 * @brief Exception for illegal CPU states.
 *
 * Thrown when the CPU enters an invalid state that cannot
 * be recovered through normal emulation.
 *
 * Examples:
 * - Invalid opcode encountered
 * - Protected mode violation
 * - Triple fault
 */
class IllegalCpuStateException : public EmulatorException {
public:
    explicit IllegalCpuStateException(const std::string& msg)
        : EmulatorException("Illegal CPU state: " + msg)
        , eip_(0)
        , cs_(0)
    {}

    IllegalCpuStateException(const std::string& msg, uint32_t eip, uint16_t cs)
        : EmulatorException(format_message(
            "Illegal CPU state at {:04X}:{:08X}: {}", cs, eip, msg))
        , eip_(eip)
        , cs_(cs)
    {}

    [[nodiscard]] uint32_t eip() const noexcept { return eip_; }
    [[nodiscard]] uint16_t cs() const noexcept { return cs_; }

private:
    uint32_t eip_;
    uint16_t cs_;
};

/**
 * @brief Exception for DMA subsystem errors.
 *
 * Thrown when DMA operations fail due to:
 * - Invalid channel access
 * - Address translation failure
 * - Transfer boundary violation
 */
class DmaException : public EmulatorException {
public:
    explicit DmaException(const std::string& msg)
        : EmulatorException("DMA error: " + msg)
        , channel_(-1)
    {}

    DmaException(const std::string& msg, int channel)
        : EmulatorException(format_message(
            "DMA error on channel {}: {}", channel, msg))
        , channel_(channel)
    {}

    [[nodiscard]] int channel() const noexcept { return channel_; }

private:
    int channel_;
};

/**
 * @brief Exception for invalid callback invocations.
 *
 * Thrown when:
 * - Invalid callback ID is invoked
 * - Callback handler is null
 * - Callback re-entry violation
 */
class CallbackException : public EmulatorException {
public:
    explicit CallbackException(uint32_t id)
        : EmulatorException(format_message("Illegal callback #{}", id))
        , callback_id_(id)
    {}

    CallbackException(uint32_t id, const std::string& msg)
        : EmulatorException(format_message(
            "Callback #{} error: {}", id, msg))
        , callback_id_(id)
    {}

    [[nodiscard]] uint32_t callback_id() const noexcept { return callback_id_; }

private:
    uint32_t callback_id_;
};

/**
 * @brief Exception for memory access violations.
 *
 * Thrown on out-of-bounds guest memory access.
 * Used in debug builds; release builds may use unchecked access.
 */
class MemoryAccessException : public EmulatorException {
public:
    explicit MemoryAccessException(uint32_t addr)
        : EmulatorException(format_message(
            "Memory access violation at 0x{:08X}", addr))
        , address_(addr)
        , size_(1)
    {}

    MemoryAccessException(uint32_t addr, size_t size)
        : EmulatorException(format_message(
            "Memory access violation: {} bytes at 0x{:08X}", size, addr))
        , address_(addr)
        , size_(size)
    {}

    [[nodiscard]] uint32_t address() const noexcept { return address_; }
    [[nodiscard]] size_t size() const noexcept { return size_; }

private:
    uint32_t address_;
    size_t size_;
};

/**
 * @brief Exception replacing abort() in library mode.
 *
 * When code that previously called abort() is executed in library
 * mode, this exception is thrown instead, allowing the host to
 * handle the error gracefully.
 *
 * @note Should only be caught at the top-level FFI boundary.
 */
class FatalException : public EmulatorException {
public:
    explicit FatalException(const std::string& msg)
        : EmulatorException("Fatal error: " + msg)
        , file_("")
        , line_(0)
    {}

    FatalException(const std::string& msg, const char* file, int line)
        : EmulatorException(format_message(
            "Fatal error at {}:{}: {}", file, line, msg))
        , file_(file)
        , line_(line)
    {}

    [[nodiscard]] const char* file() const noexcept { return file_; }
    [[nodiscard]] int line() const noexcept { return line_; }

private:
    const char* file_;
    int line_;
};

/**
 * @brief Exception for configuration errors.
 */
class ConfigException : public EmulatorException {
public:
    explicit ConfigException(const std::string& msg)
        : EmulatorException("Configuration error: " + msg)
    {}

    ConfigException(const std::string& section, const std::string& msg)
        : EmulatorException(format_message(
            "Configuration error in [{}]: {}", section, msg))
        , section_(section)
    {}

    [[nodiscard]] const std::string& section() const noexcept { return section_; }

private:
    std::string section_;
};

/**
 * @brief Exception for I/O port access errors.
 */
class IoPortException : public EmulatorException {
public:
    IoPortException(uint16_t port, const std::string& msg)
        : EmulatorException(format_message(
            "I/O port error at 0x{:04X}: {}", port, msg))
        , port_(port)
    {}

    [[nodiscard]] uint16_t port() const noexcept { return port_; }

private:
    uint16_t port_;
};

} // namespace legends

// ─────────────────────────────────────────────────────────────────────────────
// abort() Replacement Macro
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Replace abort() with exception in library mode.
 *
 * In standalone mode, calls real abort().
 * In library mode, throws FatalException.
 *
 * Usage: Replace `abort()` with `LEGENDS_ABORT("reason")`
 */
#ifdef LEGENDS_LIBRARY_MODE
    #define LEGENDS_ABORT(msg) \
        throw ::legends::FatalException(msg, __FILE__, __LINE__)
#else
    #include <cstdlib>
    #include <iostream>
    #define LEGENDS_ABORT(msg) \
        do { \
            std::cerr << "Fatal: " << (msg) << " at " << __FILE__ << ":" << __LINE__ << "\n"; \
            std::abort(); \
        } while(0)
#endif

/**
 * @brief Assert that throws in library mode instead of aborting.
 */
#ifdef LEGENDS_LIBRARY_MODE
    #define LEGENDS_ASSERT(cond, msg) \
        do { \
            if (!(cond)) { \
                throw ::legends::FatalException( \
                    std::string("Assertion failed: ") + (msg), __FILE__, __LINE__); \
            } \
        } while(0)
#else
    #include <cassert>
    #define LEGENDS_ASSERT(cond, msg) assert((cond) && (msg))
#endif
