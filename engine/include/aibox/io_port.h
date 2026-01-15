/**
 * @file io_port.h
 * @brief RAII wrapper for I/O port handler registration.
 *
 * Provides automatic unregistration of I/O port handlers when the
 * registration object goes out of scope.
 *
 * Requirements implemented:
 * - REQ-MEM-011: Auto unregister on scope exit
 * - REQ-MEM-014: Handle wrapper move semantics
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include <functional>
#include <cstdint>
#include <utility>

namespace aibox {

// ─────────────────────────────────────────────────────────────────────────────
// I/O Handler Types
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Function signature for I/O port read handlers.
 *
 * @param port The port number being read
 * @param width Access width in bytes (1, 2, or 4)
 * @return Value read from the port
 */
using IoReadHandler = std::function<uint32_t(uint16_t port, size_t width)>;

/**
 * @brief Function signature for I/O port write handlers.
 *
 * @param port The port number being written
 * @param value Value being written
 * @param width Access width in bytes (1, 2, or 4)
 */
using IoWriteHandler = std::function<void(uint16_t port, uint32_t value, size_t width)>;

// ─────────────────────────────────────────────────────────────────────────────
// Internal Registration Interface
// ─────────────────────────────────────────────────────────────────────────────

namespace internal {

/**
 * @brief Register I/O port handlers.
 *
 * This function should be implemented by the emulator core to register
 * handlers with the I/O subsystem.
 *
 * @param port Port number to register
 * @param read Read handler (may be nullptr for write-only)
 * @param write Write handler (may be nullptr for read-only)
 * @return true if registration succeeded
 */
bool register_io_port(uint16_t port, IoReadHandler read, IoWriteHandler write);

/**
 * @brief Unregister I/O port handlers.
 *
 * @param port Port number to unregister
 */
void unregister_io_port(uint16_t port);

/**
 * @brief Check if port is currently registered.
 *
 * @param port Port number to check
 * @return true if port is registered
 */
bool is_port_registered(uint16_t port);

} // namespace internal

// ─────────────────────────────────────────────────────────────────────────────
// IoPortRegistration - RAII wrapper
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief RAII wrapper for I/O port handler registration.
 *
 * Automatically unregisters handlers when the object goes out of scope.
 * Supports move semantics for transfer of ownership.
 *
 * @note Non-copyable to prevent double-unregistration.
 * @note Move semantics transfer ownership - moved-from object won't unregister.
 *
 * @invariant After construction with handlers, is_installed() == true
 * @invariant After move, source.is_installed() == false
 * @invariant After uninstall(), is_installed() == false
 *
 * Example:
 * @code
 *   {
 *       IoPortRegistration hypercall(0xDEAD,
 *           [](uint16_t, size_t) { return 0xCAFEBABE; },
 *           [](uint16_t, uint32_t val, size_t) { handle_command(val); }
 *       );
 *       // Port is registered and handling I/O
 *
 *   }  // Port automatically unregistered here
 * @endcode
 *
 * @see IoReadHandler, IoWriteHandler
 */
class IoPortRegistration {
public:
    // ─────────────────────────────────────────────────────────────
    // Construction and destruction
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Default constructor - creates invalid registration.
     * @post is_installed() == false
     */
    IoPortRegistration() noexcept = default;

    /**
     * @brief Register handlers for an I/O port.
     *
     * @param port Port number to register (0x0000-0xFFFF)
     * @param read Read handler (may be nullptr for write-only ports)
     * @param write Write handler (may be nullptr for read-only ports)
     * @post is_installed() == true if registration succeeded
     */
    IoPortRegistration(uint16_t port, IoReadHandler read, IoWriteHandler write)
        : port_(port)
        , read_(std::move(read))
        , write_(std::move(write))
        , installed_(false)
    {
        installed_ = internal::register_io_port(port_, read_, write_);
    }

    /**
     * @brief Convenience constructor for read-only port.
     */
    IoPortRegistration(uint16_t port, IoReadHandler read)
        : IoPortRegistration(port, std::move(read), nullptr)
    {}

    /**
     * @brief Destructor - unregisters port if still installed.
     *
     * Automatically calls uninstall() if the port is registered
     * (REQ-MEM-011).
     */
    ~IoPortRegistration() {
        uninstall();
    }

    // Non-copyable
    IoPortRegistration(const IoPortRegistration&) = delete;
    IoPortRegistration& operator=(const IoPortRegistration&) = delete;

    // Movable
    /**
     * @brief Move constructor - transfers ownership.
     *
     * @param other Source registration (will be invalidated)
     * @post other.is_installed() == false
     */
    IoPortRegistration(IoPortRegistration&& other) noexcept
        : port_(other.port_)
        , read_(std::move(other.read_))
        , write_(std::move(other.write_))
        , installed_(other.installed_)
    {
        other.installed_ = false;  // Prevent double-unregister
    }

    /**
     * @brief Move assignment - transfers ownership.
     *
     * Unregisters current port before taking ownership of other.
     *
     * @param other Source registration (will be invalidated)
     * @return Reference to this
     * @post other.is_installed() == false
     */
    IoPortRegistration& operator=(IoPortRegistration&& other) noexcept {
        if (this != &other) {
            uninstall();  // Unregister current
            port_ = other.port_;
            read_ = std::move(other.read_);
            write_ = std::move(other.write_);
            installed_ = other.installed_;
            other.installed_ = false;
        }
        return *this;
    }

    // ─────────────────────────────────────────────────────────────
    // Operations
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Manually unregister the port handler.
     *
     * Safe to call multiple times. After this call, is_installed()
     * returns false.
     *
     * @post is_installed() == false
     */
    void uninstall() noexcept {
        if (installed_) {
            internal::unregister_io_port(port_);
            installed_ = false;
        }
    }

    /**
     * @brief Reinstall the port handler.
     *
     * If already installed, does nothing. Otherwise attempts to
     * register the port again.
     *
     * @return true if installation succeeded
     */
    bool reinstall() noexcept {
        if (installed_) {
            return true;
        }
        if (read_ || write_) {
            installed_ = internal::register_io_port(port_, read_, write_);
        }
        return installed_;
    }

    // ─────────────────────────────────────────────────────────────
    // Accessors
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Check if port is currently registered.
     * @return true if handlers are installed
     */
    [[nodiscard]] bool is_installed() const noexcept { return installed_; }

    /**
     * @brief Get the registered port number.
     * @return Port number
     */
    [[nodiscard]] uint16_t port() const noexcept { return port_; }

    /**
     * @brief Check if read handler is set.
     */
    [[nodiscard]] bool has_read_handler() const noexcept {
        return static_cast<bool>(read_);
    }

    /**
     * @brief Check if write handler is set.
     */
    [[nodiscard]] bool has_write_handler() const noexcept {
        return static_cast<bool>(write_);
    }

    /**
     * @brief Explicit boolean conversion.
     * @return true if installed
     */
    explicit operator bool() const noexcept { return installed_; }

private:
    uint16_t port_ = 0;
    IoReadHandler read_;
    IoWriteHandler write_;
    bool installed_ = false;
};

// ─────────────────────────────────────────────────────────────────────────────
// IoPortRange - Multiple consecutive port registration
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief RAII wrapper for registering a range of consecutive I/O ports.
 *
 * Useful for devices that use multiple consecutive ports
 * (e.g., VGA uses 0x3C0-0x3CF).
 *
 * Example:
 * @code
 *   IoPortRange vga_ports(0x3C0, 16,
 *       [](uint16_t port, size_t) { return vga_read(port); },
 *       [](uint16_t port, uint32_t val, size_t) { vga_write(port, val); }
 *   );
 * @endcode
 */
class IoPortRange {
public:
    /**
     * @brief Register handlers for a range of consecutive ports.
     *
     * @param base_port First port number
     * @param count Number of consecutive ports
     * @param read Read handler (receives actual port number)
     * @param write Write handler (receives actual port number)
     */
    IoPortRange(uint16_t base_port, size_t count,
                IoReadHandler read, IoWriteHandler write)
        : base_port_(base_port)
        , count_(count)
        , read_(read)
        , write_(write)
        , installed_count_(0)
    {
        install();
    }

    /**
     * @brief Destructor - unregisters all ports in range.
     */
    ~IoPortRange() {
        uninstall();
    }

    // Non-copyable
    IoPortRange(const IoPortRange&) = delete;
    IoPortRange& operator=(const IoPortRange&) = delete;

    // Movable
    IoPortRange(IoPortRange&& other) noexcept
        : base_port_(other.base_port_)
        , count_(other.count_)
        , read_(std::move(other.read_))
        , write_(std::move(other.write_))
        , installed_count_(other.installed_count_)
    {
        other.installed_count_ = 0;
    }

    IoPortRange& operator=(IoPortRange&& other) noexcept {
        if (this != &other) {
            uninstall();
            base_port_ = other.base_port_;
            count_ = other.count_;
            read_ = std::move(other.read_);
            write_ = std::move(other.write_);
            installed_count_ = other.installed_count_;
            other.installed_count_ = 0;
        }
        return *this;
    }

    /**
     * @brief Uninstall all registered ports.
     */
    void uninstall() noexcept {
        for (size_t i = 0; i < installed_count_; i++) {
            internal::unregister_io_port(static_cast<uint16_t>(base_port_ + i));
        }
        installed_count_ = 0;
    }

    /**
     * @brief Check if all ports are installed.
     */
    [[nodiscard]] bool is_fully_installed() const noexcept {
        return installed_count_ == count_;
    }

    /**
     * @brief Get number of successfully installed ports.
     */
    [[nodiscard]] size_t installed_count() const noexcept {
        return installed_count_;
    }

    /**
     * @brief Get base port number.
     */
    [[nodiscard]] uint16_t base_port() const noexcept { return base_port_; }

    /**
     * @brief Get total port count.
     */
    [[nodiscard]] size_t count() const noexcept { return count_; }

private:
    uint16_t base_port_;
    size_t count_;
    IoReadHandler read_;
    IoWriteHandler write_;
    size_t installed_count_;

    void install() {
        for (size_t i = 0; i < count_; i++) {
            uint16_t port = static_cast<uint16_t>(base_port_ + i);
            if (internal::register_io_port(port, read_, write_)) {
                installed_count_++;
            } else {
                break;  // Stop on first failure
            }
        }
    }
};

} // namespace aibox
