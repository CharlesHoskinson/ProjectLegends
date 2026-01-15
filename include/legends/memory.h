/**
 * @file memory.h
 * @brief RAII wrappers for guest memory management.
 *
 * Provides:
 * - GuestMemory: Owning RAII wrapper for emulated guest RAM
 * - MemoryView: Non-owning view for FFI boundaries
 * - MemoryRegion: Named region with metadata
 *
 * Requirements implemented:
 * - REQ-MEM-001: RAII for all dynamically allocated memory
 * - REQ-MEM-002: Bounds-checked access in debug builds
 * - REQ-MEM-003: Smart pointers for single-owner resources
 * - REQ-MEM-004: Zero-initialize all memory buffers
 * - REQ-MEM-010: Release memory on destruction
 * - REQ-MEM-020: Bounds checking in debug builds
 * - REQ-MEM-021: Unchecked access in release builds
 * - REQ-MEM-022: MemoryView validity guarantees
 * - REQ-MEM-040: Throw std::bad_alloc on allocation failure
 * - REQ-MEM-041: Throw MemoryAccessException on out-of-bounds
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include "exceptions.h"

#include <gsl-lite/gsl-lite.hpp>
#include <memory>
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <span>
#include <string>

namespace legends {

// Type alias for span (C++23 std::span)
template<typename T>
using Span = std::span<T>;

// ─────────────────────────────────────────────────────────────────────────────
// Forward declarations
// ─────────────────────────────────────────────────────────────────────────────

class GuestMemory;
class MemoryView;

// ─────────────────────────────────────────────────────────────────────────────
// GuestMemory - Owning RAII wrapper for guest RAM
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief RAII wrapper for guest memory allocation.
 *
 * Owns the memory buffer representing the emulated machine's RAM.
 * Provides bounds-checked and unchecked access methods.
 *
 * @note Non-copyable, movable. Moving transfers ownership.
 * @note All memory is zero-initialized on allocation (REQ-MEM-004).
 * @note In debug builds, all accesses are bounds-checked.
 * @note In release builds, unchecked methods skip validation.
 *
 * @invariant data_ != nullptr implies size_ > 0
 * @invariant After move, source has size_ == 0 and data_ == nullptr
 *
 * Example:
 * @code
 *   GuestMemory mem(16 * 1024 * 1024);  // 16MB
 *   mem.write8(0x1000, 0x42);
 *   uint8_t val = mem.read8(0x1000);
 *
 *   // Hot path (after bounds verified externally)
 *   for (size_t i = 0; i < verified_len; i++) {
 *       mem.write8_unchecked(base + i, data[i]);
 *   }
 * @endcode
 */
class GuestMemory {
public:
    // ─────────────────────────────────────────────────────────────
    // Construction and destruction
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Construct guest memory of specified size.
     *
     * Allocates and zero-initializes the memory buffer.
     *
     * @param size_bytes Size in bytes (typically 1MB-64MB for DOS)
     * @throws std::bad_alloc if allocation fails (REQ-MEM-040)
     * @pre size_bytes > 0
     * @post valid() == true
     * @post All bytes are zero
     */
    explicit GuestMemory(size_t size_bytes)
        : data_(std::make_unique<uint8_t[]>(size_bytes))
        , size_(size_bytes)
    {
        gsl_Expects(size_bytes > 0);
        // Zero-initialize (REQ-MEM-004)
        std::memset(data_.get(), 0, size_bytes);
        gsl_Ensures(valid());
    }

    /**
     * @brief Default constructor - creates invalid (empty) memory.
     * @post valid() == false
     * @post size() == 0
     */
    GuestMemory() noexcept : data_(nullptr), size_(0) {}

    /**
     * @brief Destructor - automatically releases memory.
     *
     * unique_ptr handles deallocation (REQ-MEM-010).
     */
    ~GuestMemory() = default;

    // Non-copyable
    GuestMemory(const GuestMemory&) = delete;
    GuestMemory& operator=(const GuestMemory&) = delete;

    // Movable
    /**
     * @brief Move constructor - transfers ownership.
     * @param other Source memory (will be invalidated)
     * @post other.valid() == false
     */
    GuestMemory(GuestMemory&& other) noexcept
        : data_(std::move(other.data_))
        , size_(other.size_)
    {
        other.size_ = 0;
    }

    /**
     * @brief Move assignment - transfers ownership.
     * @param other Source memory (will be invalidated)
     * @return Reference to this
     * @post other.valid() == false
     */
    GuestMemory& operator=(GuestMemory&& other) noexcept {
        if (this != &other) {
            data_ = std::move(other.data_);
            size_ = other.size_;
            other.size_ = 0;
        }
        return *this;
    }

    // ─────────────────────────────────────────────────────────────
    // Bounds-checked access (debug builds, API boundaries)
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Read byte with bounds checking.
     * @param addr Guest physical address
     * @return Byte value at address
     * @throws MemoryAccessException if addr >= size (debug builds)
     */
    [[nodiscard]] uint8_t read8(uint32_t addr) const {
        validate_address(addr, 1);
        return data_[addr];
    }

    /**
     * @brief Write byte with bounds checking.
     * @param addr Guest physical address
     * @param val Value to write
     * @throws MemoryAccessException if addr >= size (debug builds)
     */
    void write8(uint32_t addr, uint8_t val) {
        validate_address(addr, 1);
        data_[addr] = val;
    }

    /**
     * @brief Read 16-bit word with bounds checking (little-endian).
     * @param addr Guest physical address
     * @return Word value at address
     * @throws MemoryAccessException if access crosses boundary
     */
    [[nodiscard]] uint16_t read16(uint32_t addr) const {
        validate_address(addr, 2);
        return static_cast<uint16_t>(data_[addr]) |
               (static_cast<uint16_t>(data_[addr + 1]) << 8);
    }

    /**
     * @brief Write 16-bit word with bounds checking (little-endian).
     * @param addr Guest physical address
     * @param val Value to write
     * @throws MemoryAccessException if access crosses boundary
     */
    void write16(uint32_t addr, uint16_t val) {
        validate_address(addr, 2);
        data_[addr] = static_cast<uint8_t>(val);
        data_[addr + 1] = static_cast<uint8_t>(val >> 8);
    }

    /**
     * @brief Read 32-bit dword with bounds checking (little-endian).
     * @param addr Guest physical address
     * @return Dword value at address
     * @throws MemoryAccessException if access crosses boundary
     */
    [[nodiscard]] uint32_t read32(uint32_t addr) const {
        validate_address(addr, 4);
        return static_cast<uint32_t>(data_[addr]) |
               (static_cast<uint32_t>(data_[addr + 1]) << 8) |
               (static_cast<uint32_t>(data_[addr + 2]) << 16) |
               (static_cast<uint32_t>(data_[addr + 3]) << 24);
    }

    /**
     * @brief Write 32-bit dword with bounds checking (little-endian).
     * @param addr Guest physical address
     * @param val Value to write
     * @throws MemoryAccessException if access crosses boundary
     */
    void write32(uint32_t addr, uint32_t val) {
        validate_address(addr, 4);
        data_[addr] = static_cast<uint8_t>(val);
        data_[addr + 1] = static_cast<uint8_t>(val >> 8);
        data_[addr + 2] = static_cast<uint8_t>(val >> 16);
        data_[addr + 3] = static_cast<uint8_t>(val >> 24);
    }

    // ─────────────────────────────────────────────────────────────
    // Unchecked access (hot paths, after external validation)
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Read byte WITHOUT bounds checking.
     * @warning Caller must ensure addr < size()
     * @param addr Guest physical address (must be valid)
     * @return Byte value at address
     */
    [[nodiscard]] uint8_t read8_unchecked(uint32_t addr) const noexcept {
        return data_[addr];
    }

    /**
     * @brief Write byte WITHOUT bounds checking.
     * @warning Caller must ensure addr < size()
     * @param addr Guest physical address (must be valid)
     * @param val Value to write
     */
    void write8_unchecked(uint32_t addr, uint8_t val) noexcept {
        data_[addr] = val;
    }

    /**
     * @brief Read 16-bit word WITHOUT bounds checking (little-endian).
     * @warning Caller must ensure addr + 1 < size()
     */
    [[nodiscard]] uint16_t read16_unchecked(uint32_t addr) const noexcept {
        return static_cast<uint16_t>(data_[addr]) |
               (static_cast<uint16_t>(data_[addr + 1]) << 8);
    }

    /**
     * @brief Write 16-bit word WITHOUT bounds checking (little-endian).
     * @warning Caller must ensure addr + 1 < size()
     */
    void write16_unchecked(uint32_t addr, uint16_t val) noexcept {
        data_[addr] = static_cast<uint8_t>(val);
        data_[addr + 1] = static_cast<uint8_t>(val >> 8);
    }

    /**
     * @brief Read 32-bit dword WITHOUT bounds checking (little-endian).
     * @warning Caller must ensure addr + 3 < size()
     */
    [[nodiscard]] uint32_t read32_unchecked(uint32_t addr) const noexcept {
        return static_cast<uint32_t>(data_[addr]) |
               (static_cast<uint32_t>(data_[addr + 1]) << 8) |
               (static_cast<uint32_t>(data_[addr + 2]) << 16) |
               (static_cast<uint32_t>(data_[addr + 3]) << 24);
    }

    /**
     * @brief Write 32-bit dword WITHOUT bounds checking (little-endian).
     * @warning Caller must ensure addr + 3 < size()
     */
    void write32_unchecked(uint32_t addr, uint32_t val) noexcept {
        data_[addr] = static_cast<uint8_t>(val);
        data_[addr + 1] = static_cast<uint8_t>(val >> 8);
        data_[addr + 2] = static_cast<uint8_t>(val >> 16);
        data_[addr + 3] = static_cast<uint8_t>(val >> 24);
    }

    // ─────────────────────────────────────────────────────────────
    // Block operations
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Copy block from guest memory to host buffer.
     * @param addr Starting guest address
     * @param dest Destination buffer
     * @param len Number of bytes to copy
     * @throws MemoryAccessException if range exceeds bounds
     * @pre dest != nullptr || len == 0
     */
    void read_block(uint32_t addr, uint8_t* dest, size_t len) const {
        if (len == 0) return;
        gsl_Expects(dest != nullptr);
        validate_address(addr, len);
        std::memcpy(dest, &data_[addr], len);
    }

    /**
     * @brief Copy block from host buffer to guest memory.
     * @param addr Starting guest address
     * @param src Source buffer
     * @param len Number of bytes to copy
     * @throws MemoryAccessException if range exceeds bounds
     * @pre src != nullptr || len == 0
     */
    void write_block(uint32_t addr, const uint8_t* src, size_t len) {
        if (len == 0) return;
        gsl_Expects(src != nullptr);
        validate_address(addr, len);
        std::memcpy(&data_[addr], src, len);
    }

    /**
     * @brief Fill memory region with a value.
     * @param addr Starting guest address
     * @param val Value to fill with
     * @param len Number of bytes to fill
     * @throws MemoryAccessException if range exceeds bounds
     */
    void fill(uint32_t addr, uint8_t val, size_t len) {
        if (len == 0) return;
        validate_address(addr, len);
        std::memset(&data_[addr], val, len);
    }

    /**
     * @brief Copy within guest memory (handles overlap).
     * @param dest_addr Destination address
     * @param src_addr Source address
     * @param len Number of bytes to copy
     * @throws MemoryAccessException if either range exceeds bounds
     */
    void copy(uint32_t dest_addr, uint32_t src_addr, size_t len) {
        if (len == 0) return;
        validate_address(dest_addr, len);
        validate_address(src_addr, len);
        std::memmove(&data_[dest_addr], &data_[src_addr], len);
    }

    // ─────────────────────────────────────────────────────────────
    // View accessors
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Get raw pointer to memory base.
     * @note For FFI interop only. Prefer span-based access.
     * @return Pointer to first byte, or nullptr if invalid
     */
    [[nodiscard]] uint8_t* data() noexcept { return data_.get(); }

    /**
     * @brief Get const raw pointer to memory base.
     */
    [[nodiscard]] const uint8_t* data() const noexcept { return data_.get(); }

    /**
     * @brief Total memory size in bytes.
     * @return Size in bytes
     */
    [[nodiscard]] size_t size() const noexcept { return size_; }

    /**
     * @brief Check if memory is allocated and valid.
     * @return true if memory is allocated
     */
    [[nodiscard]] bool valid() const noexcept {
        return data_ != nullptr && size_ > 0;
    }

    /**
     * @brief Check if address is within bounds.
     * @param addr Address to check
     * @param access_size Size of access (1, 2, or 4)
     * @return true if access is within bounds
     */
    [[nodiscard]] bool in_bounds(uint32_t addr, size_t access_size = 1) const noexcept {
        return addr < size_ && (addr + access_size) <= size_;
    }

    /**
     * @brief Get span view of entire memory.
     * @return Span covering all memory
     */
    [[nodiscard]] Span<uint8_t> as_span() noexcept {
        return Span<uint8_t>(data_.get(), size_);
    }

    /**
     * @brief Get const span view of entire memory.
     */
    [[nodiscard]] Span<const uint8_t> as_span() const noexcept {
        return Span<const uint8_t>(data_.get(), size_);
    }

    /**
     * @brief Get span view of a region.
     * @param offset Starting offset
     * @param len Length of region
     * @return Span of the region
     * @throws MemoryAccessException if region exceeds bounds
     */
    [[nodiscard]] Span<uint8_t> subspan(uint32_t offset, size_t len) {
        validate_address(offset, len);
        return Span<uint8_t>(&data_[offset], len);
    }

    /**
     * @brief Get const span view of a region.
     */
    [[nodiscard]] Span<const uint8_t> subspan(uint32_t offset, size_t len) const {
        validate_address(offset, len);
        return Span<const uint8_t>(&data_[offset], len);
    }

private:
    std::unique_ptr<uint8_t[]> data_;
    size_t size_;

    /**
     * @brief Validate address and access size.
     *
     * In debug builds, throws if out of bounds.
     * In release builds, this is a no-op for performance.
     *
     * @param addr Starting address
     * @param access_size Size of access
     * @throws MemoryAccessException if out of bounds (debug only)
     */
    void validate_address(uint32_t addr, size_t access_size) const {
#if defined(NDEBUG) && !defined(LEGENDS_ALWAYS_BOUNDS_CHECK)
        // Release: no validation for performance (REQ-MEM-021)
        (void)addr;
        (void)access_size;
#else
        // Debug or forced checking: full validation (REQ-MEM-020)
        if (addr >= size_ || (static_cast<size_t>(addr) + access_size) > size_) {
            throw MemoryAccessException(addr, access_size);
        }
#endif
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// MemoryView - Non-owning view for FFI boundaries
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Non-owning view of memory for FFI boundaries.
 *
 * Does NOT manage lifetime. Caller must ensure underlying
 * memory outlives the view (REQ-MEM-022).
 *
 * Use cases:
 * - Passing memory regions to C APIs
 * - Temporary views for function parameters
 * - Interfacing with external libraries
 *
 * @warning Not safe to store long-term. Use for function parameters only.
 *
 * Example:
 * @code
 *   void process_data(MemoryView view) {
 *       for (size_t i = 0; i < view.size(); i++) {
 *           process_byte(view.data()[i]);
 *       }
 *   }
 *
 *   GuestMemory mem(1024);
 *   process_data(mem);  // Implicit conversion
 * @endcode
 */
class MemoryView {
public:
    /**
     * @brief Construct from raw pointer and size.
     * @param ptr Pointer to memory (may be nullptr)
     * @param size Size in bytes
     */
    MemoryView(uint8_t* ptr, size_t size) noexcept
        : ptr_(ptr), size_(size) {}

    /**
     * @brief Construct from const pointer and size.
     */
    MemoryView(const uint8_t* ptr, size_t size) noexcept
        : ptr_(const_cast<uint8_t*>(ptr)), size_(size), const_(true) {}

    /**
     * @brief Implicit conversion from GuestMemory.
     * @param mem Guest memory reference
     */
    MemoryView(GuestMemory& mem) noexcept
        : ptr_(mem.data()), size_(mem.size()) {}

    /**
     * @brief Implicit conversion from const GuestMemory.
     */
    MemoryView(const GuestMemory& mem) noexcept
        : ptr_(const_cast<uint8_t*>(mem.data()))
        , size_(mem.size())
        , const_(true) {}

    /**
     * @brief Default constructor - creates empty view.
     */
    MemoryView() noexcept : ptr_(nullptr), size_(0) {}

    // ─────────────────────────────────────────────────────────────
    // Accessors
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Get raw pointer to memory.
     * @return Pointer to first byte, or nullptr if empty
     */
    [[nodiscard]] uint8_t* data() noexcept { return ptr_; }

    /**
     * @brief Get const pointer to memory.
     */
    [[nodiscard]] const uint8_t* data() const noexcept { return ptr_; }

    /**
     * @brief Get size in bytes.
     */
    [[nodiscard]] size_t size() const noexcept { return size_; }

    /**
     * @brief Check if view is empty.
     */
    [[nodiscard]] bool empty() const noexcept { return size_ == 0; }

    /**
     * @brief Check if view is valid (non-null, non-empty).
     */
    [[nodiscard]] bool valid() const noexcept {
        return ptr_ != nullptr && size_ > 0;
    }

    /**
     * @brief Check if view is const.
     */
    [[nodiscard]] bool is_const() const noexcept { return const_; }

    /**
     * @brief Get span view.
     */
    [[nodiscard]] Span<uint8_t> as_span() noexcept {
        return Span<uint8_t>(ptr_, size_);
    }

    /**
     * @brief Get const span view.
     */
    [[nodiscard]] Span<const uint8_t> as_span() const noexcept {
        return Span<const uint8_t>(ptr_, size_);
    }

    /**
     * @brief Get subview.
     * @param offset Starting offset
     * @param len Length (or remaining if larger)
     */
    [[nodiscard]] MemoryView subview(size_t offset, size_t len = SIZE_MAX) const noexcept {
        if (offset >= size_) {
            return MemoryView();  // Empty view
        }
        size_t actual_len = std::min(len, size_ - offset);
        return MemoryView(ptr_ + offset, actual_len);
    }

    // ─────────────────────────────────────────────────────────────
    // Element access
    // ─────────────────────────────────────────────────────────────

    /**
     * @brief Access byte by index (unchecked).
     */
    [[nodiscard]] uint8_t& operator[](size_t idx) noexcept {
        return ptr_[idx];
    }

    /**
     * @brief Access byte by index (const, unchecked).
     */
    [[nodiscard]] const uint8_t& operator[](size_t idx) const noexcept {
        return ptr_[idx];
    }

private:
    uint8_t* ptr_;
    size_t size_;
    bool const_ = false;
};

// ─────────────────────────────────────────────────────────────────────────────
// MemoryRegion - Named region with metadata
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Memory region access flags.
 */
enum class MemoryAccess : uint8_t {
    None = 0,
    Read = 1,
    Write = 2,
    Execute = 4,
    ReadWrite = Read | Write,
    All = Read | Write | Execute
};

/**
 * @brief Bitwise OR for MemoryAccess flags.
 */
inline MemoryAccess operator|(MemoryAccess a, MemoryAccess b) noexcept {
    return static_cast<MemoryAccess>(
        static_cast<uint8_t>(a) | static_cast<uint8_t>(b));
}

/**
 * @brief Bitwise AND for MemoryAccess flags.
 */
inline MemoryAccess operator&(MemoryAccess a, MemoryAccess b) noexcept {
    return static_cast<MemoryAccess>(
        static_cast<uint8_t>(a) & static_cast<uint8_t>(b));
}

/**
 * @brief Check if flag is set.
 */
inline bool has_flag(MemoryAccess flags, MemoryAccess flag) noexcept {
    return (flags & flag) == flag;
}

/**
 * @brief Named memory region with metadata.
 *
 * Represents a logical region within guest memory with
 * a name, base address, size, and access flags.
 *
 * Use cases:
 * - Conventional memory (0x00000-0x9FFFF)
 * - Video memory (0xA0000-0xBFFFF)
 * - ROM BIOS (0xF0000-0xFFFFF)
 */
class MemoryRegion {
public:
    /**
     * @brief Construct a memory region.
     * @param name Region name (e.g., "Conventional", "Video")
     * @param base Base address in guest memory
     * @param size Size in bytes (must fit in uint32_t)
     * @param access Access flags
     * @pre size <= UINT32_MAX (region must fit in 32-bit address space)
     * @pre base + size <= UINT32_MAX (region must not overflow)
     */
    MemoryRegion(std::string name, uint32_t base, size_t size,
                 MemoryAccess access = MemoryAccess::ReadWrite)
        : name_(std::move(name))
        , base_(base)
        , size_(size)
        , access_(access)
    {
        gsl_Expects(size <= UINT32_MAX);
        gsl_Expects(static_cast<uint64_t>(base) + size <= UINT32_MAX);
    }

    // Accessors
    [[nodiscard]] const std::string& name() const noexcept { return name_; }
    [[nodiscard]] uint32_t base() const noexcept { return base_; }
    [[nodiscard]] size_t size() const noexcept { return size_; }
    [[nodiscard]] uint32_t end() const noexcept {
        return base_ + static_cast<uint32_t>(size_);
    }
    [[nodiscard]] MemoryAccess access() const noexcept { return access_; }

    /**
     * @brief Check if address is within this region.
     */
    [[nodiscard]] bool contains(uint32_t addr) const noexcept {
        return addr >= base_ && addr < end();
    }

    /**
     * @brief Check if range overlaps this region.
     */
    [[nodiscard]] bool overlaps(uint32_t addr, size_t len) const noexcept {
        uint32_t range_end = addr + static_cast<uint32_t>(len);
        return addr < end() && range_end > base_;
    }

    /**
     * @brief Check if read access is allowed.
     */
    [[nodiscard]] bool can_read() const noexcept {
        return has_flag(access_, MemoryAccess::Read);
    }

    /**
     * @brief Check if write access is allowed.
     */
    [[nodiscard]] bool can_write() const noexcept {
        return has_flag(access_, MemoryAccess::Write);
    }

    /**
     * @brief Check if execute access is allowed.
     */
    [[nodiscard]] bool can_execute() const noexcept {
        return has_flag(access_, MemoryAccess::Execute);
    }

private:
    std::string name_;
    uint32_t base_;
    size_t size_;
    MemoryAccess access_;
};

} // namespace legends
