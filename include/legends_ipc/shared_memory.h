// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_SHARED_MEMORY_H
#define LEGENDS_IPC_SHARED_MEMORY_H

#include <cstdint>
#include <expected>
#include <span>
#include <string>
#include <legends_ipc/ipc_error.h>

namespace legends_ipc {

class AudioRingBuffer;
class FramebufferShm;

// RAII, move-only shared memory region.
// Platform-specific create/open in platform/{windows,posix}/.
class SharedMemoryRegion {
public:
    ~SharedMemoryRegion();

    SharedMemoryRegion(const SharedMemoryRegion&) = delete;
    SharedMemoryRegion& operator=(const SharedMemoryRegion&) = delete;
    SharedMemoryRegion(SharedMemoryRegion&& other) noexcept;
    SharedMemoryRegion& operator=(SharedMemoryRegion&& other) noexcept;

    // Create a new shared memory region.
    static std::expected<SharedMemoryRegion, IpcError>
    create(const std::string& name, size_t size);

    // Open an existing shared memory region by name.
    static std::expected<SharedMemoryRegion, IpcError>
    open(const std::string& name, size_t size);

    std::span<uint8_t> data() { return {data_, size_}; }
    std::span<const uint8_t> data() const { return {data_, size_}; }
    size_t size() const { return size_; }
    const std::string& name() const { return name_; }

    // Default-constructs an empty (unmapped) region.
private:
    friend class AudioRingBuffer;
    friend class FramebufferShm;

    // Default-constructs an empty (unmapped) region.
    SharedMemoryRegion() = default;

    std::string name_;
    uint8_t* data_ = nullptr;
    size_t size_    = 0;

#ifdef _WIN32
    void* handle_  = nullptr; // HANDLE
    void* mapping_ = nullptr; // MapViewOfFile result
#else
    int fd_ = -1;
#endif

    void cleanup();
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_SHARED_MEMORY_H
