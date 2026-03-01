// SPDX-License-Identifier: MIT
#ifdef _WIN32

#include <legends_ipc/shared_memory.h>
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <string>
#include <utility>

namespace legends_ipc {

SharedMemoryRegion::~SharedMemoryRegion() { cleanup(); }

SharedMemoryRegion::SharedMemoryRegion(SharedMemoryRegion&& other) noexcept
    : name_(std::move(other.name_))
    , data_(other.data_)
    , size_(other.size_)
    , handle_(other.handle_)
    , mapping_(other.mapping_)
{
    other.data_ = nullptr;
    other.size_ = 0;
    other.handle_ = nullptr;
    other.mapping_ = nullptr;
}

SharedMemoryRegion& SharedMemoryRegion::operator=(SharedMemoryRegion&& other) noexcept {
    if (this != &other) {
        cleanup();
        name_ = std::move(other.name_);
        data_ = other.data_;
        size_ = other.size_;
        handle_ = other.handle_;
        mapping_ = other.mapping_;
        other.data_ = nullptr;
        other.size_ = 0;
        other.handle_ = nullptr;
        other.mapping_ = nullptr;
    }
    return *this;
}

void SharedMemoryRegion::cleanup() {
    if (mapping_) {
        UnmapViewOfFile(mapping_);
        mapping_ = nullptr;
    }
    if (handle_) {
        CloseHandle(handle_);
        handle_ = nullptr;
    }
    data_ = nullptr;
    size_ = 0;
}

std::expected<SharedMemoryRegion, IpcError>
SharedMemoryRegion::create(const std::string& name, size_t size) {
    if (size == 0)
        return std::unexpected(IpcError::InvalidArgument);

    std::string mapped_name = "Local\\legends_shm_" + name;

    HANDLE h = CreateFileMappingA(
        INVALID_HANDLE_VALUE, nullptr, PAGE_READWRITE,
        static_cast<DWORD>(size >> 32),
        static_cast<DWORD>(size & 0xFFFFFFFF),
        mapped_name.c_str());

    if (!h)
        return std::unexpected(IpcError::OutOfMemory);

    void* ptr = MapViewOfFile(h, FILE_MAP_ALL_ACCESS, 0, 0, size);
    if (!ptr) {
        CloseHandle(h);
        return std::unexpected(IpcError::OutOfMemory);
    }

    // Zero-initialize
    memset(ptr, 0, size);

    SharedMemoryRegion region;
    region.name_ = name;
    region.data_ = static_cast<uint8_t*>(ptr);
    region.size_ = size;
    region.handle_ = h;
    region.mapping_ = ptr;
    return std::expected<SharedMemoryRegion, IpcError>{std::in_place, std::move(region)};
}

std::expected<SharedMemoryRegion, IpcError>
SharedMemoryRegion::open(const std::string& name, size_t size) {
    if (size == 0)
        return std::unexpected(IpcError::InvalidArgument);

    std::string mapped_name = "Local\\legends_shm_" + name;

    HANDLE h = OpenFileMappingA(FILE_MAP_ALL_ACCESS, FALSE, mapped_name.c_str());
    if (!h)
        return std::unexpected(IpcError::NotConnected);

    void* ptr = MapViewOfFile(h, FILE_MAP_ALL_ACCESS, 0, 0, size);
    if (!ptr) {
        CloseHandle(h);
        return std::unexpected(IpcError::OutOfMemory);
    }

    SharedMemoryRegion region;
    region.name_ = name;
    region.data_ = static_cast<uint8_t*>(ptr);
    region.size_ = size;
    region.handle_ = h;
    region.mapping_ = ptr;
    return std::expected<SharedMemoryRegion, IpcError>{std::in_place, std::move(region)};
}

} // namespace legends_ipc

#endif // _WIN32
