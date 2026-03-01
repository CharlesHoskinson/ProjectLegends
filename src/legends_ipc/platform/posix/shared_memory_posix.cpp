// SPDX-License-Identifier: MIT
#ifndef _WIN32

#include <legends_ipc/shared_memory.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <cstring>
#include <utility>

namespace legends_ipc {

SharedMemoryRegion::~SharedMemoryRegion() { cleanup(); }

SharedMemoryRegion::SharedMemoryRegion(SharedMemoryRegion&& other) noexcept
    : name_(std::move(other.name_))
    , data_(other.data_)
    , size_(other.size_)
    , fd_(other.fd_)
{
    other.data_ = nullptr;
    other.size_ = 0;
    other.fd_ = -1;
}

SharedMemoryRegion& SharedMemoryRegion::operator=(SharedMemoryRegion&& other) noexcept {
    if (this != &other) {
        cleanup();
        name_ = std::move(other.name_);
        data_ = other.data_;
        size_ = other.size_;
        fd_ = other.fd_;
        other.data_ = nullptr;
        other.size_ = 0;
        other.fd_ = -1;
    }
    return *this;
}

void SharedMemoryRegion::cleanup() {
    if (data_) {
        munmap(data_, size_);
        data_ = nullptr;
    }
    if (fd_ >= 0) {
        close(fd_);
        fd_ = -1;
    }
    size_ = 0;
}

std::expected<SharedMemoryRegion, IpcError>
SharedMemoryRegion::create(const std::string& name, size_t size) {
    if (size == 0)
        return std::unexpected(IpcError::InvalidArgument);

    std::string shm_name = "/legends_shm_" + name;

    int fd = shm_open(shm_name.c_str(), O_CREAT | O_RDWR, 0600);
    if (fd < 0)
        return std::unexpected(IpcError::OutOfMemory);

    if (ftruncate(fd, static_cast<off_t>(size)) != 0) {
        close(fd);
        shm_unlink(shm_name.c_str());
        return std::unexpected(IpcError::OutOfMemory);
    }

    void* ptr = mmap(nullptr, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (ptr == MAP_FAILED) {
        close(fd);
        shm_unlink(shm_name.c_str());
        return std::unexpected(IpcError::OutOfMemory);
    }

    memset(ptr, 0, size);

    SharedMemoryRegion region;
    region.name_ = name;
    region.data_ = static_cast<uint8_t*>(ptr);
    region.size_ = size;
    region.fd_ = fd;
    return std::expected<SharedMemoryRegion, IpcError>{std::in_place, std::move(region)};
}

std::expected<SharedMemoryRegion, IpcError>
SharedMemoryRegion::open(const std::string& name, size_t size) {
    if (size == 0)
        return std::unexpected(IpcError::InvalidArgument);

    std::string shm_name = "/legends_shm_" + name;

    int fd = shm_open(shm_name.c_str(), O_RDWR, 0600);
    if (fd < 0)
        return std::unexpected(IpcError::NotConnected);

    void* ptr = mmap(nullptr, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (ptr == MAP_FAILED) {
        close(fd);
        return std::unexpected(IpcError::OutOfMemory);
    }

    SharedMemoryRegion region;
    region.name_ = name;
    region.data_ = static_cast<uint8_t*>(ptr);
    region.size_ = size;
    region.fd_ = fd;
    return std::expected<SharedMemoryRegion, IpcError>{std::in_place, std::move(region)};
}

} // namespace legends_ipc

#endif // !_WIN32
