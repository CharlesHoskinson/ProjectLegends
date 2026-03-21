// SPDX-License-Identifier: MIT
#include <legends_ipc/framebuffer_shm.h>
#include <cstring>
#include <string>
#include <string_view>

namespace legends_ipc {

void FramebufferShm::map_pointers() {
    auto d = region_.data();
    header_   = reinterpret_cast<FramebufferHeader*>(d.data());
    buf_size_ = static_cast<size_t>(header_->max_width) * header_->max_height * 4;
    buffer0_  = d.data() + sizeof(FramebufferHeader);
    buffer1_  = buffer0_ + buf_size_;
}

std::expected<FramebufferShm, IpcError>
FramebufferShm::create(std::string_view name, uint32_t max_width, uint32_t max_height) {
    if (max_width == 0 || max_height == 0)
        return std::unexpected(IpcError::InvalidArgument);

    size_t total = required_size(max_width, max_height);
    auto region = SharedMemoryRegion::create(std::string(name) + "_fb", total);
    if (!region.has_value())
        return std::unexpected(region.error());

    FramebufferShm fb;
    fb.region_ = std::move(*region);
    fb.map_pointers();

    fb.header_->max_width  = max_width;
    fb.header_->max_height = max_height;
    fb.header_->frame_index.store(0, std::memory_order_relaxed);
    fb.header_->active_buffer.store(0, std::memory_order_relaxed);
    fb.header_->current_width  = 0;
    fb.header_->current_height = 0;

    return fb;
}

std::expected<FramebufferShm, IpcError>
FramebufferShm::open(std::string_view name, uint32_t max_width, uint32_t max_height) {
    if (max_width == 0 || max_height == 0)
        return std::unexpected(IpcError::InvalidArgument);

    size_t total = required_size(max_width, max_height);
    auto region = SharedMemoryRegion::open(std::string(name) + "_fb", total);
    if (!region.has_value())
        return std::unexpected(region.error());

    FramebufferShm fb;
    fb.region_ = std::move(*region);
    fb.map_pointers();
    return fb;
}

std::span<uint8_t> FramebufferShm::begin_write() {
    uint32_t active = header_->active_buffer.load(std::memory_order_acquire);
    // Write to the non-active buffer
    uint8_t* target = (active == 0) ? buffer1_ : buffer0_;
    return {target, buf_size_};
}

void FramebufferShm::end_write(uint32_t width, uint32_t height) {
    uint32_t active = header_->active_buffer.load(std::memory_order_acquire);
    uint32_t next = (active == 0) ? 1 : 0;

    header_->current_width  = width;
    header_->current_height = height;
    header_->active_buffer.store(next, std::memory_order_release);
    header_->frame_index.fetch_add(1, std::memory_order_release);
}

std::optional<FrameData> FramebufferShm::read_if_new(uint64_t last_index) const {
    uint64_t idx = header_->frame_index.load(std::memory_order_acquire);
    if (idx <= last_index)
        return std::nullopt;

    uint32_t active = header_->active_buffer.load(std::memory_order_acquire);
    const uint8_t* buf = (active == 0) ? buffer0_ : buffer1_;

    uint32_t w = header_->current_width;
    uint32_t h = header_->current_height;
    size_t pixel_bytes = static_cast<size_t>(w) * h * 4;

    return FrameData{
        .pixels = {buf, pixel_bytes},
        .width = w,
        .height = h,
        .frame_index = idx
    };
}

uint32_t FramebufferShm::max_width() const { return header_->max_width; }
uint32_t FramebufferShm::max_height() const { return header_->max_height; }

} // namespace legends_ipc
