// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_FRAMEBUFFER_SHM_H
#define LEGENDS_IPC_FRAMEBUFFER_SHM_H

#include <atomic>
#include <cstdint>
#include <expected>
#include <optional>
#include <span>
#include <string_view>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/shared_memory.h>

namespace legends_ipc {

// Shared memory layout for the framebuffer header (32 bytes).
struct FramebufferHeader {
    uint32_t max_width;                   // 0
    uint32_t max_height;                  // 4
    std::atomic<uint64_t> frame_index;    // 8
    std::atomic<uint32_t> active_buffer;  // 16
    uint32_t current_width;               // 20
    uint32_t current_height;              // 24
    uint32_t padding;                     // 28
};                                        // 32 total

static_assert(sizeof(FramebufferHeader) == 32);

struct FrameData {
    std::span<const uint8_t> pixels;
    uint32_t width;
    uint32_t height;
    uint64_t frame_index;
};

// Double-buffered framebuffer over shared memory.
// Writer (engine): begin_write() -> write pixels -> end_write(w,h)
// Reader (proxy):  read_if_new(last_idx) -> optional<FrameData>
class FramebufferShm {
public:
<<<<<<< HEAD
    [[nodiscard]] static std::expected<FramebufferShm, IpcError>
    create(const std::string& name, uint32_t max_width, uint32_t max_height);

    [[nodiscard]] static std::expected<FramebufferShm, IpcError>
    open(const std::string& name, uint32_t max_width, uint32_t max_height);
=======
    static std::expected<FramebufferShm, IpcError>
    create(std::string_view name, uint32_t max_width, uint32_t max_height);

    static std::expected<FramebufferShm, IpcError>
    open(std::string_view name, uint32_t max_width, uint32_t max_height);
>>>>>>> worktree-agent-a4ab30fc

    // Writer: get buffer to write into (the non-active buffer).
    [[nodiscard]] std::span<uint8_t> begin_write();

    // Writer: flip active buffer and update dimensions + frame index.
    void end_write(uint32_t width, uint32_t height);

    // Reader: read the active buffer if frame_index > last_index.
    [[nodiscard]] std::optional<FrameData> read_if_new(uint64_t last_index) const;

    [[nodiscard]] uint32_t max_width() const;
    [[nodiscard]] uint32_t max_height() const;

    [[nodiscard]] static size_t required_size(uint32_t max_w, uint32_t max_h) {
        return sizeof(FramebufferHeader) + 2 * static_cast<size_t>(max_w) * max_h * 4;
    }

private:
    FramebufferShm() = default;
    SharedMemoryRegion region_;
    FramebufferHeader* header_ = nullptr;
    uint8_t* buffer0_ = nullptr;
    uint8_t* buffer1_ = nullptr;
    size_t buf_size_   = 0;

    void map_pointers();
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_FRAMEBUFFER_SHM_H
