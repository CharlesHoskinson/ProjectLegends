# AIBox: Embeddable DOSBox-X

AIBox is the embedding layer for DOSBox-X that provides a C FFI for programmatic control of DOS emulation. It supports headless operation, deterministic stepping, and frame serialization.

## Overview

**Purpose:** Embed DOS emulation into applications through a stable C API.

**Features:**
- Headless operation (no GUI required)
- Deterministic stepping via `aibox_step(handle, ms)`
- Text-mode frame capture
- Batch input execution
- Screenshot capture with annotation support
- C FFI with ABI versioning

## Architecture

```
                ┌──────────────────┐
                │ Host Application │
                └────────┬─────────┘
                         │ C FFI
                         ▼
┌────────────────────────────────────────────────┐
│             AIBox Layer (C++23)                │
│                                                │
│  ffi_core · ffi_llm · ffi_vision · ffi_events  │
│                                                │
│  ┌──────────────────────────────────────────┐  │
│  │ DOSBoxContext                            │  │
│  │   TimingState · CpuState · MemoryState   │  │
│  │   MixerState  · VgaState · PicState      │  │
│  └──────────────────────────────────────────┘  │
└────────────────────────┬───────────────────────┘
                         │
                         ▼
┌────────────────────────────────────────────────┐
│              DOSBox-X Core                     │
│  CPU · Memory · VGA · DOS Kernel · Hardware    │
└────────────────────────────────────────────────┘
```

## Memory Model

Each context owns independent memory state:

```
DOSBoxContext
└── MemoryState
    ├── base         - Guest RAM buffer
    ├── size         - Allocated bytes
    ├── phandlers[]  - Page handler array
    ├── mhandles[]   - EMS/XMS handle array
    ├── a20          - A20 gate state
    ├── lfb          - Linear framebuffer region
    └── lfb_mmio     - MMIO region
```

Context-aware memory functions take `DOSBoxContext*` as the first parameter:

```c
// Per-context memory access
uint8_t val = phys_readb(ctx, addr);
phys_writeb(ctx, addr, val);

// Per-context page handlers
MEM_SetPageHandler(ctx, page, count, handler);

// Per-context allocation
MemHandle h = MEM_AllocatePages(ctx, pages, sequence);
```

## Quick Start

### Prerequisites

- GCC 13+ or Clang 16+ (C++23)
- CMake 3.20+
- Ninja (recommended)

### Building

```bash
mkdir cmake-build && cd cmake-build
cmake .. -G Ninja
cmake --build .
```

### Basic Usage

```c
#include <aibox/ffi_core.h>
#include <aibox/ffi_llm.h>

int main() {
    if (!aibox_check_abi_compatible(AIBOX_ABI_VERSION)) {
        return 1;
    }

    aibox_handle_t handle = aibox_create("dosbox.conf");
    if (!handle) return 1;

    if (aibox_init(handle) != AIBOX_OK) {
        aibox_destroy(handle);
        return 1;
    }

    // Run for 1 second
    aibox_step(handle, 1000);

    // Get screen as text
    char buffer[32768];
    size_t len;
    aibox_llm_get_frame(handle, AIBOX_LLM_FORMAT_CANONICAL_TEXT,
                        buffer, sizeof(buffer), &len);
    printf("%s\n", buffer);

    // Type command
    aibox_llm_type(handle, "DIR\n", 0);
    aibox_step(handle, 500);

    aibox_destroy(handle);
    return 0;
}
```

## API Modules

### ffi_core.h - Lifecycle

| Function | Description |
|----------|-------------|
| `aibox_create()` | Create instance |
| `aibox_init()` | Initialize |
| `aibox_step()` | Run N milliseconds |
| `aibox_destroy()` | Free resources |
| `aibox_memory_read/write()` | Guest memory access |
| `aibox_key_event()` | Keyboard input |
| `aibox_mouse_event()` | Mouse input |

### ffi_llm.h - Frame Serialization

| Function | Description |
|----------|-------------|
| `aibox_llm_get_frame()` | Screen as text/JSON |
| `aibox_llm_execute_batch()` | Batch actions |
| `aibox_llm_type()` | Type text |
| `aibox_llm_special_key()` | Special key |

### ffi_vision.h - Screenshot

| Function | Description |
|----------|-------------|
| `aibox_vision_capture_*()` | Capture framebuffer |
| `aibox_vision_add_overlay()` | Add bounding box |
| `aibox_vision_export_coco()` | COCO format |
| `aibox_vision_export_yolo()` | YOLO format |

## Error Handling

| Range | Category |
|-------|----------|
| 0 | Success |
| 1-99 | Common errors |
| 100-199 | Hardware errors |
| 200-299 | LLM errors |
| 300-399 | Vision errors |
| 900-999 | Internal errors |

```c
const char* msg = aibox_last_error(handle);
const char* desc = aibox_error_message(error_code);
```

## Thread Safety

- **Core API:** Single-threaded
- **Error storage:** Thread-local
- **Handle registry:** Thread-safe

## License

GPL-2.0 (same as DOSBox-X)

## See Also

- [include/aibox/](include/aibox/) - Header files
- [tests/unit/](tests/unit/) - Test examples
