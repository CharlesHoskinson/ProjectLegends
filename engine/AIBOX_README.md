# AIBox: LLM-Controllable DOSBox-X

AIBox is a modernization layer for DOSBox-X that enables LLM agents to interact with DOS applications through a clean C/C++ FFI. It provides headless operation, deterministic stepping, and token-efficient frame serialization.

## Overview

**Purpose:** Enable AI agents to control and observe DOS applications running inside DOSBox-X.

**Key Features:**
- **Headless operation** - No GUI required, runs as a library
- **Deterministic stepping** - `aibox_step(handle, ms)` for reproducible execution
- **Text-mode frame serialization** - Token-efficient screen capture for LLMs
- **Batch action execution** - Multiple inputs in a single API call
- **Vision overlays** - Annotate screenshots with bounding boxes (COCO/YOLO)
- **C FFI with ABI versioning** - Stable interface for Rust/Python bindings

## Architecture

```
+-------------------------------------------------------------+
|                    Host Application (Rust/Python/C)         |
|  +-------------+  +-------------+  +-------------------+    |
|  | LLM Agent   |  | GPU Render  |  | Game-Specific     |    |
|  | Controller  |  | (wgpu/GL)   |  | Logic             |    |
|  +-------------+  +-------------+  +-------------------+    |
+---------------------------------|---------------------------+
                                  | FFI Boundary
+---------------------------------v---------------------------+
|                    AIBox Layer (C++23)                      |
|  +-------------+  +-------------+  +-------------------+    |
|  | ffi_core    |  | ffi_llm     |  | ffi_vision        |    |
|  | (lifecycle) |  | (frames)    |  | (screenshots)     |    |
|  +-------------+  +-------------+  +-------------------+    |
+---------------------------------|---------------------------+
                                  |
+---------------------------------v---------------------------+
|                    DOSBox-X Core                            |
|  CPU | Memory | VGA | DOS Kernel | Hardware Devices         |
+---------------------------------|---------------------------+
                                  |
+---------------------------------v---------------------------+
|                    DOS Guest Application                    |
+-------------------------------------------------------------+
```

## Quick Start

### Prerequisites

- GCC 13+ or Clang 16+ (C++23 support required)
- CMake 3.20+
- Ninja (recommended) or Make

### Building

```bash
cd C:\aibox\dosbox-x
mkdir cmake-build && cd cmake-build
cmake .. -G Ninja
cmake --build .
```

This produces:
- `libaibox_core.a` - Static library
- `tests/aibox_unit_tests.exe` - Unit tests (1045+ tests)

### Running Tests

```bash
./tests/aibox_unit_tests.exe
```

### Basic Usage (C)

```c
#include <aibox/ffi_core.h>
#include <aibox/ffi_llm.h>

int main() {
    // Check ABI compatibility
    if (!aibox_check_abi_compatible(AIBOX_ABI_VERSION)) {
        fprintf(stderr, "ABI mismatch!\n");
        return 1;
    }

    // Create and initialize
    aibox_handle_t handle = aibox_create("dosbox.conf");
    if (!handle) {
        fprintf(stderr, "Failed to create: %s\n", aibox_last_error(NULL));
        return 1;
    }

    if (aibox_init(handle) != AIBOX_OK) {
        fprintf(stderr, "Failed to init: %s\n", aibox_last_error(handle));
        aibox_destroy(handle);
        return 1;
    }

    // Run for 1 second (deterministic)
    aibox_step(handle, 1000);

    // Get current frame as text
    char buffer[32768];
    size_t len;
    aibox_llm_get_frame(handle, AIBOX_LLM_FORMAT_CANONICAL_TEXT,
                        buffer, sizeof(buffer), &len);
    printf("Screen:\n%s\n", buffer);

    // Type a command
    aibox_llm_type(handle, "DIR\n", 0);
    aibox_step(handle, 500);

    // Cleanup
    aibox_destroy(handle);
    return 0;
}
```

## API Modules

### ffi_core.h - Lifecycle and Memory

| Function | Description |
|----------|-------------|
| `aibox_create()` | Create emulator instance |
| `aibox_init()` | Initialize emulator |
| `aibox_step()` | Run for N milliseconds (deterministic) |
| `aibox_destroy()` | Free all resources |
| `aibox_memory_read/write()` | Access guest memory |
| `aibox_key_event()` | Inject keyboard input |
| `aibox_mouse_event()` | Inject mouse input |

### ffi_llm.h - LLM Integration

| Function | Description |
|----------|-------------|
| `aibox_llm_get_frame()` | Get screen as text/JSON |
| `aibox_llm_execute_batch()` | Execute action batch |
| `aibox_llm_type()` | Type text (convenience) |
| `aibox_llm_special_key()` | Send special key |
| `aibox_llm_estimate_tokens()` | Estimate token count |

### ffi_vision.h - Screenshot and Overlays

| Function | Description |
|----------|-------------|
| `aibox_vision_capture_*()` | Capture framebuffer |
| `aibox_vision_add_overlay()` | Add bounding box overlay |
| `aibox_vision_export_coco()` | Export COCO annotations |
| `aibox_vision_export_yolo()` | Export YOLO annotations |

## Error Handling

All functions return `aibox_error_t` (unified error codes):

| Range | Category |
|-------|----------|
| 0 | Success (AIBOX_OK) |
| 1-99 | Common errors (invalid param, handle, state) |
| 100-199 | Hardware/emulation errors |
| 200-299 | LLM subsystem errors |
| 300-399 | Vision subsystem errors |
| 900-999 | Fatal/internal errors |

Get error details:
```c
const char* msg = aibox_last_error(handle);
const char* desc = aibox_error_message(error_code);
```

## C++23 Features Used

- `std::expected` for Result types
- `std::format` for string formatting
- `std::span` for memory views
- `std::ranges` for container algorithms
- `std::source_location` for error context
- gsl-lite contracts (`gsl_Expects`, `gsl_Ensures`)

## Thread Safety

- **Core API:** Not thread-safe. Use from single thread.
- **Error storage:** Thread-local (each thread has own error state)
- **Handle registry:** Thread-safe (internal locking)

## License

DOSBox-X is licensed under the GNU General Public License v2.0.
AIBox modifications follow the same license.

## See Also

- [docs/API.md](docs/API.md) - Detailed API reference
- [tests/unit/](tests/unit/) - Unit test examples
- [include/aibox/](include/aibox/) - Header files
