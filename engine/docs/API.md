# AIBox API Reference

Complete API documentation for the AIBox FFI layer.

## Table of Contents

1. [Core Lifecycle API](#core-lifecycle-api)
2. [Memory Access API](#memory-access-api)
3. [Input Injection API](#input-injection-api)
4. [LLM API](#llm-api)
5. [Vision API](#vision-api)
6. [Error Handling](#error-handling)
7. [C++ Internal API](#cpp-internal-api)

---

## Core Lifecycle API

Header: `<aibox/ffi_core.h>`

### ABI Versioning

```c
// Check before using the library
uint32_t version = aibox_get_abi_version();
int compatible = aibox_check_abi_compatible(AIBOX_ABI_VERSION);
const char* version_str = aibox_get_version_string();
```

### Instance Management

#### aibox_create

```c
aibox_handle_t aibox_create(const char* config_path);
```

Create a new emulator instance.

**Parameters:**
- `config_path`: Path to DOSBox configuration file, or NULL for defaults

**Returns:** Handle to instance, or NULL on failure

**Example:**
```c
aibox_handle_t handle = aibox_create("game.conf");
if (!handle) {
    fprintf(stderr, "Create failed: %s\n", aibox_last_error(NULL));
}
```

#### aibox_init

```c
aibox_error_t aibox_init(aibox_handle_t handle);
```

Initialize the emulator. Must be called after `aibox_create()` and before `aibox_step()`.

**Returns:** `AIBOX_OK` on success

#### aibox_step

```c
int32_t aibox_step(aibox_handle_t handle, uint32_t milliseconds);
```

Run emulator for specified virtual time. This is deterministic - always runs exactly the specified amount of virtual time regardless of wall-clock time.

**Parameters:**
- `handle`: Emulator handle
- `milliseconds`: Virtual milliseconds to execute

**Returns:** Number of instructions executed, or negative error code

**Example:**
```c
// Run for 100ms of virtual time
int32_t instructions = aibox_step(handle, 100);
if (instructions < 0) {
    fprintf(stderr, "Step failed: %s\n", aibox_last_error(handle));
}
```

#### aibox_stop

```c
aibox_error_t aibox_stop(aibox_handle_t handle);
```

Signal emulator to stop after current instruction. Does not destroy the instance.

#### aibox_destroy

```c
void aibox_destroy(aibox_handle_t handle);
```

Destroy instance and free all resources. Handle becomes invalid after this call.

### Handle Validation

```c
aibox_handle_status_t aibox_validate_handle(aibox_handle_t handle);
```

Validation status codes:
- `AIBOX_HANDLE_VALID` (0): Handle is valid
- `AIBOX_HANDLE_NULL` (-1): Handle is null
- `AIBOX_HANDLE_INVALID_GENERATION` (-2): Use-after-free detected
- `AIBOX_HANDLE_WRONG_TYPE` (-3): Type mismatch
- `AIBOX_HANDLE_DESTROYED` (-4): Handle was freed

---

## Memory Access API

Header: `<aibox/ffi_core.h>`

### aibox_memory_read

```c
int32_t aibox_memory_read(
    aibox_handle_t handle,
    uint32_t address,
    void* buffer,
    size_t size
);
```

Read from guest memory.

**Returns:** Number of bytes read, or negative error code

### aibox_memory_write

```c
int32_t aibox_memory_write(
    aibox_handle_t handle,
    uint32_t address,
    const void* data,
    size_t size
);
```

Write to guest memory.

**Returns:** Number of bytes written, or negative error code

### aibox_memory_size

```c
size_t aibox_memory_size(aibox_handle_t handle);
```

**Returns:** Guest memory size in bytes

---

## Input Injection API

Header: `<aibox/ffi_core.h>`

### aibox_key_event

```c
aibox_error_t aibox_key_event(
    aibox_handle_t handle,
    uint8_t scancode,
    int is_pressed
);
```

Inject keyboard event using AT scan codes.

**Parameters:**
- `scancode`: AT keyboard scan code
- `is_pressed`: 1 for key down, 0 for key up

### aibox_mouse_event

```c
aibox_error_t aibox_mouse_event(
    aibox_handle_t handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
);
```

Inject mouse event.

**Parameters:**
- `delta_x`, `delta_y`: Relative movement
- `buttons`: Bitmask (bit 0=left, 1=right, 2=middle)

---

## LLM API

Header: `<aibox/ffi_llm.h>`

### Frame Retrieval

#### aibox_llm_get_frame

```c
aibox_error_t aibox_llm_get_frame(
    aibox_handle_t handle,
    aibox_llm_format_t format,
    char* output_buffer,
    size_t output_capacity,
    size_t* output_len_out
);
```

Get current screen as text or JSON.

**Formats:**
- `AIBOX_LLM_FORMAT_JSON` (0): Full JSON with metadata
- `AIBOX_LLM_FORMAT_CANONICAL_TEXT` (1): Text with box borders
- `AIBOX_LLM_FORMAT_RAW_TEXT` (2): Raw text, no borders
- `AIBOX_LLM_FORMAT_COMPACT_JSON` (3): Minified JSON

**Example:**
```c
char buffer[32768];
size_t len;
aibox_error_t err = aibox_llm_get_frame(
    handle,
    AIBOX_LLM_FORMAT_CANONICAL_TEXT,
    buffer, sizeof(buffer), &len
);
if (err == AIBOX_OK) {
    printf("%.*s\n", (int)len, buffer);
}
```

#### aibox_llm_get_diff_frame

```c
aibox_error_t aibox_llm_get_diff_frame(
    aibox_handle_t handle,
    aibox_llm_format_t format,
    char* output_buffer,
    size_t output_capacity,
    size_t* output_len_out
);
```

Get only changed portions since last frame. Reduces token count for LLM input.

### Batch Execution

#### aibox_llm_execute_batch

```c
aibox_error_t aibox_llm_execute_batch(
    aibox_handle_t handle,
    const char* json_request,
    size_t json_request_len,
    char* json_response_out,
    size_t json_response_capacity,
    size_t* json_response_len_out
);
```

Execute multiple actions in a single call.

**Request JSON:**
```json
{
  "actions": [
    {"type": "type", "text": "DIR\\n"},
    {"type": "wait", "ms": 500},
    {"type": "special_key", "key": "Enter"}
  ],
  "timeout_ms": 5000,
  "return_frame": true,
  "stop_on_error": true
}
```

**Response JSON:**
```json
{
  "success": true,
  "actions_executed": 3,
  "results": [
    {"index": 0, "status": "ok", "duration_us": 1234},
    {"index": 1, "status": "ok", "duration_us": 500000},
    {"index": 2, "status": "ok", "duration_us": 567}
  ],
  "total_duration_us": 501801,
  "frame": "..."
}
```

### Convenience Functions

```c
// Type text (supports \n for Enter, \t for Tab)
aibox_error_t aibox_llm_type(
    aibox_handle_t handle,
    const char* text,
    uint32_t delay_between_ms
);

// Send special key ("Enter", "Escape", "F1", "CtrlC", etc.)
aibox_error_t aibox_llm_special_key(
    aibox_handle_t handle,
    const char* key_name
);

// Wait for duration
aibox_error_t aibox_llm_wait(
    aibox_handle_t handle,
    uint32_t milliseconds
);

// Click at text coordinates
aibox_error_t aibox_llm_click(
    aibox_handle_t handle,
    uint8_t column,
    uint8_t row,
    const char* button  // "left", "right", "middle"
);
```

### State Queries

```c
// Get video mode and dimensions
int32_t aibox_llm_get_video_mode(
    aibox_handle_t handle,
    uint8_t* columns,
    uint8_t* rows
);

// Get cursor position
aibox_error_t aibox_llm_get_cursor(
    aibox_handle_t handle,
    uint8_t* column,
    uint8_t* row,
    int* visible
);

// Check if in text mode (vs graphics)
int32_t aibox_llm_is_text_mode(aibox_handle_t handle);

// Estimate token count for current frame
int32_t aibox_llm_estimate_tokens(aibox_handle_t handle);
```

---

## Vision API

Header: `<aibox/ffi_vision.h>`

### Screenshot Capture

```c
// Capture as raw RGBA
aibox_error_t aibox_vision_capture_rgba(
    aibox_handle_t handle,
    uint8_t* buffer,
    size_t buffer_capacity,
    aibox_vision_capture_info_t* info_out
);

// Capture as PNG
aibox_error_t aibox_vision_capture_png(
    aibox_handle_t handle,
    uint8_t* buffer,
    size_t buffer_capacity,
    size_t* size_out
);

// Capture as JPEG
aibox_error_t aibox_vision_capture_jpeg(
    aibox_handle_t handle,
    uint8_t* buffer,
    size_t buffer_capacity,
    size_t* size_out,
    int quality  // 1-100
);
```

### Overlays

```c
// Add bounding box overlay
aibox_error_t aibox_vision_add_overlay(
    aibox_handle_t handle,
    uint32_t overlay_id,
    const aibox_vision_bbox_t* bbox,
    const char* label,
    uint32_t color_rgba
);

// Remove overlay
aibox_error_t aibox_vision_remove_overlay(
    aibox_handle_t handle,
    uint32_t overlay_id
);

// Clear all overlays
aibox_error_t aibox_vision_clear_overlays(aibox_handle_t handle);
```

### Annotation Export

```c
// Export as COCO format JSON
aibox_error_t aibox_vision_export_coco(
    aibox_handle_t handle,
    char* buffer,
    size_t buffer_capacity,
    size_t* size_out
);

// Export as YOLO format (one line per box)
aibox_error_t aibox_vision_export_yolo(
    aibox_handle_t handle,
    char* buffer,
    size_t buffer_capacity,
    size_t* size_out
);
```

---

## Error Handling

Header: `<aibox/ffi_core.h>`

### Error Codes

```c
typedef enum {
    AIBOX_OK = 0,

    // Common Errors (1-99)
    AIBOX_ERR_INVALID_PARAM = 1,
    AIBOX_ERR_INVALID_HANDLE = 2,
    AIBOX_ERR_NOT_INITIALIZED = 3,
    AIBOX_ERR_ALREADY_INITIALIZED = 4,
    AIBOX_ERR_INVALID_STATE = 5,
    AIBOX_ERR_BUFFER_TOO_SMALL = 6,
    AIBOX_ERR_OUT_OF_MEMORY = 7,
    AIBOX_ERR_TIMEOUT = 11,

    // Hardware Errors (100-199)
    AIBOX_ERR_CPU = 100,
    AIBOX_ERR_DMA = 101,
    AIBOX_ERR_MEMORY = 102,
    AIBOX_ERR_CONFIG = 103,
    AIBOX_ERR_IO_PORT = 104,

    // LLM Errors (200-299)
    AIBOX_ERR_LLM_INVALID_JSON = 200,
    AIBOX_ERR_LLM_BATCH_TOO_LARGE = 201,
    AIBOX_ERR_LLM_ACTION_FAILED = 202,
    AIBOX_ERR_LLM_NOT_TEXT_MODE = 203,

    // Vision Errors (300-399)
    AIBOX_ERR_VISION_NO_FRAMEBUFFER = 300,
    AIBOX_ERR_VISION_NOT_DIRTY = 301,
    AIBOX_ERR_VISION_INVALID_FORMAT = 302,

    // Fatal Errors (900-999)
    AIBOX_ERR_FATAL = 998,
    AIBOX_ERR_INTERNAL = 999
} aibox_error_t;
```

### Error Functions

```c
// Get last error message for handle
const char* aibox_last_error(aibox_handle_t handle);

// Get human-readable description
const char* aibox_error_message(aibox_error_t error);

// Thread-local error storage (ffi.h)
const char* aibox_ffi_last_error(void);
void aibox_ffi_clear_error(void);
const char* aibox_ffi_error_string(int code);
```

---

## C++ Internal API

Header: `<aibox/ffi.h>`

### Exception-Safe Wrapper

```cpp
namespace aibox::ffi {

// Wrap any function with exception handling
template<typename F>
int safe_call(F&& func) noexcept;

// Thread-local error storage
void set_error(const char* msg);
void set_error_fmt(std::format_string<Args...> fmt, Args&&... args);
const char* get_error() noexcept;
void clear_error() noexcept;
bool error_truncated() noexcept;

}
```

**Example:**
```cpp
extern "C" aibox_error_t my_ffi_function(int* out) {
    return aibox::ffi::safe_call([&]() {
        if (!out) {
            aibox::ffi::set_error("Null output pointer");
            return AIBOX_ERR_INVALID_PARAM;
        }
        *out = compute_value();  // May throw
        return AIBOX_OK;
    });
}
```

### Exception Types

All exceptions derive from `EmulatorException`:

| Exception | Error Code | Description |
|-----------|------------|-------------|
| `IllegalCpuStateException` | `AIBOX_ERR_CPU` | Invalid CPU state |
| `DmaException` | `AIBOX_ERR_DMA` | DMA transfer error |
| `MemoryAccessException` | `AIBOX_ERR_MEMORY` | Bad memory access |
| `ConfigException` | `AIBOX_ERR_CONFIG` | Configuration error |
| `IoPortException` | `AIBOX_ERR_IO_PORT` | I/O port error |
| `FatalException` | `AIBOX_ERR_FATAL` | Unrecoverable error |
| `CallbackException` | `AIBOX_ERR_INTERNAL` | Callback failure |

### Result Type

```cpp
#include <aibox/error.h>

template<typename T>
using Result = std::expected<T, Error>;

// Usage
Result<int> compute() {
    if (error_condition) {
        return std::unexpected(Error(ErrorCode::InvalidParam, "bad input"));
    }
    return 42;
}

auto result = compute();
if (result) {
    use(*result);
} else {
    log_error(result.error());
}
```

---

## Thread Safety Notes

1. **Core API functions** are NOT thread-safe. Call from single thread.
2. **Handle registry** is internally synchronized (thread-safe allocation/free).
3. **Error storage** is thread-local. Each thread has independent error state.
4. **Callbacks** must be called from the emulation thread only.

## Memory Management

1. **Handles** are reference-counted internally. Always call `aibox_destroy()`.
2. **Buffers** are caller-owned. Ensure sufficient capacity.
3. **Strings** returned by `aibox_last_error()` are valid until next API call.
4. **C++ objects** use RAII. `CallbackToken` auto-unregisters on destruction.
