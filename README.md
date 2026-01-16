# Project Legends

**Embeddable x86 Emulation Framework**

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-GPL--2.0-blue)]()
[![C++ Standard](https://img.shields.io/badge/C%2B%2B-23-blue)]()
[![Tests](https://img.shields.io/badge/tests-4000%2B%20passing-brightgreen)]()

---

## Overview

Project Legends is an embeddable x86 emulation framework built on a refactored DOSBox-X engine. It provides a C API for embedding DOS/x86 emulation into applications that require deterministic execution and programmatic control.

The core problem this solves: existing emulators are standalone applications. They spawn threads, use global state, call `exit()` on errors, and assume they own the process. This makes them unsuitable for embedding into larger systems where you need multiple instances, state serialization, or reproducible execution.

Project Legends treats the emulator as a library. The host application controls execution timing, input injection, and state capture. All mutable state lives in an explicit context structure, enabling multiple independent instances.

**Features:**

- **Context-based state** - No global variables, multiple instances supported
- **Explicit memory model** - Per-context RAM, page handlers, and memory allocation
- **Deterministic stepping** - `step(ctx, ms)` advances emulation predictably
- **Platform abstraction** - Runs headless or with SDL2/SDL3 backends
- **C API** - Stable ABI for Rust, Python, or any FFI-capable language

---

## Architecture

```
                     ┌───────────────────┐
                     │  Host Application │
                     └─────────┬─────────┘
                               │ C ABI
                               ▼
┌──────────────────────────────────────────────────────────────┐
│                       legends_embed.h                        │
│          Lifecycle · Stepping · Capture · Input · State      │
└──────────────────────────────┬───────────────────────────────┘
                               │
               ┌───────────────┴───────────────┐
               ▼                               ▼
┌─────────────────────────┐     ┌─────────────────────────────┐
│      AIBox Layer        │     │           PAL               │
│                         │     │                             │
│  ffi_core    ffi_llm    │     │  ITiming    IDisplay        │
│  ffi_vision  ffi_events │     │  IAudio     IInput          │
│                         │     │                             │
│  DOSBoxContext          │     │  Backends:                  │
│  InstanceRegistry       │     │  Headless · SDL2 · SDL3     │
└────────────┬────────────┘     └─────────────────────────────┘
             │
             ▼
┌──────────────────────────────────────────────────────────────┐
│                    DOSBox-X Core Engine                      │
│                                                              │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │   CPU    │  │ Hardware │  │ DOS/BIOS │  │   GUI    │     │
│  │ x86 emu  │  │ PIC, PIT │  │ INT 21h  │  │  Menu    │     │
│  │ prot mode│  │ VGA, SB  │  │ FileSys  │  │  Mapper  │     │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘     │
└──────────────────────────────────────────────────────────────┘
```

---

## Memory Model

Each `DOSBoxContext` owns its memory subsystem. This enables multiple independent instances without shared state.

### Memory Architecture

```
┌─────────────────────────────────────────────────────────────┐
│ DOSBoxContext                                               │
│                                                             │
│   ┌─────────────────────────────────────────────────────┐   │
│   │ MemoryState                                         │   │
│   │                                                     │   │
│   │   base ──────────────► Guest RAM buffer             │   │
│   │   size                 Allocated bytes              │   │
│   │                                                     │   │
│   │   phandlers[] ───────► PageHandler* per page        │   │
│   │   mhandles[] ────────► EMS/XMS allocation chain     │   │
│   │                                                     │   │
│   │   a20.enabled          A20 gate for 8086 wrap       │   │
│   │   lfb, lfb_mmio        VGA framebuffer regions      │   │
│   │                                                     │   │
│   │   pages                Total memory pages           │   │
│   │   handler_pages        Handler array size           │   │
│   │   address_bits         CPU address bus width        │   │
│   └─────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

### Components

| Component | Description |
|-----------|-------------|
| `base` | Guest RAM buffer pointer (replaces global `MemBase`) |
| `size` | Allocated size in bytes |
| `phandlers[]` | Page handler array for memory-mapped I/O |
| `mhandles[]` | Memory handle array for EMS/XMS allocation tracking |
| `a20` | A20 gate state for 8086 address wrapping |
| `lfb/lfb_mmio` | Linear framebuffer regions for VGA |

### Context-Aware API

All memory functions have context-aware overloads:

```c
// Old global API (still available for compatibility)
uint8_t val = phys_readb(0x12345);
MEM_SetPageHandler(0xA0, 16, handler);

// New context-aware API
uint8_t val = phys_readb(ctx, 0x12345);
MEM_SetPageHandler(ctx, 0xA0, 16, handler);
```

Context-aware functions (38 total):
- **Core**: `MEM_AllocateForContext`, `MEM_FreeForContext`, `MEM_SyncFromContext`, `MEM_SyncToContext`
- **A20**: `MEM_A20_Enabled(ctx)`, `MEM_A20_Enable(ctx, enabled)`
- **Pages**: `MEM_TotalPages(ctx)`, `MEM_PageMask(ctx)`, `MEM_PageMaskActive(ctx)`
- **Physical R/W**: `phys_readb/w/d(ctx)`, `phys_writeb/w/d(ctx)`
- **Block R/W**: `MEM_BlockRead/Write(ctx)`, `MEM_BlockCopy(ctx)`
- **Handlers**: `MEM_SetPageHandler(ctx)`, `MEM_GetPageHandler(ctx)`, `MEM_RegisterHandler(ctx)`
- **Allocation**: `MEM_AllocatePages(ctx)`, `MEM_ReleasePages(ctx)`, `MEM_FreeLargest(ctx)`
- **Mapping**: `MEM_map_RAM_physmem(ctx)`, `MEM_map_ROM_physmem(ctx)`, `MEM_unmap_physmem(ctx)`

### Memory Lifecycle

```c
DOSBoxContext ctx;

// 1. Allocate memory for context
MEM_AllocateForContext(&ctx, 16384);  // 16MB
// Allocates: ctx.memory.base, ctx.memory.phandlers, ctx.memory.mhandles

// 2. Use memory
phys_writeb(&ctx, 0x7C00, 0xEB);
MEM_SetPageHandler(&ctx, 0xA0, 32, vga_handler);
MemHandle h = MEM_AllocatePages(&ctx, 4, true);

// 3. Free memory
MEM_FreeForContext(&ctx);
```

### Instance Isolation

Two contexts operate on independent memory:

```c
DOSBoxContext ctx1, ctx2;

MEM_AllocateForContext(&ctx1, 16384);
MEM_AllocateForContext(&ctx2, 4096);

phys_writeb(&ctx1, 0x1000, 0xAA);
phys_writeb(&ctx2, 0x1000, 0xBB);

// Independent - no cross-contamination
assert(phys_readb(&ctx1, 0x1000) == 0xAA);
assert(phys_readb(&ctx2, 0x1000) == 0xBB);
```

---

## Global State Migration

The original DOSBox-X used global variables extensively. These have been migrated to `DOSBoxContext`:

| Status | Count | Description |
|--------|-------|-------------|
| **Migrated** | 49 | Moved to DOSBoxContext (74%) |
| **Pending** | 17 | Remaining for full multi-instance (26%) |
| **Total** | 66 | Tracked in `globals_registry.yaml` |

The registry tracks each global's:
- Migration status
- Target context location
- Determinism relevance

---

## Quick Start

### Building

```bash
cmake -B build -G Ninja -DLEGENDS_BUILD_TESTS=ON
cmake --build build
ctest --test-dir build --output-on-failure
```

### Embedding

```c
#include <legends/legends_embed.h>

int main() {
    legends_handle handle;
    legends_config_t config = LEGENDS_CONFIG_INIT;

    legends_create(&config, &handle);

    // Run for 1 second
    for (int i = 0; i < 100; i++) {
        legends_step_ms(handle, 10, NULL);
    }

    legends_text_input(handle, "DIR\n");
    legends_step_ms(handle, 500, NULL);

    legends_destroy(handle);
    return 0;
}
```

---

## FFI Modules

### ffi_core.h - Lifecycle

```c
aibox_handle_t aibox_create(const char* config);
int aibox_init(aibox_handle_t handle);
int aibox_step(aibox_handle_t handle, uint32_t ms);
int aibox_destroy(aibox_handle_t handle);
int aibox_memory_read(aibox_handle_t h, uint32_t addr, void* buf, size_t len);
int aibox_memory_write(aibox_handle_t h, uint32_t addr, const void* buf, size_t len);
```

### ffi_llm.h - Text Frame Serialization

```c
int aibox_llm_get_frame(aibox_handle_t h, int format, char* buf, size_t len, size_t* out);
int aibox_llm_execute_batch(aibox_handle_t h, const char* json_actions);
int aibox_llm_type(aibox_handle_t h, const char* text, uint32_t flags);
```

### ffi_vision.h - Screenshot Capture

```c
int aibox_vision_capture_rgb(aibox_handle_t h, uint8_t* buf, size_t len, uint16_t* w, uint16_t* h);
int aibox_vision_add_overlay(aibox_handle_t h, const aibox_bbox_t* bbox);
int aibox_vision_export_coco(aibox_handle_t h, char* json, size_t len);
```

---

## Error Codes

| Code | Value | Description |
|------|-------|-------------|
| `LEGENDS_OK` | 0 | Success |
| `LEGENDS_ERR_NULL_HANDLE` | -1 | Null handle |
| `LEGENDS_ERR_NULL_POINTER` | -2 | Null pointer argument |
| `LEGENDS_ERR_NOT_INITIALIZED` | -4 | Instance not initialized |
| `LEGENDS_ERR_BUFFER_TOO_SMALL` | -6 | Buffer too small |
| `LEGENDS_ERR_OUT_OF_MEMORY` | -11 | Allocation failed |
| `LEGENDS_ERR_WRONG_THREAD` | -14 | Called from wrong thread |

---

## Platform Abstraction Layer

The PAL decouples the engine from platform-specific code:

| Interface | Purpose |
|-----------|---------|
| `ITiming` | Wall clock for throttling |
| `IDisplay` | Frame upload, mode setting |
| `IAudio` | Push-based audio output |
| `IInput` | Event polling |

**Backends:** Headless (no dependencies), SDL2, SDL3

---

## Project Structure

```
ProjectLegends/
├── engine/                     # DOSBox-X core
│   ├── include/
│   │   ├── dosbox/             # Context, handles, platform interfaces
│   │   │   └── dosbox_context.h
│   │   └── mem.h               # Memory API
│   ├── src/
│   │   ├── hardware/memory.cpp # Memory implementation
│   │   ├── cpu/                # x86 emulation
│   │   ├── dos/                # DOS kernel
│   │   └── hardware/           # Device emulation
│   └── globals_registry.yaml
│
├── include/legends/            # Public API
│   └── legends_embed.h
│
├── src/pal/                    # Platform backends
│
├── tests/
│
└── spec/
    ├── CONTRACT.md             # API contract
    └── tla/                    # Formal specifications
```

---

## License

GPL-2.0, consistent with DOSBox-X.

---

## Acknowledgments

- **DOSBox Team** - Original DOSBox emulator
- **DOSBox-X Team** - Extended platform support

---

*Copyright (c) 2024-2026 Charles Hoskinson*
