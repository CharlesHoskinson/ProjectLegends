# Project Legends

**A Modern Embeddable x86 Emulation Framework for AI-Driven Computing**

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-GPL--2.0-blue)]()
[![C++ Standard](https://img.shields.io/badge/C%2B%2B-23-blue)]()
[![Tests](https://img.shields.io/badge/tests-120%20passing-brightgreen)]()

---

## Overview

Project Legends is a modernized, embeddable x86 emulation framework designed for deterministic execution and AI integration. Built on the foundation of DOSBox-X, it provides a clean C API boundary for embedding DOS/x86 emulation into modern applications, with a particular focus on:

- **Deterministic Execution**: Bit-perfect reproducibility across runs
- **LLM Integration**: Structured I/O optimized for language model interaction
- **Vision Model Support**: Screen capture with semantic annotations
- **Formal Verification**: TLA+ specifications for critical subsystems

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Host Application (Rust/Python/C++)           │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼ (Stable C ABI)
┌─────────────────────────────────────────────────────────────────┐
│                    legends_embed.h (C API)                      │
│   legends_step(), legends_capture_text(), legends_key_event()   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                 Legends Core (Modern C++23)                     │
│   MachineContext, LLM Serializer, Vision Capture, Event Bus    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼ (Compile Firewall)
┌─────────────────────────────────────────────────────────────────┐
│               Legacy DOSBox-X Core (Minimal Patches)            │
│                    CPU, Memory, Devices                         │
└─────────────────────────────────────────────────────────────────┘
```

## Key Features

### Embeddable C API

A clean, stable C ABI for embedding the emulator:

```c
#include <legends/legends_embed.h>

// Create emulator instance
legends_handle handle;
legends_create(NULL, &handle);

// Step execution
legends_step_result_t result;
legends_step_ms(handle, 100, &result);

// Capture screen
size_t cell_count;
legends_capture_text(handle, NULL, 0, &cell_count, NULL);

// Inject input
legends_key_event(handle, 0x1E, 1);  // Press 'A'

// Save/restore state
legends_save_state(handle, buffer, size, &actual);
legends_load_state(handle, buffer, size);

// Cleanup
legends_destroy(handle);
```

### Deterministic Execution

Every execution is reproducible:

```c
// Same inputs always produce same outputs
legends_config_t config = LEGENDS_CONFIG_INIT;
config.deterministic = 1;

legends_create(&config, &handle);

// Verify determinism
int is_deterministic;
legends_verify_determinism(handle, 10000, &is_deterministic);
assert(is_deterministic);
```

### LLM-Optimized I/O

Structured output for language models:

- **Text Frames**: CP437 character + attribute pairs
- **Semantic Actions**: High-level action descriptors
- **Diff Compression**: Efficient delta encoding
- **JSON Serialization**: Machine-readable output

### Vision Model Integration

Screen capture with annotations:

- **RGB24 Capture**: Pre-scaler framebuffer access
- **Dirty Tracking**: Efficient change detection
- **Overlay System**: Annotation rendering
- **Palette Support**: VGA palette extraction

### Save-State Determinism

Full state serialization per TLA+ specification:

- **Event Queue**: Pending timer/interrupt events
- **CPU State**: Registers, flags, mode
- **PIC State**: IRR, IMR, ISR for master/slave
- **DMA State**: Channel configuration
- **SHA-256 Hashing**: State verification

## Building

### Prerequisites

- CMake 3.20+
- C++23 compiler (GCC 13+, Clang 16+, MSVC 2022)
- GoogleTest (fetched automatically)

### Build Commands

```bash
# Configure
cmake -B build -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON

# Build
cmake --build build

# Run tests
./build/tests/legends_unit_tests
./build/tests/legends_abi_test
```

### Build Options

| Option | Default | Description |
|--------|---------|-------------|
| `LEGENDS_BUILD_TESTS` | OFF | Build unit tests |
| `LEGENDS_HEADLESS` | OFF | Headless mode (no GUI) |
| `LEGENDS_LIBRARY_MODE` | OFF | Build as static library |

## API Reference

### Lifecycle Functions

| Function | Description |
|----------|-------------|
| `legends_get_api_version()` | Get API version for ABI checks |
| `legends_create()` | Create emulator instance (single per process) |
| `legends_destroy()` | Destroy instance and free resources |
| `legends_reset()` | Soft reset (preserves config) |
| `legends_get_config()` | Query current configuration |

### Stepping Functions

| Function | Description |
|----------|-------------|
| `legends_step_ms()` | Step by emulated milliseconds |
| `legends_step_cycles()` | Step by exact CPU cycles |
| `legends_get_emu_time()` | Get current emulated time |
| `legends_get_total_cycles()` | Get total cycles executed |

### Frame Capture Functions

| Function | Description |
|----------|-------------|
| `legends_capture_text()` | Capture text mode screen |
| `legends_capture_rgb()` | Capture RGB24 framebuffer |
| `legends_is_frame_dirty()` | Check if frame changed |
| `legends_get_cursor()` | Get cursor position |

### Input Injection Functions

| Function | Description |
|----------|-------------|
| `legends_key_event()` | Inject AT scancode |
| `legends_key_event_ext()` | Inject extended scancode (E0 prefix) |
| `legends_text_input()` | Type UTF-8 text string |
| `legends_mouse_event()` | Inject mouse movement/buttons |

### Save/Load Functions

| Function | Description |
|----------|-------------|
| `legends_save_state()` | Serialize complete state |
| `legends_load_state()` | Restore from serialized state |
| `legends_get_state_hash()` | SHA-256 of observable state |
| `legends_verify_determinism()` | Round-trip determinism test |

### Introspection Functions

| Function | Description |
|----------|-------------|
| `legends_get_last_error()` | Get human-readable error message |
| `legends_set_log_callback()` | Register log callback |

## Error Codes

| Code | Value | Description |
|------|-------|-------------|
| `LEGENDS_OK` | 0 | Success |
| `LEGENDS_ERR_NULL_HANDLE` | -1 | Null handle provided |
| `LEGENDS_ERR_NULL_POINTER` | -2 | Null pointer argument |
| `LEGENDS_ERR_ALREADY_CREATED` | -3 | Instance already exists |
| `LEGENDS_ERR_NOT_INITIALIZED` | -4 | Instance not initialized |
| `LEGENDS_ERR_BUFFER_TOO_SMALL` | -6 | Buffer too small |
| `LEGENDS_ERR_INVALID_CONFIG` | -7 | Invalid configuration |
| `LEGENDS_ERR_INVALID_STATE` | -8 | Invalid save state |
| `LEGENDS_ERR_VERSION_MISMATCH` | -9 | API version mismatch |

## Formal Specification

Project Legends includes TLA+ specifications for critical subsystems:

- `spec/tla/Types.tla` - Core type definitions
- `spec/tla/EmuKernel.tla` - Emulation kernel
- `spec/tla/Scheduler.tla` - Event scheduler
- `spec/tla/PIC.tla` - Interrupt controller
- `spec/tla/DMA.tla` - DMA controller
- `spec/tla/SaveState.tla` - Save/load invariants

### Key Invariants

**Determinism**: Same inputs always produce same outputs
```
(config, input_trace, step_schedule) → final_state_hash
```

**Round-Trip**: Save/load preserves observable state
```
Obs(Deserialize(Serialize(S))) = Obs(S)
```

## Testing

### Test Suites

- **Unit Tests**: 120+ tests covering all API functions
- **ABI Tests**: Pure C compilation verification
- **Fuzz Tests**: Random input stability testing
- **Property Tests**: Invariant verification

### Running Tests

```bash
# All tests
ctest --test-dir build --output-on-failure

# Unit tests only
./build/tests/legends_unit_tests

# Specific test suite
./build/tests/legends_unit_tests --gtest_filter="LegendsSaveStateTest*"
```

### CI Pipeline

- **fast-tests**: Unit tests on every PR
- **asan-tests**: AddressSanitizer memory checking
- **ubsan-tests**: UndefinedBehaviorSanitizer
- **firewall-check**: Compile isolation verification

## Project Structure

```
ProjectLegends/
├── include/legends/       # Public headers
│   ├── legends_embed.h    # Main embeddable API
│   ├── llm_frame.h        # LLM I/O structures
│   ├── vision_*.h         # Vision capture
│   └── ...
├── src/legends/           # Implementation
│   ├── legends_embed_api.cpp
│   ├── llm_*.cpp
│   ├── vision_*.cpp
│   └── ...
├── tests/                 # Test suite
│   ├── unit/
│   └── fixtures/
├── spec/tla/              # TLA+ specifications
└── .github/workflows/     # CI configuration
```

## Contributing

We welcome contributions! Please see our contribution guidelines:

1. Fork the repository
2. Create a feature branch
3. Write tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

### Code Style

- C++23 with modern idioms
- `gsl-lite` for contracts
- Comprehensive documentation
- TLA+ specs for critical changes

## License

Project Legends is licensed under the GNU General Public License v2.0, consistent with its DOSBox-X heritage.

## Acknowledgments

Project Legends builds upon the excellent work of the DOSBox and DOSBox-X communities:

- **DOSBox Team**: Original DOSBox emulator
- **DOSBox-X Team**: Extended platform support and features
- **Contributors**: The many developers who have contributed to x86 emulation

Special thanks to the formal methods community for TLA+ tooling and methodology.

---

**Project Legends** - Bringing deterministic x86 emulation to the AI era.

*Copyright (c) 2024-2025 Charles Hoskinson and Contributors*
