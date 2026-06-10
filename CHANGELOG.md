# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- **Embeddable C API** (`legends_embed.h`) with 22+ functions covering
  lifecycle, stepping, capture, input injection, save/load, and diagnostics
- **Platform Abstraction Layer (PAL)** with headless, SDL2, and SDL3 backends
  implementing IWindow, IContext, IAudioSink, IHostClock, and IInputSource
- **State serialization** with CRC-32 integrity verification and determinism
  round-trip invariant (`Obs(Deserialize(Serialize(S))) = Obs(S)`)
- **DOSBox-X engine** compiled as static library (`aibox_core`) with library
  mode API, context-based state isolation, and embeddable lifecycle
- **GPL v2 process isolation** architecture: MIT-licensed IPC library
  (`legends_ipc`), engine host process (`legends_engine_host`), and proxy
  library (`legends_proxy`) enabling non-GPL application shells
- **IPC protocol** with binary wire format, shared memory framebuffer
  (double-buffered, zero-copy), shared memory audio ring buffer, and
  named pipe control channel
- **Application shell** (`src/app/`) with CLI parser, INI config parser,
  platform directory support, scancode mapping, action bus, input mapper,
  save manager, menu system, hotkey dispatcher, mount manager, video capture
  (ZMBV codec), mapper UI, and save browser
- **Phase 3 enhanced features** (scaffolded): joystick mapper, shader
  presets/renderer, AI config/HTTP client/screen context/panel, audio mixer,
  MIDI config, printer manager, TTF renderer, IPX config, Glide config,
  PC-98 config
- **Phase 4 polish**: file logger, error reporter, crash breadcrumb/reporter,
  SSIM image comparison, portable mode, update checker
- **Security hardening**: update-checker HTTPS transport uses WinHTTP secure
  requests (`src/app/update_checker_win.cpp:46`); AI HTTP client transport is
  still deferred (`src/app/ai_http_client.cpp:212`); API key protection, config
  field limits, save state CRC validation, path confinement, read-only mounts,
  sensitive directory warnings, stack protector, FORTIFY_SOURCE, CFG (MSVC)
- **CI pipeline** with Linux (GCC/Clang), Windows (MSVC), macOS (AppleClang),
  SDL3 builds, sanitizers (ASan, UBSan, TSan, MSan), C ABI verification,
  static analysis (clang-tidy), fuzz testing (libFuzzer), TLA+ model
  checking, code coverage, dependency scanning, and packaging
- **TLA+ formal specifications** for lifecycle, PAL, threading, save state,
  determinism, capture, input, reentrancy, bus, scheduler, interrupt, DMA,
  error model, config validation, and API contract
- **Fuzz targets** for engine load state, legends load state, input injection,
  and config parser
- **1500+ tests** across unit, integration, ABI, and toolchain categories
- **Wasm sandbox** build option and WIT interface definition (planned)
- **License files**: COPYING (GPL v2), LICENSE (multi-component overview),
  NOTICE (copyright attributions and SPDX identifiers)

### Fixed

- NOMINMAX defined before windows.h to prevent std::min/std::max macro
  conflicts on MSVC
- MSVC C3409 parser bug workaround by extracting lambdas from TEST bodies
- Shared memory skip guards, mount error mapping, TSan allow-failure
- MSVC constexpr lambda compatibility, fragmented recv handling, crash
  handler reliability
- Pre-existing test bugs: hex validation, SHM init order, skip guards
- MSan marked as allow-failure (requires instrumented libc++)
- Headless mode skip guards for mount/event tests
- Linux/macOS update checker stubs, zmbv_stubs for SDL3 target
- Cross-platform CI build failures resolved across all platforms
