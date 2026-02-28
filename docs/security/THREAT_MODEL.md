# Project Legends -- Threat Model

## Overview

Project Legends embeds a full x86 emulation engine (derived from DOSBox-X) as a
library. The emulated guest runs untrusted DOS programs. This document identifies
trust boundaries, enumerates threats using STRIDE, and tracks mitigations.

Audience: maintainers, downstream integrators, security reviewers.

---

## Trust Boundaries

Four trust boundaries exist. Data crossing any boundary is treated as untrusted
on the receiving side.

### TB-1: Host <-> Emulated Guest (x86 Sandbox)

The emulated x86 machine executes arbitrary DOS-era code. All output from the
guest to the host must be treated as adversarial:

- Frame capture output (text cells, RGB pixels)
- Audio samples (S16LE stereo PCM)
- Interrupt / IO port side-effects
- Save state blobs produced by guest-visible memory
- MIDI messages emitted by guest programs
- Printer spool data
- File system operations through mounted drives

The host exposes configuration and drive mounts to the guest. A compromised or
malicious guest program should not be able to read, write, or traverse host paths
outside the mounted directories.

### TB-2: Application <-> Engine (IPC Boundary)

When `LEGENDS_USE_IPC=ON`, the GPL-licensed engine runs in a separate process
(`legends_engine_host`). The MIT-licensed `legends_proxy` library serializes
`legends_embed.h` C API calls over a pipe to the engine host.

Data crossing this boundary:
- Serialized API call arguments (config structs, buffers, paths)
- Serialized return values (step results, capture buffers, error codes)
- Save state blobs transferred in both directions

The proxy library must contain no GPL code. Message framing and size limits are
enforced at the serialization layer.

### TB-3: User Input <-> Application

Keyboard, mouse, and joystick events enter through the PAL `IInputSource`
interface. Backend implementations exist for SDL2, SDL3, and headless mode.

Events are translated from host OS scancodes to the platform-independent
`pal::InputEvent` union, then injected into the emulated keyboard controller,
mouse port, or joystick port via `legends_key_event()`, `legends_mouse_event()`,
or `legends_joystick_event()`.

Attack surface:
- Scancode values outside valid AT Set 1 range
- Excessive event rates (input flooding)
- Re-entrant calls to `legends_step_*()` from within event processing

### TB-4: Build / Supply Chain <-> Distributed Binary

Dependencies are fetched via CMake `FetchContent` with version-pinned `GIT_TAG`
values in `cmake/dependencies.cmake`. Release artifacts are packaged by CPack
(NSIS/ZIP on Windows, DMG/TGZ on macOS, TGZ on Linux).

Attack surface:
- Dependency compromise at the Git hosting level
- Tampered release binaries
- Missing code signing allows spoofed distributions

---

## STRIDE Analysis

### TB-1: Host <-> Emulated Guest

| Category | Threat | Likelihood | Impact | Status |
|---|---|---|---|---|
| **Spoofing** | Guest spoofs host file system identity via path traversal in mount paths | Medium | High | Mitigated (in progress): canonical path resolution for mounts |
| **Tampering** | Malicious save state blob corrupts host memory during load | High | Critical | Mitigated: magic number validation (`DBXS`/`DBXE`), CRC-32 integrity check, section offset bounds validation, version checking. Fuzz-tested at both API and engine layers (`fuzz_legends_load_state`, `fuzz_engine_load_state`). |
| **Tampering** | Crafted image file (.iso/.img) triggers parser vulnerability on mount | Medium | High | In progress: image parser validation hardening |
| **Repudiation** | Guest modifies save state to replay from an earlier point, bypassing intended progression | Low | Low | Accepted: save state is caller-controlled by design; not a security boundary |
| **Info Disclosure** | Guest reads host memory via emulation bug (sandbox escape) | Low | Critical | Mitigated by design: CPU emulation operates on emulated RAM only; no direct host pointer exposure. Needs formal audit. |
| **Info Disclosure** | Save state blob leaks host addresses or paths | Low | Medium | Mitigated: save state contains emulated machine state only; host pointers are not serialized |
| **DoS** | Malicious save state causes OOM via inflated size field | Medium | Medium | Mitigated: `total_size` header field validated against buffer size; bounded allocation in load path |
| **DoS** | CPU emulation enters infinite loop consuming host resources | Medium | Low | Mitigated: caller controls stepping granularity via `legends_step_ms()`/`legends_step_cycles()`; no unbounded execution |
| **EoP** | Guest escapes emulation sandbox to execute host code | Low | Critical | Mitigated by design: no JIT, all instructions interpreted; IO ports mapped to emulated devices only. Requires formal audit. |
| **EoP** | Guest writes outside emulated RAM via integer overflow in memory addressing | Low | Critical | Mitigated: memory access goes through page tables with bounds checks. Fuzz-tested. |

### TB-2: Application <-> Engine (IPC)

| Category | Threat | Likelihood | Impact | Status |
|---|---|---|---|---|
| **Spoofing** | Rogue process connects to engine host pipe, impersonating the application | Low | High | TODO: pipe ACLs or authentication token exchange at connection setup |
| **Tampering** | IPC messages modified in transit (local MITM) | Low | Medium | TODO: HMAC or nonce-based message authentication |
| **Tampering** | Oversized IPC message causes buffer overflow in proxy | Medium | High | Mitigated: message size limits enforced at serialization boundary |
| **Repudiation** | No audit trail of IPC commands sent to engine | Low | Low | Accepted: logging available via `legends_set_log_callback()` |
| **Info Disclosure** | Pipe contents readable by other local users | Low | Medium | TODO: restrict pipe permissions to current user |
| **DoS** | Flood of IPC messages starves engine host | Low | Medium | Mitigated: synchronous request/response model; one outstanding call at a time |
| **EoP** | Crafted IPC message causes engine host to execute arbitrary code | Low | Critical | Mitigated: engine host validates all deserialized arguments against `legends_embed.h` type constraints |

### TB-3: User Input <-> Application

| Category | Threat | Likelihood | Impact | Status |
|---|---|---|---|---|
| **Spoofing** | Synthetic input events injected by another process (SendInput on Windows, etc.) | Low | Low | Accepted: standard for all desktop applications; OS-level concern |
| **Tampering** | Scancode value outside AT Set 1 range passed to `legends_key_event()` | Medium | Medium | Mitigated: scancode range validated before injection into keyboard controller |
| **Tampering** | Joystick axis value crafted to cause integer overflow in emulated gameport | Low | Medium | Mitigated: `legends_joystick_event()` clamps axis values to 0-255 range |
| **Repudiation** | User denies input sequence that caused unintended action | Low | Low | Accepted: not applicable to emulator use case |
| **Info Disclosure** | Input events leak to other emulator components unexpectedly | Low | Low | Mitigated: events flow through typed `pal::InputEvent` union; no raw pointer sharing |
| **DoS** | Input flood overwhelms keyboard buffer | Medium | Low | Mitigated: keyboard buffer is fixed-size (96 entries); excess events dropped. Step call serialization prevents unbounded accumulation. |
| **DoS** | Re-entrant `legends_step_*()` call from input callback | Medium | High | Mitigated: reentrancy guard returns `LEGENDS_ERR_REENTRANT_CALL` |
| **EoP** | Crafted input sequence exploits emulated BIOS interrupt handler | Low | Medium | Mitigated: BIOS handlers operate within emulated address space only |

### TB-4: Build / Supply Chain <-> Distributed Binary

| Category | Threat | Likelihood | Impact | Status |
|---|---|---|---|---|
| **Spoofing** | Attacker distributes trojanized binary under project name | Medium | Critical | TODO: code signing on all platforms (see `docs/security/CODE_SIGNING.md`) |
| **Tampering** | Dependency tag moved to point at malicious commit | Low | Critical | Mitigated: version-pinned `GIT_TAG` in `cmake/dependencies.cmake`. TODO: add commit hash pinning for stronger guarantees. |
| **Tampering** | CI artifact tampered between build and distribution | Low | High | TODO: artifact checksums published alongside releases |
| **Repudiation** | No way to verify which source produced a given binary | Medium | Medium | TODO: SBOM generation; reproducible build verification |
| **Info Disclosure** | Debug symbols or internal paths leak in release builds | Low | Low | Mitigated: release builds use `-DNDEBUG` and strip debug info |
| **DoS** | Compromised dependency introduces crash or hang | Low | Medium | Mitigated: CI runs unit tests, integration tests, and sanitizers on all three platforms before merge |
| **EoP** | Supply chain attack injects backdoor through transitive dependency | Low | Critical | Mitigated (partial): FetchContent pins direct dependencies; no transitive dependency resolution. TODO: vendor or hash-lock all dependencies. |

---

## Implemented Mitigations Summary

### Bounds-checked capture APIs, two-call pattern

All variable-size output APIs (`legends_capture_text`, `legends_capture_rgb`,
`legends_capture_audio`, `legends_save_state`, `legends_get_last_error`,
`legends_capture_midi_audio`) use the two-call pattern:

1. Call with `buffer=NULL` to query required size
2. Call with appropriately-sized buffer

Returns `LEGENDS_ERR_BUFFER_TOO_SMALL` if the caller-provided buffer is
insufficient. This prevents buffer overflows at the API boundary.

### Fuzz-tested save/load paths

Three libFuzzer targets exercise deserialization:

- `fuzz_legends_load_state` -- fuzzes `legends_load_state()` at the public API level
- `fuzz_engine_load_state` -- fuzzes `dosbox_lib_load_state()` at the engine level
- `fuzz_input_injection` -- fuzzes input injection APIs

Custom mutators understand the save state header format (magic bytes, version
field, total_size) to reach deeper code paths. Corpus generation tooling
creates seed inputs from valid save states.

### Version-pinned dependencies

`cmake/dependencies.cmake` pins all external dependencies:

| Dependency | Pinned Tag |
|---|---|
| gsl-lite | v1.0.0 |
| SDL3 | release-3.2.8 |
| GoogleTest | v1.14.0 |
| Google Benchmark | v1.8.3 |
| FluidSynth | v2.3.5 |
| mt32emu (MUNT) | v2.7.0 |

### Sanitizer and fuzz testing in CI

CI runs on all three platforms (Windows, macOS, Linux) with:
- Unit tests and integration tests
- AddressSanitizer (`-fsanitize=address`)
- UndefinedBehaviorSanitizer (`-fsanitize=undefined`)
- MemorySanitizer (`-fsanitize=memory`) where supported
- Fuzz testing quick-run target (`fuzz-quick`, 60-second run per merge)

### Save state header validation (in progress)

Save state format includes:
- Magic number: `DBXS` (0x53584244) at Legends API layer, `DBXE` (0x45584244) at engine layer
- Version field checked against supported versions (V2, V3, V4)
- CRC-32 checksum of data after header
- `total_size` field validated against actual buffer size
- Section offsets validated against total size before dereferencing
- Input event count validated against buffer capacity (max 319)

### Canonical path resolution for mounts (in progress)

`legends_mount_drive()` will resolve host paths to canonical form before exposing
them to the emulated file system. This prevents path traversal attacks where a
guest program attempts to escape the mounted directory via `..` sequences or
symlink chains.

### Image parser validation (in progress)

Disk image parsers (.iso, .img, .ima, .cue, .bin) are being hardened to validate
header fields, reject malformed images, and bound all allocations against the
actual file size.

---

## Open Items

- [ ] Formal security audit of CPU emulation (TB-1 sandbox escape)
- [ ] IPC pipe authentication: token exchange or OS-level ACLs (TB-2)
- [ ] IPC message authentication: HMAC or nonce (TB-2)
- [ ] Commit hash pinning for all FetchContent dependencies (TB-4)
- [ ] SBOM generation for release artifacts (TB-4)
- [ ] Code signing on all platforms: Windows Authenticode, macOS notarization, Linux GPG (TB-4)
- [ ] Artifact checksum publication alongside releases (TB-4)
- [ ] Vendor or hash-lock transitive dependencies (TB-4)
- [ ] Restrict IPC pipe permissions to current user (TB-2)
- [ ] IPX networking input validation audit (TB-1, when IPX is stabilized)
