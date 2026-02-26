# Project Legends — Threat Model (Skeleton)

> **Status**: Skeleton — full content requires formal security review.

## Trust Boundaries

### 1. Host ↔ Emulated Guest

The emulated x86 machine runs untrusted code (DOS programs). All data crossing
from the guest to the host must be treated as untrusted:
- Frame capture output (text cells, RGB pixels)
- Audio samples
- Interrupt/IO port side effects

**Mitigations**: Bounds-checked capture APIs, two-call pattern prevents buffer overflows, fuzz-tested load/save paths.

### 2. Application ↔ Engine (IPC Boundary)

When `LEGENDS_USE_IPC=ON`, the engine host runs in a separate process. The IPC
protocol serializes `legends_embed.h` calls over a pipe.

**Mitigations**: MIT-licensed proxy/IPC layer contains no GPL code; message size limits; input validation at the serialization boundary.

### 3. User Input ↔ Application

Keyboard, mouse, and joystick events from the host OS enter through the PAL
input source and are translated to emulated scancodes.

**Mitigations**: Scancode range validation, input buffer limits, reentrancy guard on step calls.

### 4. Build/Supply Chain ↔ Distributed Binary

Dependencies are fetched from GitHub via FetchContent with pinned `GIT_TAG` values.

**Mitigations**: Version-pinned dependencies (`cmake/dependencies.cmake`), CI verification on all three platforms, sanitizer + fuzz testing on merge-to-main.

## STRIDE Analysis

| Threat | Category | Boundary | Status |
|---|---|---|---|
| Guest escapes emulation sandbox | Elevation of Privilege | 1 | Mitigated by CPU emulation design; needs formal audit |
| Malicious save state crashes host | Denial of Service | 1 | Fuzz-tested; bounded allocation |
| IPC message spoofing | Tampering | 2 | TODO: add HMAC or nonce validation |
| Dependency compromise | Tampering | 4 | Pinned tags; TODO: add hash verification |
| Crafted input overflow | Buffer Overflow | 3 | Bounds-checked in PAL input source |

## Open Items

- [ ] Full STRIDE analysis for each trust boundary
- [ ] Formal security audit of save/load deserialization
- [ ] IPC protocol authentication design
- [ ] Dependency hash pinning (beyond git tag)
- [ ] SBOM generation for release artifacts
