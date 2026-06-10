# API Surface & Architecture Audit — Project Legends

- **Auditor role:** API surface & architecture
- **Audit date:** 2026-06-09
- **Baseline:** AUDIT.md of 2026-02-24 (findings C1-C2, H1-H9, M1-M11, L1-L8)
- **Scope:** `include/legends`, `include/legends_ipc`, `include/pal`, `src/app/runtime_host.*`, `src/legends/legends_embed_api.cpp` structure, `src/legends_proxy`, `src/engine_host`, `cmake/ModuleDAG.cmake` / `ModuleManifest.cmake`, install rules, README embeddability promise.

---

## 1. Executive summary

The in-process C ABI (`include/legends/legends_embed.h`, 50 `LEGENDS_API` functions) is in materially better shape than at the February audit: the destroy-fallback hole (H5) is fixed, all previously unused error codes (L2) are now used, the `LEGENDS_ERROR` macro collision (L4) is gone, the dual error-code system is documented with static_asserts, config strings are deep-copied, and the 27-pair header duplication (C1) has been collapsed to 4-line forwarding headers.

The new risk center is the **runtime split**. Since February the project grew a second runtime path (`legends_proxy` reimplementing the C ABI over IPC, `legends_engine_host` dispatching 43 message cases) plus a C++ `RuntimeHost` facade adopted across the app shell. This IPC architecture is structurally sound but **not finished and not honest about it**:

1. **IPC mode cannot actually run.** No production code ever establishes the IPC connection (`ProxyConnection::connect()` is only called from tests), so every proxied `legends_*` call returns `LEGENDS_ERR_NOT_INITIALIZED`; additionally the SDL2+IPC executable cannot even link. The CI IPC job builds headless-only and never catches either.
2. **The two runtimes do not expose identical semantics.** Six API functions are `NOT_SUPPORTED` over IPC, `legends_destroy(NULL)` is a no-op in-process but destroys the engine over IPC, half the proxy functions skip handle validation entirely, and `legends_capture_rgb` silently changes its error contract.
3. **The ABI version handshake does not cross the process boundary.** `CreateReq` drops `api_version`/`struct_size`/`config_path`/`working_dir`; the engine host's `HandshakeAck` carries `protocol_version` and `engine_version` but the proxy never reads them.
4. **The installed package is broken for embedders.** `install(DIRECTORY include/legends ...)` ships 25 forwarding headers that `#include <aibox/...>` headers which are never installed, a `gsl.hpp` that requires a private dependency, and `runtime_host.h` whose implementation lives in the never-installed `legends_app` target.

Net: a **single-instance, in-process, build-from-source embedder** gets a genuinely good C API today. The README/architecture promise — GPL-isolated process mode, installable SDK, "embeddable" in the package-consumer sense — is not yet delivered.

**Health grade: C** (good core C ABI, prior fixes verified; the headline architecture additions are unwired, unverified in CI, and divergent).

---

## 2. Prior-finding status (in scope)

| Prior ID | Finding | Status at HEAD | Evidence |
|---|---|---|---|
| C1 | 27+ duplicated header pairs `include/legends` vs `engine/include/aibox` | **Resolved (with a new caveat)** | All 25 overlapping pairs in `include/legends/` are now 4-line forwarding headers, e.g. `include/legends/builder.h:1-4` (`#include <aibox/builder.h>` + `namespace legends { using namespace aibox; }`); `machine_context.h` is 7 lines. Single source of truth is `engine/include/aibox/`. Caveat: these forwarding headers are installed while their `aibox/` targets are not — see finding api-06. |
| H5 | `legends_destroy()` fallback destroys active instance on any non-null handle | **Resolved (in-process)** | `src/legends/legends_embed_api.cpp:960-969`: null handle → `LEGENDS_OK` no-op; non-matching handle → `get_instance()` returns nullptr → `LEGENDS_ERR_NULL_HANDLE`. No `g_active_instance` fallback. Caveat: the IPC proxy reintroduces the permissive behavior (`src/legends_proxy/proxy_api.cpp:81-83` ignores the handle entirely) — see finding api-02. |
| L2 | Error codes `REENTRANT_CALL`, `IO_FAILED`, `NOT_SUPPORTED` defined but unused | **Resolved** | `LEGENDS_ERR_REENTRANT_CALL` returned at `legends_embed_api.cpp:1010` (and step paths); `LEGENDS_ERR_IO_FAILED` used in `src/legends_proxy/ipc_error_mapping.h:15-16` and `legends_embed_api.cpp`; `LEGENDS_ERR_NOT_SUPPORTED` used by proxy stubs (`proxy_api.cpp:425,452-454,571,675`) and dispatcher default (`engine_dispatcher.cpp:536`). Commit `7f86dd7` made stub APIs return `NOT_SUPPORTED` instead of `OK`. |
| L3 | `HandleRegistry` fully implemented but unused | **Confirmed open** | `engine/include/aibox/handle_registry.h` (504 lines) is consumed only by tests (`tests/unit/test_handle_registry.cpp`, `test_thread_safety.cpp`, `test_gsl_contracts.cpp`). The embed API still validates handles by pointer equality against the single `g_active_instance` (`legends_embed_api.cpp:79-82`). It is also re-exported publicly via the forwarding header `include/legends/handle_registry.h`. |
| L4 | `LEGENDS_ERROR` macro collision between `error.h` and `legends_embed_api.cpp` | **Resolved** | `grep "define LEGENDS_ERROR"` across `src/`, `include/`, `engine/include`, `engine/src` finds exactly one definition: `src/legends/legends_embed_api.cpp:690` (with a defensive `#ifdef/#undef` at 687-688). Neither `include/legends/error.h` (now a forwarding header) nor `engine/include/aibox/error.h` defines it. Commit `91569c6` additionally documented the dual public/internal error-code systems and added sign-invariant static_asserts (`legends_embed.h:56-99`). |

Related context: the prior audit's "Module DAG enforcement complete" (resolved M9, Sprint 3) is now stale relative to the IPC split — see finding api-08.

---

## 3. New findings

### api-01 — IPC runtime mode is not usable end-to-end (no bootstrap, SDL2+IPC cannot link, CI never exercises the app)  — **HIGH**

The entire GPL-isolation runtime (`LEGENDS_USE_IPC=ON`) has no production path that establishes the connection:

- Every proxied API call gates on `conn().is_connected()` and returns `LEGENDS_ERR_NOT_INITIALIZED` otherwise (`src/legends_proxy/proxy_api.cpp:23,33,44,57,...`).
- `ProxyConnection::connect()` (`src/legends_proxy/proxy_connection.cpp:13-51`) is declared in a **private** header (`src/legends_proxy/proxy_connection.h`, not under `include/`), and a repo-wide search shows it is invoked only by `tests/integration/test_ipc_integration.cpp` and unit tests. Neither `src/app/application.cpp` nor `src/main.cpp` references `ProxyConnection` or `EngineSpawner` at all (grep over `src/app`, `src/main.cpp` returns zero hits). `EngineSpawner::spawn` is used in production code only for crash *restart* (`src/legends_proxy/crash_handler.cpp:35`), never for initial spawn. The comment "Connect to an existing engine host (or auto-spawn one)" (`proxy_connection.h:25`) describes unimplemented behavior.
- Consequence: in an IPC build, `Application::init` calls `legends_create()` (`src/app/application.cpp:905`), the proxy returns `NOT_INITIALIZED`, and the app exits with `ExitCode::EngineCreateFailed` (`application.cpp:909-917`). The IPC mode literally cannot boot the shipped application or any embedder that uses only public headers.
- Worse, the **SDL2 + IPC** combination cannot even link: `project_legends` (SDL2 branch) compiles only `src/main.cpp` (`CMakeLists.txt:1152-1156`) and in IPC mode links `legends_proxy + legends_pal` but **not** `legends_app` (`CMakeLists.txt:1173-1180`), while `src/main.cpp:9` instantiates `legends::Application`, which is compiled only into `legends_app` (`CMakeLists.txt:503-505`). Unresolved symbols guaranteed. (The SDL3 branch dodges this by re-listing all ~45 app sources inline, `CMakeLists.txt:1211-1268`.)
- CI never sees any of this: the `linux-ipc` job configures `-DLEGENDS_HEADLESS=ON` (no SDL), so `project_legends` is never built; it only asserts `legends_engine_host` and `legends_unit_tests` exist (`.github/workflows/ci.yml:95-127`).

This confirms the TODO.md status "GPL v2 Process Isolation 2/16" — but the README/ARCHITECTURE present IPC mode as a working build mode (`ARCHITECTURE.md:547-554`).

**Recommendation:** Implement the bootstrap inside proxy `legends_create()` (spawn `legends_engine_host` via `EngineSpawner`, create pipe/SHM, handshake) or expose a public `legends_ipc_connect()` entry point; fix the SDL2+IPC link by splitting `Application` out of the GPL-linked `legends_app` (it links `legends_core` PUBLIC, `CMakeLists.txt:571-575`) into a runtime-agnostic shell library; add a CI job that boots the app (or a smoke embedder) against a spawned engine host. **Effort: L.**

### api-02 — In-process and IPC runtimes do not expose identical C ABI semantics — **HIGH**

The promise of the runtime split is that an embedder (or `RuntimeHost`) can swap backends without behavioral change. Verified divergences:

1. **Six functions are `NOT_SUPPORTED` over IPC**: `legends_set_log_callback` (`proxy_api.cpp:424-426`), `legends_start/stop/is_video_capture` (`:452-454`), `legends_set_ttf_font` (`:571`), `legends_register_event_callback` (`:675`). The app calls `runtime_->set_log_callback(...)` unconditionally (`src/app/application.cpp:1181,1193`), so logging silently disappears in IPC mode.
2. **`legends_destroy(NULL)` semantics invert.** In-process: documented no-op returning `LEGENDS_OK` (`legends_embed_api.cpp:960-963`). Proxy: parameter ignored, `DestroyReq` always sent, engine-side singleton destroyed (`proxy_api.cpp:81-83`; `engine_dispatcher.cpp:67-73`). An embedder defensively calling `legends_destroy(NULL)` kills the live instance in IPC mode. This re-creates the spirit of fixed finding H5 across the process boundary.
3. **Handle validation is inconsistent within the proxy itself.** `legends_step_ms/step_cycles/key_event/mouse_event/reset/get_emu_time/get_total_cycles/capture_rgb/is_frame_dirty/get_cursor/is_audio_active/get_state_hash/get_last_error/mount_drive/unmount_drive` ignore the handle (e.g. `proxy_api.cpp:116-132, 255-265, 293-304`), while `key_event_ext/text_input/save_state/load_state/joystick/midi/printer/ipx/glide/pc98/has_capability` check `!handle → LEGENDS_ERR_NULL_HANDLE` (e.g. `:267-268, 280-282, 331`). In-process, *every* handle function validates. So `legends_step_ms(NULL, 10, ...)` returns `LEGENDS_ERR_NULL_HANDLE` in-process but happily steps the engine over IPC.
4. **`legends_capture_rgb` changes its contract.** In-process: `BUFFER_TOO_SMALL` when the buffer is too small, dims always reported, `NULL_POINTER` if `size_out` is null (`legends_embed_api.cpp:1277-1319`). Proxy: reads the SHM framebuffer; if no frame yet, returns `LEGENDS_OK` with `*size_out = 0`; if the buffer is too small it **silently skips the copy and still returns `LEGENDS_OK`** (`proxy_api.cpp:214-233`). Callers cannot detect truncation.
5. **Thread-affinity (`LEGENDS_ERR_WRONG_THREAD`) and reentrancy (`LEGENDS_ERR_REENTRANT_CALL`) guards exist only in-process** (engine-host side enforces them on its own thread, which is always the dispatcher thread — so these error codes are unreachable for IPC embedders, changing the documented error model of `legends_embed.h:76,85`).
6. The `IpcEngineRuntime` sentinel handle (`(uintptr_t)1`, `proxy_api.cpp:75-78`) means handle identity is cosmetic in IPC mode.

The two `RuntimeHost` subclasses are textually identical (see api-07), so none of this is mediated at the facade layer either.

**Recommendation:** Write a single parameterized conformance test suite (error codes, null-handle behavior, two-call patterns, destroy semantics) executed against both runtimes in CI; fix proxy null-handle checks and `capture_rgb` error contract; either implement log forwarding/event notification over the already-defined `SetLogCallbackReq`/`EventNotification` messages or document the capability matrix in `legends_embed.h` and surface it through `legends_has_capability`. **Effort: L** (M for the fixes, +S for the harness).

### api-03 — ABI/version handshake and config do not survive the IPC boundary — **HIGH**

- `CreateReq` carries only 7 numeric config fields (`include/legends_ipc/messages.h:112-128`); `api_version`, `struct_size`, `config_path`, and `working_dir` are dropped by the proxy (`proxy_api.cpp:59-68`). The dispatcher rebuilds the config from its **own** `LEGENDS_CONFIG_INIT` (`engine_dispatcher.cpp:52-59`), so the in-process version gate (`legends_embed_api.cpp:829-839`, returns `INVALID_CONFIG`/`VERSION_MISMATCH`) validates the engine host's header against itself — a tautology. A shell built against API 1.1 talking to a 1.0 engine host is undetectable at create time.
- The wire **does** carry version data — `HandshakeAck.protocol_version` and `HandshakeAck.engine_version = LEGENDS_API_VERSION` (`messages.h:33-41`, `src/engine_host/main.cpp:55-57`) — but the proxy checks only `error_code` and discards both versions (`proxy_connection.cpp:41-43`). `IpcError::VersionMismatch` and its mapping (`ipc_error_mapping.h:21`) are dead code. The `Handshake` request message (`messages.h:21`) is never sent by anyone; the engine pushes an unsolicited ack.
- Dropping `config_path` is a functional regression, not just hygiene: the app resolves and passes a `.conf` path (`application.cpp:885-897`), which the engine host silently never receives — DOS configuration silently ignored in IPC mode.

**Recommendation:** Validate `ack.protocol_version`/`engine_version` in `ProxyConnection::connect()` (fail with `VersionMismatch`); add `api_version`+`struct_size` to `CreateReq` and validate host-side; transmit `config_path`/`working_dir` (with the path-confinement checks the security roadmap already requires). **Effort: S-M.**

### api-04 — IPC responses are not correlated by type or sequence ID — **MEDIUM** (high consequence, mitigated by lock-step usage)

`ProxyConnection::request<Resp>()` deserializes whatever message arrives next without verifying `msg->header.msg_type == Resp::type` or that `sequence_id` matches the request (`src/legends_proxy/proxy_connection.h:39-45`; `proxy_connection.cpp:74-88` assigns a fresh `seq` but never checks it on receive). The header infrastructure exists (`include/legends_ipc/message_header.h:14-40` carries both fields). Failure mode: a request that times out (5 s, `proxy_connection.cpp:85`) returns an error to the caller, but the late response stays in the pipe; the *next* request then consumes the stale response and field-wise LE decoding happily reinterprets, e.g., a `StepMsResp` as a `KeyEventResp` — garbage accepted as valid, stream desynchronized for the remainder of the session.

**Recommendation:** In `request<>`, check `msg_type` (treating `ErrorResponse` specially) and loop-discarding responses whose `sequence_id` < expected; consider draining the pipe on timeout. **Effort: S.**

### api-05 — Installed package is broken for embedders — **HIGH**

`install(DIRECTORY include/legends include/pal ...)` (`CMakeLists.txt:1350-1352`) ships the entire `include/legends` tree, but:

- The 25 forwarding headers (`builder.h`, `error.h`, `machine_context.h`, ... — each `#include <aibox/...>`, e.g. `include/legends/builder.h:3`) reference `engine/include/aibox/` headers that are **never installed** (only targets `legends_core`, `aibox_core`, `legends_pal` archives plus `include/legends` + `include/pal` are installed, `CMakeLists.txt:1333-1357`). Any consumer including them gets a hard compile error.
- `include/legends/gsl.hpp` self-documents "gsl-lite is a PRIVATE dependency ... Do NOT include this header in public API headers" yet ships in the public include set, and `contracts.hpp` similarly exposes internal contract machinery.
- `include/legends/runtime_host.h` (the C++ facade, `RuntimeHost`/`InProcessEngineRuntime`/`IpcEngineRuntime`/`create_runtime`) is installed, but its implementation `src/app/runtime_host.cpp` is compiled only into `legends_app` (`CMakeLists.txt:503-505`) and `project_legends` (`:1211-1214`) — neither installed. Installed consumers get unresolved symbols.
- `include/legends_ipc` and the `legends_ipc`/`legends_proxy`/`legends_engine_host` artifacts are never installed, so the IPC mode is not consumable as a package at all.

Effectively only `legends_embed.h` + `legends_export.h` survive installation intact. The prior audit marked the CMake package export fixed (old H6); the export exists but exports a broken header set.

**Recommendation:** Define the supported public surface explicitly (C ABI: `legends_embed.h`, `legends_export.h`; optionally `runtime_host.h` if its impl moves into an installed library); install only that, or install `engine/include/aibox` alongside if the C++ surface is intended to be public. Add a CI consumption test: `cmake --install` into a scratch prefix, then build a 20-line external embedder against `find_package(Legends)`. **Effort: M.**

### api-06 — `RuntimeHost`: duplicate identical subclasses, inverted layering, dead types — **MEDIUM**

- `InProcessEngineRuntime` (`src/app/runtime_host.cpp:25-318`) and `IpcEngineRuntime` (`:328-621`) are **byte-for-byte identical** ~300-line implementations; both call the same `legends_*` symbols, because the actual backend switch is link-time (`legends_proxy` vs `legends_core`). The class split implies a behavioral difference that does not exist; the only differentiation is the `#if LEGENDS_USE_IPC` factory branch (`runtime_host.cpp:629-651`) and the matching branch in `application.cpp:929-945`. One concrete class (`CEngineRuntime`) would eliminate ~300 duplicated lines and a misleading abstraction; alternatively, `IpcEngineRuntime` should own connection bootstrap/heartbeat/crash-restart (which would justify its existence and fix api-01).
- Layering inversion: the header lives in the public API tree (`include/legends/runtime_host.h`) but its implementation lives in the **app layer** (`src/app/`) and is compiled into the GPL-linked `legends_app`. A "public" interface implemented by the topmost layer cannot be consumed by embedders (see api-05) and creates an `include/legends → src/app` conceptual dependency that ModuleManifest's own forbidden-pattern list is designed to prevent (`cmake/ModuleManifest.cmake:86-92`).
- `legends::FrameData` (`runtime_host.h:25-33`) is referenced by no interface method and duplicates `legends_ipc::FrameData` (`include/legends_ipc/framebuffer_shm.h:33`).
- Facade coverage: `RuntimeHost` exposes 32 of the 50 C APIs. Missing: `get_emu_time`, `get_config`, `get_state_hash`, `verify_determinism`, `get_last_error`, `is_audio_active`, `has_capability`, `register_event_callback`, `printer_is_active`, `printer_flush`, `ipx_is_connected`, `is_pc98_mode`, video-capture trio, `force_destroy`, `get_api_version`. Code needing those bypasses the facade with the raw handle (e.g. crash autosave stores the raw `engine_` handle globally, `application.cpp:957`), so backend-swap guarantees are partial.

**Recommendation:** Collapse to one class, move declaration+definition into an installed `legends_runtime` (or into `legends_core`-adjacent non-GPL wrapper for IPC mode), delete `legends::FrameData`, and round out the facade or document the intentional subset. **Effort: S-M.**

### api-07 — Module DAG enforcement did not keep up with the IPC split — **MEDIUM**

`cmake/ModuleManifest.cmake:63-68` now declares DAG edges for six modules including `legends_ipc`, `legends_proxy`, `legends_engine_host`. But `cmake/ModuleDAG.cmake` still verifies only the original three: `legends_verify_all_dags()` checks `legends_core`, `legends_pal`, `aibox_core` (`ModuleDAG.cmake:196-206`) and `legends_detect_cycles()` hardcodes `set(MODULES "legends_core" "legends_pal" "aibox_core")` (`:124`). Consequences:

- The license-critical constraints — `legends_proxy → legends_ipc` only (MIT, no GPL), `legends_engine_host → legends_core;legends_ipc` — are declared but **never enforced at configure time**. A stray `target_link_libraries(legends_proxy ... legends_core)` would pass DAG verification silently (GPL leakage into the "non-GPL" shell is guarded only by the separate `VerifyGPLIsolation.cmake` post-build check, which is IPC-mode-only).
- `legends_app` (which links `legends_core` PUBLIC, `CMakeLists.txt:571-575`) is absent from the manifest entirely, so the largest new module sits outside the formal graph.

**Recommendation:** Add the missing modules to both verification functions (the manifest already has the data); add `legends_app` with an explicit edge list; assert in CI for both build modes. **Effort: S.**

### api-08 — `legends_config_t` evolution policy is self-contradictory — **MEDIUM**

`legends_embed.h:114` promises "This struct layout is frozen for v1.x. New fields added at end only", and reserves `uint64_t _reserved[8]` (`:143`). But `legends_create()` rejects any config whose `struct_size != sizeof(legends_config_t)` **exactly** (`legends_embed_api.cpp:829-833`). Under this check, appending a field in v1.1 breaks every embedder compiled against v1.0 (their `struct_size` is smaller), defeating the stated additive-evolution policy. The conventional contract is `struct_size >= minimum && struct_size <= sizeof(current)`, reading only the prefix the caller declared. Related version-discipline observations: the API grew from 22 to 50 functions since the 2026-02 audit while `LEGENDS_API_VERSION_MINOR` is still 0 (`legends_embed.h:45-47`) and `CHANGELOG.md` has only `[Unreleased]` — semver exists on paper but has never been exercised; the IPC layer additionally hardcodes `protocol_version = 1` with no negotiation (see api-03).

**Recommendation:** Change the struct_size check to ranged-prefix semantics now (before any external consumer exists, this is still a free change); start bumping MINOR on API additions; pin and test `LEGENDS_CONFIG_INIT` against older struct prefixes in the ABI test (`tests/unit/test_legends_abi.c`). **Effort: S.**

### api-09 — Single-instance design contradicts the README's embeddability motivation — **MEDIUM**

`README.md:17` motivates the project: existing emulators are "unsuitable for embedding into larger systems where you need **multiple instances**, state serialization, or reproducible execution." The delivered design is explicitly single-instance: `legends_embed.h:13` ("Single instance per process"), `legends_create` returns `LEGENDS_ERR_ALREADY_CREATED` (`:74`, enforced via atomic CAS at `legends_embed_api.cpp:803-819`). The IPC architecture is the natural escape hatch (one engine-host **process per instance** would deliver multi-instance without touching engine globals), but `ProxyConnection` is a hard singleton (`proxy_connection.cpp:8-11`) and the engine host holds a single `g_handle` (`engine_dispatcher.cpp:13`), so the limitation is re-baked into the new layer. Not a defect per se — but the public promise and the architecture roadmap should either commit to N-process multi-instance via IPC or stop implying multi-instance.

**Recommendation:** Decide and document. If multi-instance is wanted, the cheapest path is keying `ProxyConnection` per handle and spawning one host per `legends_create` — the message protocol already needs no per-instance changes since the handle is implicit. **Effort: decision S; implementation L.**

### api-10 — Protocol surface contains dead and unsolicited message types; minor uninitialized-bytes leak — **LOW**

- Never sent nor dispatched: `ForceDestroyReq/Resp` (proxy maps `legends_force_destroy` to `DestroyReq`, `proxy_api.cpp:85-87`), `CaptureRgbReq/Resp` and `CaptureAudioReq/Resp` (superseded by SHM), `SetLogCallbackReq/Resp`, `StartVideoCaptureReq` etc., `SetTtfFontReq/Resp`, `RegisterEventCallbackReq/Resp`, `EventNotification` (`include/legends_ipc/message_types.h:28,48-49,66-67,84-85,94-99,122-123,152-154`). `Handshake` (0x0001) is never sent — the engine host pushes an unsolicited `HandshakeAck` (`src/engine_host/main.cpp:54-62`).
- `GetStateHashReq` handler serializes `resp.hash` even when `legends_get_state_hash` failed and the array was never written (`engine_dispatcher.cpp:177-182`; `GetStateHashResp` has no in-class initializer for `hash`), leaking up to 32 bytes of engine-host stack across the process boundary. Same pattern worth checking on other partially-filled responses.
- 108 message types vs 43 dispatched request cases is fine as a forward-reservation strategy, but the dead types should be commented as reserved/SHM-superseded so the dispatcher's `default: NOT_SUPPORTED` (`engine_dispatcher.cpp:534-538`) is clearly intentional per type.

**Recommendation:** Zero-init response structs, annotate reserved message IDs, and either implement `EventNotification` (needed for api-02 item 1) or remove it. **Effort: S.**

### api-11 — SDL3 executable re-lists the entire app source tree instead of reusing `legends_app` — **LOW**

`CMakeLists.txt:1211-1268` duplicates ~45 source files of `legends_app` (`:503-556`) inline in the SDL3 `project_legends` target. Any added app source must be registered twice (three times counting the SDL2/IPC matrix); drift here produces backend-specific link failures of exactly the kind already present in api-01. **Recommendation:** make `legends_app` PAL-agnostic and link it from both SDL targets, or generate the source list once into a variable. **Effort: S.**

---

## 4. What is genuinely good

- **The C ABI core is professional.** Two-call pattern used consistently; documented dual error-code system with compile-time sign invariants (`legends_embed.h:56-99`); error codes all reachable; thread-affinity, reentrancy, and bounds-validation macros consistently applied; config strings deep-copied (`legends_instance.h:46-49`, fixing old M4/M9 at this layer); `LEGENDS_CONFIG_INIT` + `struct_size`/`api_version` gating at create (`legends_embed_api.cpp:828-839`).
- **C1 deduplication actually happened** — the highest-severity structural debt from February is gone (25 forwarding shims, one canonical header tree).
- **The IPC wire format is clean**: explicit LE field encoding (`wire_format.h`), 10-byte header with type/size/seq (`message_header.h:14-20`), `std::expected`-based decode errors, SHM for high-bandwidth paths (framebuffer double-buffer, audio ring) — the right architecture, just unfinished at the edges.
- **`legends_export.h`** handles static/DLL/visibility correctly; there is a dedicated C-mode ABI test target (`tests/unit/test_legends_abi.c`, `CMakeLists.txt:859-873`).

---

## 5. Sprint-theme recommendations

1. **"Make IPC real" sprint (api-01, api-03, api-04):** bootstrap spawn+connect inside proxy `legends_create`; validate handshake versions; correlate responses by type+sequence; fix SDL2+IPC link; add a CI job that runs the app (or a smoke embedder) end-to-end in IPC mode. This converts the GPL-isolation roadmap item from scaffolding to a feature.
2. **"One ABI, two runtimes" parity sprint (api-02, api-06, api-10):** single conformance suite run against both backends in CI; fix proxy null-handle/destroy/capture_rgb contracts; collapse the duplicate `RuntimeHost` subclasses; implement or formally capability-gate the six `NOT_SUPPORTED` functions (wire `EventNotification` for log/event callbacks).
3. **"Installable SDK" sprint (api-05, api-08, api-11):** prune the installed header set to the supported surface, install (or stop shipping references to) `aibox` headers, move `runtime_host` into an installed library, adopt ranged `struct_size` semantics, and add a CI `cmake --install` + external-consumer build test.
4. **"Boundary enforcement catch-up" (api-07):** extend ModuleDAG verification to all six declared modules plus `legends_app`, so the MIT/GPL link constraints that the licensing story depends on are enforced at configure time in both build modes.

---

## 6. Files examined (primary evidence set)

`include/legends/legends_embed.h`, `legends_export.h`, `runtime_host.h`, all 25 forwarding headers, `gsl.hpp`, `contracts.hpp`; `include/legends_ipc/{message_types,message_header,messages,wire_format,ipc_error,framebuffer_shm,audio_ring,control_channel,engine_spawner,shared_memory,message_codec}.h`; `include/pal/*` (listing); `src/legends/legends_embed_api.cpp` (lifecycle/error/macro/capture/save sections), `src/legends/internal/legends_instance.h`; `src/app/runtime_host.cpp`, `src/app/application.cpp` (runtime creation, direct-call sites), `src/main.cpp`; `src/legends_proxy/{proxy_api.cpp,proxy_connection.{h,cpp},ipc_error_mapping.h,crash_handler.cpp,heartbeat.cpp}`; `src/engine_host/{main.cpp,engine_dispatcher.cpp}`; `cmake/{ModuleDAG,ModuleManifest}.cmake`; `CMakeLists.txt` (targets 186-600, executables 1150-1300, install 1330-1390); `.github/workflows/ci.yml` (linux-ipc job); `README.md`, `ARCHITECTURE.md` (claims), `CHANGELOG.md`, `AUDIT.md` (baseline), `TODO.md` context; git log since 2026-02-24.
