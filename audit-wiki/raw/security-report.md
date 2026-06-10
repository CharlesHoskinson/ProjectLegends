# Security & Untrusted-Input Audit — Project Legends

Auditor role: Security & untrusted-input surfaces and isolation
Audit date: 2026-06-09
Commit context: HEAD (post-2026-02-24 prior audit; 115 commits since)
Scope: save-state deserialization, IPC message layer + dispatcher + proxy, shared-memory channels, guest-reachable surfaces, fuzzing coverage, and hardening posture vs roadmap Security Hardening / GPL Process Isolation REQs.

---

## Executive summary

The **save-state deserialization** path is the strongest part of this surface. Both the legends layer (`src/legends/legends_embed_api.cpp`) and the engine bridge (`engine/src/misc/dosbox_library.cpp`) validate magic, version, declared size vs underflow, CRC32 over the data region, and every section offset/length against the *checksummed* region with overflow-safe subtraction-form macros, with a four-phase atomic load. Two prior findings in this path are now fixed: **H6** (memory-bounds integer overflow) and **H9** (unaligned `reinterpret_cast`). **H7** (`HashMode::Full`) is partially fixed.

The weak part is the **IPC / shared-memory isolation layer** that did not exist at the prior audit. It is the GPL trust boundary (MIT shell ⇄ GPL engine host) and is, by design, the component that runs untrusted guest code — yet:

- The framebuffer and audio shared-memory **consumers trust geometry fields stored in attacker-mappable shared memory**, producing out-of-bounds reads in the trusted shell (SEC-01).
- The proxy **does not validate response message type or sequence id**, so any out-of-order or unsolicited message is misinterpreted (SEC-02).
- The IPC endpoints have **no peer authentication** and use predictable, world-reachable names with default ACLs and no squatting protection (SEC-03).
- The **108-message / 89-struct IPC parser and 43-case dispatcher are not fuzzed at all** (SEC-04).
- The GPL-isolation **guarantees are unverified**: CI builds and unit-tests IPC mode but performs no GPL symbol-isolation scan, no crash-recovery, and the SHM write path is not even wired into the host main loop (SEC-05).

IPC mode is opt-in (`LEGENDS_USE_IPC=OFF` by default), which bounds present-day exposure, but it is the stated roadmap direction and these issues block it from being a real security boundary. Save-state load is reachable in the default in-process build and is well-hardened.

Health grade: **C**.

---

## What is in good shape (evidence)

- **Legends-layer load validation** — `legends_load_state` validates header size, magic, version, `total_size >= header` (underflow guard), `total_size <= buffer_size`, CRC32 over the data region, then every section against `verified_size = total_size` using overflow-safe macros, plus per-count caps (`VALIDATE_COUNT_MAX`) and a pre-validation pass over input-event types before any mutation. `src/legends/legends_embed_api.cpp:2291-2428`.
- **Overflow-safe bounds macros** — `VALIDATE_SECTION_BOUNDS`/`VALIDATE_DATA_BOUNDS` use subtraction form (`size > buf - offset`) that cannot wrap. `legends_embed_api.cpp:706-724`.
- **H9 fixed** — header and every section are `memcpy`'d into aligned locals; no `reinterpret_cast` over caller buffers in the load path. `legends_embed_api.cpp:2298-2300,2364-2409`.
- **H6 fixed** — `dosbox_lib_read_memory`/`write_memory` now use `size > memory.size || address > memory.size - size`. `engine/src/misc/dosbox_library.cpp:1723,1747`.
- **Engine V5 load** — magic, forward-compatible version reject, size underflow guard, CRC32, per-section offset validation, and bounded RLE decode into fixed-size RAM/VRAM with `orig_size` clamps and per-entry bounds checks; this path *is* fuzzed. `dosbox_library.cpp:1106-1167,1409-1487`.
- **IPC payload cap** — `MessageCodec` rejects any frame claiming `payload_size > 64 MB` before allocation. `include/legends_ipc/message_codec.h:22`, `src/legends_ipc/message_codec.cpp:41-44`.
- **String-message deserializers** are bounds-checked (`buf.size() - 4 < len`) before constructing the string. `src/legends_ipc/messages.cpp:591-600` and peers.

---

## Findings

### SEC-01 (High) — Shared-memory consumers trust attacker-controlled geometry → OOB read in the trusted shell

The framebuffer header (`current_width`, `current_height`, `max_width`, `max_height`) and audio header (`capacity_frames`, `channels`) live *inside* the shared-memory region, which is written by the engine host — the untrusted, guest-code-running process the isolation is meant to contain. The consumer side trusts these fields without validating them against the actually-mapped region size.

Framebuffer:
- `FramebufferShm::read_if_new` computes `pixel_bytes = current_width * current_height * 4` from header fields and returns a `span` of that length into a buffer that is only `max_width*max_height*4` bytes; there is **no clamp** of `current_*` to `max_*` or to `buf_size_`. `src/legends_ipc/framebuffer_shm.cpp:74-92`.
- `legends_capture_rgb` then sets `*size_out = frame->pixels.size()` and, for a caller that sizes its buffer to that value (the documented two-call pattern), executes `std::memcpy(buffer, frame->pixels.data(), frame->pixels.size())` — reading `current_w*current_h*4` bytes out of an SHM buffer sized for `max_w*max_h*4`. A compromised host setting `current_width=current_height=0xFFFF` causes a multi-GB OOB read from the shell. `src/legends_proxy/proxy_api.cpp:222-232`.
- `map_pointers()` also derives `buf_size_` from the header's `max_width/max_height` (SHM-resident) rather than the size the region was actually mapped with. `framebuffer_shm.cpp:9-15`.

Audio ring (same root cause):
- `map_pointers()` caches `capacity_` and `channels_` from the SHM header. `pop()`/`push()` index `samples_[(idx % capacity_) * channels_ + c]`; an inflated `capacity_` or `channels_` reads/writes out of the mapped region, and a header `channels_ == 0` causes a divide-by-zero in `samples.size() / channels_`. `src/legends_ipc/audio_ring.cpp:10-16,63-110`.

Recommendation: validate all geometry on the consumer side against the mapped region size — clamp `current_* <= max_*`, require `pixel_bytes <= buf_size_`, reject `channels==0` and `capacity_frames` larger than what was mapped — and never recompute buffer extents from SHM-resident fields. Effort: M.

### SEC-02 (Medium) — Proxy does not validate response type or sequence id; async events desynchronize the stream

`ProxyConnection::request<Resp>` deserializes whatever bytes arrive as the expected `Resp` type, and `send_and_recv` returns the **first** message read after sending, with no check that `header.msg_type == Resp::type` or that `header.sequence_id == seq`. `src/legends_proxy/proxy_connection.h:39-45`, `src/legends_proxy/proxy_connection.cpp:74-88`.

Consequences at the GPL trust boundary:
- The protocol defines an unsolicited push message `EventNotification = 0x1102` (`include/legends_ipc/message_types.h:154`). If the host ever emits one, it is consumed as the next request's response and the entire request/response stream desynchronizes thereafter.
- A malfunctioning or malicious host can return a wrongly-typed but large-enough payload; `Resp::deserialize` succeeds and the shell reads attacker-chosen bytes as a valid `error_code`/result (e.g., a forged `LEGENDS_OK`).

Recommendation: in `send_and_recv`, loop discarding/cross-checking until a response whose `msg_type` matches the expected response and `sequence_id` matches the request is received; route `EventNotification` to a separate queue. Effort: S–M.

### SEC-03 (Medium) — IPC endpoints have no peer authentication and use predictable, world-reachable names

There is no authentication that the process on the other end of the control channel is the spawned engine host, and the handshake carries no token (`HandshakeAck` only has version + error_code; `src/legends_proxy/proxy_connection.cpp:36-43`, `src/engine_host/main.cpp:54-66`).

- POSIX: server socket at `/tmp/legends_<pid>.sock` (predictable; `/tmp` world-writable), created with the process umask and **no `SO_PEERCRED`** check on `accept`. `src/legends_ipc/platform/posix/control_channel_posix.cpp:51-107`. SHM is `shm_open(..., O_CREAT|O_RDWR, 0600)` with **no `O_EXCL`**, so a same-uid process can pre-create/size-confuse the region. `src/legends_ipc/platform/posix/shared_memory_posix.cpp:57-67`.
- Windows: `CreateNamedPipeA(..., nullptr)` (default DACL) with **no `FILE_FLAG_FIRST_PIPE_INSTANCE`** (name-squatting) and **no `PIPE_REJECT_REMOTE_CLIENTS`**, name `\\.\pipe\legends_<pid>`. `src/legends_ipc/platform/windows/control_channel_win.cpp:46-66`. SHM `CreateFileMappingA(..., nullptr, ...)` with default security and no `ERROR_ALREADY_EXISTS` check. `src/legends_ipc/platform/windows/shared_memory_win.cpp:62-68`.

Recommendation: add peer-credential checks (`SO_PEERCRED`/`getpeereid` on POSIX, `GetNamedPipeClientProcessId` on Windows), set `FILE_FLAG_FIRST_PIPE_INSTANCE` + `PIPE_REJECT_REMOTE_CLIENTS` + an explicit owner-only DACL, use `O_EXCL` on SHM create, prefer unguessable per-launch names in a 0700 runtime dir (or Linux abstract sockets), and include a random nonce in the handshake. Effort: M.

### SEC-04 (Medium) — IPC parsing layer is entirely unfuzzed

The four fuzz targets are `fuzz_legends_load_state`, `fuzz_engine_load_state`, `fuzz_input_injection`, `fuzz_config_parser` (`tests/fuzz/CMakeLists.txt`; CI runs them at `.github/workflows/ci.yml:496-543`). None of them exercise the IPC surface, which is the largest hand-rolled parser in the project: ~89 `deserialize()` functions (`src/legends_ipc/messages.cpp`, 905 lines), the framing `MessageCodec`/`MessageHeader`, and the 43-case `dispatch()` (`src/engine_host/engine_dispatcher.cpp`) — all parsing untrusted bytes at the GPL trust boundary. The roadmap claims "round-trip serialization tests for all IPC message types" (REQ-ISO-004), and unit tests exist (`tests/unit/test_ipc_messages.cpp` etc.), but those are well-formed inputs, not adversarial.

Recommendation: add a libFuzzer target that feeds raw bytes through `MessageCodec::feed/try_decode` and then through `dispatch()` (and, separately, drives each `Resp::deserialize` for the proxy side). Effort: S–M.

### SEC-05 (High) — GPL process-isolation guarantees are unverified; the "missing half" is the assurance, not the plumbing

TODO.md still lists GPL v2 Process Isolation as "STUB — 2 of 16 (license files), 14 missing" and "IPC isolation: STUB ONLY" (`TODO.md:19,257`), and roadmap marks REQ-ISO-003…016 all "Missing" (`roadmap.md:3319-3332`). In reality the *mechanism* is now substantially built — `LEGENDS_USE_IPC` builds `legends_engine_host` + `legends_proxy` (`CMakeLists.txt:372-431`), with a CI job that configures, builds, and runs unit tests in IPC mode (`.github/workflows/ci.yml:93-127`). The genuinely missing part is the **security/legal assurance**:

- **No REQ-ISO-016 GPL symbol-isolation scan** in CI — the linker-map/`nm` check that proves zero `aibox_core`/`legends_core` GPL symbols leak into the proprietary shell is absent (CI only does `test -f build/legends_engine_host`). This is the core GPL-compliance guarantee and it is unenforced. `ci.yml:121-124`.
- **No REQ-ISO-013 crash detection/recovery** — `crash_handler.cpp`/`heartbeat.cpp` exist but the host main loop has no watchdog/restart, so a crashed (or killed) GPL engine just breaks the pipe.
- **Write path unwired** — `src/engine_host/main.cpp` connects only the control channel; it never opens the framebuffer or audio SHM, so the engine host does not actually publish frames/audio in IPC mode. `src/engine_host/main.cpp:20-108`.

Taken together, IPC mode is a *functional* transport but **not yet a trustworthy isolation boundary**, and the documentation (TODO/roadmap) understates the code while overstating the guarantees. Recommendation: implement the REQ-ISO-016 symbol scan as a CI gate, wire crash recovery, finish the SHM write path, and reconcile TODO/roadmap status. Effort: XL (this tracks the 14 missing ISO REQs).

### SEC-06 (Low) — `MountDriveReq` path length truncated to 8 bits while full bytes are copied

`MountDriveReq::serialize` writes the path length as a single byte (`write_u8(buf, 5, static_cast<uint8_t>(host_path.size()))`) but `serialized_size_dynamic()` and the `memcpy` use the full `host_path.size()`. For a path longer than 255 bytes the recorded length wraps, so `deserialize` reconstructs a silently truncated path. `src/legends_ipc/messages.cpp:341-359`. Because the mount host path feeds path-confinement (REQ-SEC-023 canonical resolution), a truncated path is at best a correctness bug and at worst resolves to an unintended directory. Recommendation: use a `u16`/`u32` length and reject oversize paths explicitly. Effort: S.

---

## Prior-audit findings verified in passing

- **H6 (Integer overflow in memory bounds)** — RESOLVED. Subtraction form at `engine/src/misc/dosbox_library.cpp:1723,1747`.
- **H7 (`HashMode::Full` contract mismatch)** — PARTIALLY RESOLVED. `HashMode::Full` now hashes all conventional RAM (`engine/src/misc/state_hash.cpp:300-303`) but still omits VGA registers/VRAM and device state (acknowledged in-code as "added in Phase B"). Contract is closer but not yet met.
- **H9 (Unaligned `reinterpret_cast` in save/load)** — RESOLVED in the load path (memcpy-to-local throughout `legends_load_state`).

---

## Sprint recommendations

1. **Harden the SHM boundary (SEC-01, SEC-02).** Clamp/validate all consumer-side geometry against the mapped region; add response-type + sequence-id matching in the proxy and a separate event queue. These are the directly exploitable items reachable from a compromised engine host.
2. **Authenticate and lock down the IPC endpoints (SEC-03).** Peer-credential checks, first-instance/reject-remote/owner-only ACLs, `O_EXCL`, unguessable names, handshake nonce.
3. **Fuzz the IPC surface (SEC-04).** Byte-level fuzzers for `MessageCodec` + `dispatch()` and for each proxy-side `Resp::deserialize`, wired into the existing CI fuzz job.
4. **Make isolation a verifiable guarantee (SEC-05).** Add the REQ-ISO-016 GPL symbol-scan CI gate, crash detection/recovery, finish the SHM write path, and reconcile TODO/roadmap status with the code that already exists.
