# Memory Safety & C++ Correctness Audit — Project Legends

Auditor scope: legends wrapper layer and engine boundary for memory errors and UB.
Audit date: 2026-06-09. Commit at HEAD: `ef11f20`.

Focus files actually read:
- `src/legends/legends_embed_api.cpp` (3220 lines, full read)
- `src/legends/internal/instance_state.h`, `legends_instance.h`
- `engine/src/misc/dosbox_library.cpp` (2268 lines; create/destroy/reset/step/save/load/memory/input)
- `engine/src/misc/cpu_bridge.cpp` (full)
- `engine/src/aibox/headless_stub.cpp` (state struct + reset)
- `engine/include/dosbox/engine_state.h` (size constants, struct layouts)
- `engine/include/dosbox/zero_rle.h` (codec contract)
- `engine/src/misc/dosbox_context.cpp` (memory allocation)

---

## Executive summary

The team has materially closed the prior memory-safety backlog in this scope. Of the
prior findings assigned to me, **H5, H6, H9, M7, M8, M9, M11 and C2 are all resolved**,
and the resolutions are real (not cosmetic). Save/load now uses `memcpy` into aligned
locals everywhere, memory bounds use the overflow-safe subtraction form, the engine
handle is a checked sentinel, and config strings are deep-copied in both layers.

However, the load-state path grew substantially (V5: RAM + VGA RLE sub-blocks) and that
growth introduced a **new critical heap buffer overflow** reachable from the public
`legends_load_state()` API: the engine deserializer trusts the attacker-controlled
`memory.size` field and uses it as the decompression capacity for the RAM blob without
ever checking it against the real allocation. There is also a **resource leak that
bricks the library** on the create error path, and **M6 remains partially open** (event
callbacks are still invoked unguarded across the C ABI).

Health grade: **C** — strong remediation of the old backlog, but one critical
corruption bug and one library-bricking leak are open in the very paths that were
recently expanded.

---

## Prior-finding verification (in scope)

| ID | Status | Evidence |
|----|--------|----------|
| H5 — destroy fallback kills active instance | **RESOLVED** | `get_instance()` (legends_embed_api.cpp:79-82) returns `nullptr` unless `handle == g_active_instance`; `legends_destroy()` returns `LEGENDS_ERR_NULL_HANDLE` for any invalid non-null handle (960-969). No `g_active_instance` fallback remains. |
| H6 — integer overflow in memory bounds | **RESOLVED** | `dosbox_lib_read_memory`/`write_memory` use subtraction form: `size > memory.size || address > memory.size - size` (dosbox_library.cpp:1723, 1747). |
| H9 — unaligned `reinterpret_cast` in save/load | **RESOLVED** | All section headers are `memcpy`'d into aligned locals (legends_embed_api.cpp:2094-2134, 2298-2300, 2364-2409); save builds header on stack then `memcpy`s it (1874-1878, 2033-2034). Engine layer does the same (dosbox_library.cpp:1101-1103, 1172-1173). |
| M6 — exception unwinding across `extern "C"` | **PARTIALLY RESOLVED** (still open) | Log path is now guarded (`LogState::log` try/catch, instance_state.h:50-57; create CAS path 808-815). But `fire_event()` invokes user event callbacks with **no** try/catch (legends_embed_api.cpp:744-749) and is called from `extern "C"` functions that have no surrounding try/catch (`legends_mount_drive` 2809/2814, `legends_unmount_drive` 2841/2846). See NEW finding mem-03. |
| M7 — `get_context_ptr` bypasses thread check | **RESOLVED** | `dosbox_lib_get_context_ptr()` now calls `LIB_CHECK_THREAD()` (dosbox_library.cpp:660). |
| M8 — sentinel handle validation null-only | **RESOLVED** | `HANDLE_SENTINEL = 0x444F5358`; `LIB_VALIDATE_HANDLE` checks equality (dosbox_library.cpp:44, 119-121); `dosbox_lib_destroy` rejects non-sentinel non-null (476). |
| M9 — shallow config copy dangling `const char*` | **RESOLVED** | Deep copy in both layers: legends `config_path_owned`/`working_dir_owned` (legends_embed_api.cpp:849-857; legends_instance.h:48-49); engine `g_config_path_owned`/`g_working_dir_owned` (dosbox_library.cpp:382-394). |
| M11 — ignored `get_context_ptr` return then deref | **RESOLVED** | `legends_step_cycles` checks `ctx_err != DOSBOX_LIB_OK || raw_ctx == nullptr` and returns before any `static_cast`/deref (legends_embed_api.cpp:1088-1096). |
| C2 — CPU bridge skips PIC_RunQueue/NMI | **RESOLVED** | `execute_cycles` calls `PIC_RunQueue()` before the decoder and `CPU_Check_NMI()` after (cpu_bridge.cpp:113-119). |

---

## NEW findings

### mem-01 (CRITICAL) — Heap buffer overflow: `dosbox_lib_load_state` trusts attacker-controlled `memory.size`

`engine/src/misc/dosbox_library.cpp:1300-1319` deserializes the memory section and
overwrites the live allocation descriptor verbatim from untrusted input:

```cpp
dosbox::EngineStateMemory mem{};
std::memcpy(&mem, ptr + header.memory_offset, sizeof(mem));
ctx->memory.size = static_cast<size_t>(mem.size);   // line 1303 — no validation
```

`EngineStateMemory.size` is a `uint64_t` (engine_state.h:265). `ctx->memory.base` is a
fixed allocation of `bytes + 65536` made once at create time
(dosbox_context.cpp:39-41); there is **no separate capacity field** — once `memory.size`
is overwritten the true allocation size is lost.

The RAM sub-block then decompresses *into* that buffer using the corrupted size as the
capacity bound (dosbox_library.cpp:1437-1450):

```cpp
case dosbox::V5_SUBTAG_RAM: {
    if (ctx->memory.base == nullptr || ctx->memory.size == 0) break;
    if (entry.orig_size > ctx->memory.size) break;          // checks the CORRUPTED size
    size_t decoded = dosbox::zero_rle_decode(
        ptr + entry.offset, entry.size,
        ctx->memory.base, ctx->memory.size);                // cap == corrupted size
```

`zero_rle_decode` honors its `cap` argument but `cap` is now the attacker value
(zero_rle.h:84-117). Because the codec is RLE, a handful of compressed input bytes
(`entry.size`, bounded by the legends buffer) expand to `memory.size` zero bytes — so a
tiny crafted blob writes hundreds of MB past a ~704 KB allocation.

Reachability: the public `legends_load_state()` forwards the engine slice unmodified
(`legends_embed_api.cpp:2442-2449`) after only validating that `engine_offset/engine_size`
lie inside the legends buffer. Integrity is plain **CRC32** at both layers
(dosbox_library.cpp:1129-1136; legends_embed_api.cpp:2332-2338) — not a MAC — so an
attacker computes valid checksums trivially. No reallocation or clamp exists anywhere in
the load path.

Secondary corruption from the same root cause, even with no RAM blob present:
- `dosbox_lib_reset` does `memset(memory.base + memory.size, 0xF4, 65536)`
  (dosbox_library.cpp:522-527) — a wild write at `base + corrupted_size`.
- `dosbox_lib_read_memory`/`write_memory` bounds checks (1723, 1747) now compare against
  the corrupted size, exposing the whole heap to read/write via the joystick BDA path
  and any embedder memory call.

Recommendation: never overwrite `ctx->memory.size` from the save. Validate
`mem.size == ctx->memory.size` (the create-time allocation) and reject with
`DOSBOX_LIB_ERR_INVALID_STATE` on mismatch; clamp the RAM/VRAM decode `cap` to the true
allocation independently of any deserialized field. Effort: S.

### mem-02 (HIGH) — Engine handle leak bricks the library on create error path

`legends_create`'s terminal `catch` deletes the wrapper but never tears down an
already-created engine instance (`legends_embed_api.cpp:951-957`):

```cpp
} catch (const std::exception& e) {
    inst->last_error = e.what();
    inst->machine.reset();
    g_active_instance.store(nullptr, std::memory_order_release);
    delete inst;                         // engine_handle NOT destroyed
    return LEGENDS_ERR_INTERNAL;
}
```

By the time control can reach this catch, `dosbox_lib_create()` and `dosbox_lib_init()`
may already have succeeded (lines 905-923), setting the engine's `g_instance_exists =
true` and allocating `g_context`. Any throw *after* init — e.g. `load_embedded_font()`
allocates a vector and can throw `bad_alloc` (legends_embed_api.cpp:939; instance_state.h:161-164)
— is caught here, but `dosbox_lib_destroy(inst->engine_handle)` is never called. The
engine is leaked **and** left in a zombie state: `g_instance_exists` stays `true`, so the
next `legends_create()` fails permanently with `DOSBOX_LIB_ERR_ALREADY_CREATED`
(dosbox_library.cpp:360-363) until the process restarts. The earlier engine-init failure
branch (914-922) handles this correctly with an explicit destroy; the catch block does
not. Note also the catch only handles `std::exception` (no `catch(...)`), so a
non-standard throw would escape the `extern "C"` boundary (UB).

Recommendation: in the catch, if `inst->engine_handle` is non-null call
`dosbox_lib_destroy(inst->engine_handle)` before `delete inst`; add a `catch(...)` arm.
Effort: S.

### mem-03 (MEDIUM) — M6 still open: event callbacks invoked unguarded across the C ABI

`fire_event()` calls the embedder's callback with no exception guard
(`legends_embed_api.cpp:744-749`):

```cpp
auto& cb = inst->event_callbacks[event_type];
if (cb.fn) cb.fn(event_type, data, data_size, cb.userdata);   // may throw
```

It is invoked from `extern "C"` functions that have **no** surrounding try/catch:
`legends_mount_drive` (2809, 2814) and `legends_unmount_drive` (2841, 2846). If an
embedder writes the callback in C++ and it throws, the exception unwinds through
`fire_event` and out across the C ABI boundary — undefined behavior. (The log-callback
half of original M6 is fixed; this half is not.) The `fire_event` call inside
`legends_step_cycles` is incidentally safe only because that function has its own
try/catch (1084, 1177).

Recommendation: wrap the `cb.fn(...)` invocation in `fire_event` with `try { ... }
catch (...) {}`, mirroring `LogState::log`. Effort: S.

### mem-04 (MEDIUM) — Cross-layer load atomicity gap (engine committed before wrapper staging can fail)

`legends_load_state` performs the engine load in "Phase 2" (legends_embed_api.cpp:2435-2453)
*before* staging the wrapper-layer sections. The comment frames this as the atomicity
fix, but it only guarantees atomicity in one direction. After the engine state is
mutated, "Phase 3" staging can still fail: `staged_indexed_pixels.resize(...)` may throw
`bad_alloc`, which is caught and returns `LEGENDS_ERR_OUT_OF_MEMORY` (2504-2509) **without
reverting the engine**. Result: the engine holds the loaded state while the wrapper layer
keeps its old `time_state`/`frame_state`/`pics`/`input_state` — a silently desynchronized
machine that later produces wrong hashes and frames. The same shape exists in the V2
loader (2228-2237). Severity is bounded because the only post-engine failure point is the
indexed-pixels allocation.

Recommendation: stage all allocations (including `indexed_pixels`) *before* the engine
load, or snapshot/restore engine state on wrapper-staging failure. Effort: M.

### mem-05 (LOW) — Non-portable raw-struct serialization with indeterminate padding in V3 saves

Several V3 sections are written by raw `memcpy` of structs that carry compiler padding and
native byte order, despite the format being described as "portable serialization":
`ScheduledEvent` (legends_embed_api.cpp:1927-1930), `SaveStateTime`/`SaveStateCPU`/
`SaveStatePIC`/`SaveStateFrameHeader` (1889, 1900, 1908, 1967). `ScheduledEvent`
(instance_state.h:303-310) has a `uint32_t id` followed by `uint64_t deadline`, forcing
4 bytes of padding at offset 4 plus trailing padding (sizeof == 24). After field
assignment those padding bytes are indeterminate, get written to the buffer, and are
covered by CRC32 — so two logically identical states need not produce byte-identical
saves, and a save written on one ABI will mis-deserialize on another. This does not affect
`legends_get_state_hash` (which hashes fields, not the raw buffer) or single-platform
round-trips, hence LOW.

Recommendation: serialize these sections field-by-field with the existing little-endian
helpers (as already done for `InputEvent`/`DMAChannelState`), or zero-init the structs and
treat the format as platform-local only. Effort: M.

---

## What is solid

- Bounds-validation macro discipline in the wrapper loader (`VALIDATE_SECTION_BOUNDS`,
  `VALIDATE_DATA_BOUNDS`, `VALIDATE_COUNT_MAX`, `SAFE_MULTIPLY_OR_ERROR`) is consistently
  applied and uses overflow-safe subtraction forms.
- `legends_capture_rgb` text and graphics paths are correctly bounded against
  `required_size`; cursor cell indexing is guarded by `cursor_x < columns && cursor_y <
  rows` (legends_embed_api.cpp:1368-1395).
- Single-instance lifecycle uses atomic CAS; destroy is thread-affinity-checked, so no
  double-free/UAF across the documented single-threaded contract.
- The CPU-bridge `CPU_Cycles` save/restore with debug assert (cpu_bridge.cpp:109-133) is
  clean; the 64KB `0xF4` guard region after guest RAM (dosbox_context.cpp:39-44) is a good
  defense-in-depth choice — undermined only by mem-01.

## Suggested sprint themes

1. **Harden untrusted deserialization (mem-01, mem-05).** Treat every length/size/offset
   field in both save formats as hostile: validate `memory.size`/VRAM size against real
   allocations, clamp all decode caps independently, and field-serialize padded structs.
   Add a fuzz target that mutates the *engine* memory/RAM-blob fields specifically.
2. **Error-path resource safety at the C ABI (mem-02, mem-03).** Audit every `extern "C"`
   entry point for (a) engine-handle cleanup on all throw/early-return paths and (b)
   exception containment around every embedder callback (`fire_event`). Add `catch(...)`
   arms.
3. **Load atomicity (mem-04).** Move all allocations ahead of any engine mutation, or add
   engine snapshot/rollback, so a failed load leaves the machine unchanged.
