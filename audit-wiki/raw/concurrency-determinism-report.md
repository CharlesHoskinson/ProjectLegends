# Concurrency, Determinism & TLA+ Conformance Audit

- **Auditor role:** Concurrency, determinism & TLA+ conformance
- **Audit date:** 2026-06-09 (HEAD `ef11f20`, 115 commits since prior audit baseline 2026-02-24)
- **Prior references:** `C:\projectLegends\AUDIT.md` (2026-02-24), `C:\projectLegends\TLA_CONFORMANCE.md` (2026-02-24), `C:\projectLegends\tlaAudit.md` (2026-02-27)
- **Scope:** threading guarantees, step determinism, event ordering, audio/timer thread interactions, status of prior findings C2/H2/H3/H4/M1/M3/M7/M10, TLA+ invariant conformance at HEAD.

---

## 1. Executive summary

Since 2026-02-24 the project has made real progress on the *thread-discipline* half of this scope: the `get_instance()` handle fallback is gone, `dosbox_lib_get_context_ptr()` now enforces thread affinity, `legends_text_input()` is transactional, the `in_step` reentrancy guard was extended to the core mutating APIs, and `cpu_cycles` is range-validated. Four of the five NON-CONFORMANT TLA+ invariants from `TLA_CONFORMANCE.md` are fixed at HEAD, **but the conformance document was never re-baselined**, so the project's own paperwork understates its conformance while simultaneously overstating determinism.

The *determinism* half is in worse shape than the documents claim. The single most important discovery of this audit: **the "C2 fix" in the CPU bridge is vacuous.** `cpu_bridge.cpp` now calls `PIC_RunQueue()` and `CPU_Check_NMI()`, but the library build (`aibox_core`, which `legends_core` links) compiles the *stub* `PIC_RunQueue()` from `cpu_library_stubs.cpp` that does nothing and returns false. The real PIC (`engine/src/hardware/pic.cpp`) is not part of any CMake target. Consequently there is no timer tick, no IRQ delivery, no PIC event queue, and `events_processed` is always 0 in every legends step. The deterministic-emulation promise currently covers raw x86 instruction streams only — no device time.

Secondary new findings: the SHA-256 determinism hash (Fast mode) excludes CPU GPRs/EIP and RAM contents, so `legends_verify_determinism()` and the at-scale determinism tests cannot detect most real divergence; the IPC proxy does not match responses to requests by sequence or type (one timeout permanently desynchronizes the protocol); the cross-process audio ring violates SPSC by letting the writer mutate `read_index`; and TSan is `allow_failure` in CI with known races named in a comment.

---

## 2. Status of prior AUDIT.md findings in this scope

### C2 — CPU bridge skips PIC_RunQueue / CPU_Check_NMI → **CONFIRMED OPEN (fix is cosmetic)**

The bridge now contains the calls the prior audit asked for:

```cpp
// engine/src/misc/cpu_bridge.cpp:112-119
// Process pending PIC events before CPU execution (C2 fix)
if (PIC_RunQueue())
    result.events_processed++;

Bits ret = (*cpudecoder)();

// Check for NMI after execution (C2 fix)
CPU_Check_NMI();
```

However, which `PIC_RunQueue` links is decided by the build:

- `engine/CMakeLists.txt:156-199` (`AIBOX_CORE_SOURCES`) compiles `src/cpu/cpu_library_stubs.cpp` (line 198) and does **not** compile `src/hardware/pic.cpp`. A repo-wide grep confirms `hardware/pic.cpp` appears in **no** CMake target; only `dma_compat.cpp`/`memory_compat.cpp` from `hardware/` are built (engine/CMakeLists.txt:186-188).
- `engine/src/cpu/cpu_library_stubs.cpp:53-60`:
  ```cpp
  Bitu PIC_IRQCheck = 0;
  Bitu PIC_Ticks = 0;
  bool PIC_RunQueue(void) {
      // Stub: no PIC event queue in library mode yet.
      return false;
  }
  ```
- The legends wrapper links this build: root `CMakeLists.txt:201-203` (`legends_core` → `aibox_core`).

`CPU_Check_NMI()` does resolve to the real implementation (`engine/src/cpu/cpu.cpp:635`, compiled via `AIBOX_CORE_SOURCES`), so the NMI half of C2 is genuinely fixed. The PIC half is not. Consequences at HEAD:

1. No PIC event queue exists in library mode; scheduled events (PIT IRQ0, keyboard IRQ1, mixer per-ms handlers) never fire during `legends_step_cycles`/`legends_step_ms`.
2. `TIMER_AddTick()` (`engine/src/hardware/pic.cpp:807`) is never called anywhere on the step path (`dosbox_lib_step_cycles`, dosbox_library.cpp:543-607 → `execute_cycles`, cpu_bridge.cpp:79-150) — virtual device time literally does not advance, only `total_cycles` does.
3. `result.events_processed` is always 0 (stub returns false), so the value reported through `legends_step_result_t.events_processed` (legends_embed_api.cpp:1171) is misleading API surface.

**Latent bug for the future fix:** the bridge's cycle accounting only works with the stub. The *real* `PIC_RunQueue` (engine/src/hardware/pic.cpp:738-740) executes `CPU_CycleLeft += CPU_Cycles; CPU_Cycles = 0;` and then reloads `CPU_Cycles` with the window to the next PIC event. The bridge sets `CPU_Cycles = budget` *before* calling `PIC_RunQueue` (cpu_bridge.cpp:110-113) and computes `consumed = budget - CPU_Cycles` after the decoder (line 122). Linking the real PIC without restructuring the loop will corrupt the consumed-cycle math and the `CPU_Cycles = saved` restore at line 130. The fix needs a Normal_Loop-style structure: per-ms slices, `PIC_RunQueue()` → decoder → `TIMER_AddTick()` repeated, with consumed cycles taken from `CPU_CycleLeft` deltas.

### H2 — Two unsynchronized thread_local context globals → **CONFIRMED OPEN (mitigated, downgrade to medium)**

Both globals still exist:
- `engine/src/aibox/machine_context.cpp:20` — `thread_local MachineContext* g_current_context`
- `engine/src/misc/dosbox_context.cpp:65` — `thread_local dosbox::DOSBoxContext* g_current_context`

Mitigation since Feb: `legends_step_cycles` now installs **both** guards for the entire step scope, including input draining — `dosbox::ContextGuard dosbox_guard(*dctx)` (legends_embed_api.cpp:1098) and `legends::compat::ContextGuard legend_guard(*inst->machine)` (line 1101). Engine-side entry points (`dosbox_lib_init` line 443, `dosbox_lib_step_cycles` line 557, `dosbox_step` dosbox_context.cpp:999) each install their own guard. The pointers are consistent inside guarded scopes; the residual risk is non-step engine API calls that consult `aibox::compat::current()` without the legends guard installed. Architecture unchanged → keep open, severity reduced.

### H3 — `MachineContext::step()` TODO stub → **CONFIRMED OPEN (now documented as deprecated dead path)**

`engine/src/aibox/machine_context.cpp:201-246`: the function is still a counter-incrementing no-op (line 229: `// No real CPU execution — counter increment only`), but a `DEPRECATED(M10)` banner (lines 201-204) now states all production execution routes through `dosbox_lib_step_cycles()`. `MachineContext::run()` (lines 248-257) still spins on this stub and would busy-loop forever if invoked. Recommend deletion rather than documentation.

### H4 — 7 stub `init_*` methods → **CONFIRMED OPEN (reclassified as intentional delegation)**

`machine_context.cpp:376-418`: `init_pic/init_pit/init_vga/init_input/init_sound/init_dos/init_bios` all still `return Ok();` immediately, now under a comment "H4/M5: These init stubs delegate to DOSBox-X engine bridge… intentional no-ops." Given H3/M10's deprecation, these stubs and the 7 forward-declared classes they correspond to are dead weight; fold their removal into the dead-path cleanup.

### M1 — Reentrancy guard only on step → **PARTIALLY RESOLVED (narrowed)**

`inst->in_step` is now checked in: `legends_reset` (legends_embed_api.cpp:1010), `legends_step_cycles` (1076-1082, with a scope guard clearing on all exits), `legends_key_event` (1509), `legends_key_event_ext` (1527), `legends_text_input` (1544), `legends_mouse_event` (1599), `legends_save_state` (1854), `legends_load_state` (2287). Still missing on mutating APIs added since: `legends_mount_drive` (2755), `legends_unmount_drive` (2819), `legends_joystick_event` (2906, writes guest RAM directly — see NEW finding conc-08), and the Phase-3 setters (midi/printer/ipx/glide/pc98, 2959-3155). The TLA `ReentrancyMinimal.PhaseConsistent`/`CallbackSafe` invariants move from PARTIAL toward conformant but are not closed.

### M3 — MixerState unsynchronized → **SUBSTANTIALLY RESOLVED in library mode (residual lows)**

- The migrated `MixerState` ring indices are now `std::atomic<uint32_t> work_in/work_out` (engine/include/dosbox/dosbox_context.h:458-459), with relaxed snapshots used only for serialization/hash (dosbox_library.cpp:141-142, 201-202).
- The headless audio provider `BufferAudio` is mutex-protected throughout (engine/src/platform/headless/buffer_audio.cpp:24-188). Residual nit: `push_samples` reads `is_open_`/`paused_` *before* taking the lock (lines 60-63) and `pause()` writes `paused_` without the lock (109-111) — benign-bool race, TSan-visible.
- The PAL SDL2 sink uses a correct acquire/release SPSC ring (src/pal/sdl2/audio_sink_sdl2.cpp:26-74). Residual nit: the audio callback reads non-atomic `volume_` written by `setVolume()` on another thread (lines 249-252, 275-279) — torn-float UB in theory, inaudible in practice.
- The vendored `engine/src/hardware/mixer.cpp` still has plain `Bitu work_in,work_out,work_wrap` (line 103) shared between `MIXER_CallBack` (SDL audio thread, line 798) and the tick handler — but that file is only reachable in the full DOSBox-X app build, not in any CMake target audited here. Crucially, in library mode **no audio is ever produced**: `aibox::headless::PushAudioSamples` (engine/src/aibox/headless_stub.cpp:270-276) has zero production callers (only `engine/tests/unit/test_audio_integration.cpp`), and nothing pushes into `g_context->buffer_audio()`. `legends_capture_audio` → `dosbox_lib_get_audio_samples` (dosbox_library.cpp:1919-1950) will always return 0 samples. Thread-safety conformance here is *vacuous* — same pattern as the PIC stub.

### M7 — `dosbox_lib_get_context_ptr` bypasses LIB_CHECK_THREAD → **RESOLVED**

`engine/src/misc/dosbox_library.cpp:655-666` now begins with `LIB_VALIDATE_HANDLE`, `LIB_CHECK_THREAD()` (line 660), and null checks. Closes TLA `ThreadingMinimal.CoreSingleThreaded` / `WrongThreadBlocked` partials.

### M10 — Dual divergent execution paths → **CONFIRMED OPEN (deprecated + quarantined)**

`dosbox_step()` (engine/src/misc/dosbox_context.cpp:973-1007) carries a `DEPRECATED(M10)` banner and grep confirms its only callers are `engine/tests/unit/test_dosbox_context.cpp:382,404`. The stub path still exists and still silently "succeeds" while executing nothing. Risk is contained; recommend removal in the same cleanup as H3/H4.

---

## 3. TLA+ conformance re-check at HEAD

`TLA_CONFORMANCE.md` (dated 2026-02-24) reports 33/49 conformant, 11 partial, 5 non-conformant. CI runs TLC on the minimal specs (`.github/workflows/ci.yml:572-615`). Re-checked against HEAD:

### The 5 NON-CONFORMANT invariants

| Spec / invariant | Feb status | HEAD status | Evidence |
|---|---|---|---|
| LifecycleMinimal `HandleConsistency` | NON-CONF (H5 fallback) | **FIXED** | `get_instance()` requires `handle == inst` — legends_embed_api.cpp:79-82; `legends_destroy` rejects non-matching handles (960-969); intentional-bypass moved to explicit `legends_force_destroy` (998-1004) |
| ErrorModel `NullHandleConsistent` | NON-CONF (H5) | **FIXED** | same mechanism |
| InputMinimal `BufferNotCorrupted` | NON-CONF (M2 partial commit) | **FIXED** | `legends_text_input` pre-checks `slots_needed` (4 for shifted chars) against `EFFECTIVE_CAPACITY - size()` before enqueuing anything — legends_embed_api.cpp:1554-1559 |
| ConfigValidation `AllFieldsValidated` | NON-CONF | **PARTIAL** | `cpu_cycles` validated 0-or-100..1000000 (legends_embed_api.cpp:841-847). **`memory_kb` is still not range-checked** — it flows straight into `mc.memory_size = memory_kb * 1024` (line 871); `audio_rate` field still absent from `legends_config_t` |
| PALMinimal `ThreadSafety` | NON-CONF (M3) | **MOSTLY FIXED / VACUOUS** | atomics + mutexes as detailed under M3 above; conformant largely because no audio callback thread exists in library mode |

### Sampled PARTIAL invariants

| Spec / invariant | HEAD status | Gap remaining / what would make it conform |
|---|---|---|
| ThreadingMinimal `CoreSingleThreaded` / `WrongThreadBlocked` / `NoDataRaces` | **FIXED** (M7, M3) except CI cannot prove it: TSan is `allow_failure` with known races (`g_active_instance`, `CrashBreadcrumb::add()`) per ci.yml:347-355 | Fix the named races, flip `allow_failure: true` off (ci.yml:355) |
| ReentrancyMinimal `PhaseConsistent` / `CallbackSafe` | **IMPROVED, still PARTIAL** | extend `in_step` to mount/unmount/joystick/Phase-3 setters (see M1) |
| SaveStateTest `ObservationPreserved` | **IMPROVED** | GPR/segment snapshot now serialized (`snapshot_cpu_gprs` call at dosbox_library.cpp:964, restore at 1400); RAM + VGA_REG + VRAM sub-blocks counted at dosbox_library.cpp:713-719 (commit `faababd`). Remaining: engine event-scheduler queue is *vacuously* preserved because the stub PIC has no queue — once real PIC lands, queue serialization (TLA_CONFORMANCE §4 item 2) becomes a real gap again |
| SaveStateTest `EventCountPreserved` / `EventDigestPreserved` | **VACUOUSLY CONFORMANT** | legends-layer `event_queue` (`EventQueueState`, src/legends/internal/instance_state.h:332-342) has **no producer anywhere** — it is only serialized (legends_embed_api.cpp:1921-1928), restored (2205-2206, 2480-2481), and hashed (2618-2623). It is always empty. Either wire it to real scheduled events or delete it; today it is dead state that suggests coverage that doesn't exist |
| CaptureMinimal `BackendIndependent` | **LARGELY FIXED** | `sync_state_from_engine` now pulls display mode, palette, text buffer, font, indexed pixels, cursor BDA from the engine (legends_embed_api.cpp:1626-1731) instead of leaving the synthetic test pattern |
| DeterminismMinimal `TraceDeterminism` | **marked CONFORMANT in doc — OVERSTATED** | see finding conc-07: the hash that "proves" determinism excludes architectural CPU state and RAM |
| Scheduler `DeterministicSelection` (non-CI) | **MOOT/DEFERRED** | no scheduler executes in library mode (stub PIC). Must be revisited as acceptance criteria for the C2 fix |

**Process finding:** `TLA_CONFORMANCE.md` has not been touched since the fixes landed; the repo's stated conformance (33/49) is stale in both directions. Re-baseline after each conformance-affecting sprint, ideally generated by a script that greps the cited anchors.

---

## 4. New findings

### conc-07 — Determinism verification hash is blind to GPRs, EIP, and RAM (HIGH)

`legends_get_state_hash` (legends_embed_api.cpp:2552-2627) hashes the engine hash + input queue + time + PIC mirror + the always-empty event queue. The engine hash uses **`HashMode::Fast`** (`dosbox_lib_get_state_hash`, dosbox_library.cpp:684). Fast mode covers:

- `CpuState::hash_into` (engine/src/misc/dosbox_context.cpp:103-130): **only cycle counters, auto-adjust flags, NMI flags, halted** — no GPRs, no EIP, no EFLAGS, no segment registers (those live in global `cpu_regs`/`Segs`, touched only by `snapshot_cpu_gprs` during save_state, dosbox_library.cpp:964).
- `MemoryState::hash_into` (685-688): metadata only — "We do NOT hash the actual memory contents in Fast mode".
- RAM and VRAM are included only under `HashMode::Full` (engine/src/misc/state_hash.cpp:300-305), which nothing calls.

Therefore `legends_verify_determinism` (legends_embed_api.cpp:2629-2696) and every determinism test that compares hashes (`tests/unit/test_determinism_at_scale.cpp` TwoRunsProduceSameHash:78-97, MidpointSaveLoadMatchesStraightRun:104-127; `engine/tests/determinism/determinism_harness.h:93-97`) will report "deterministic" for two executions that diverge in registers or memory as long as cycle counters match — which is exactly the failure mode replay divergence produces. The test architecture is good (two-instance identity, midpoint save/load); the oracle is weak.

**Fix:** add GPR/EIP/EFLAGS/segment snapshot into the Fast hash (cheap — 100 bytes, the `snapshot_cpu_gprs` helper already exists in cpu_bridge.cpp:166-179); add a `LEGENDS_HASH_FULL` option or env-gated Full mode for the determinism tests so RAM/VRAM are covered in CI. Effort S-M.

### conc-08 — `legends_joystick_event` mutates guest state, then returns an error; bypasses input queue and reentrancy guard (MEDIUM)

legends_embed_api.cpp:2906-2956: the function writes joystick axis timer counts and button bits directly into guest RAM (BDA 0x480/0x488) via `dosbox_lib_write_memory` (lines 2938, 2953) — and then `return LEGENDS_ERR_NOT_SUPPORTED;` (line 2955). Three distinct defects:

1. **Error-model violation:** state is mutated on a call that reports failure — violates ErrorModel/`SuccessRequiresValidState` semantics and REQ-EX-004's "error without modifying state". Looks like a collision between commit `7f86dd7` (stubs return NOT_SUPPORTED) and `4b4c43b` (real joystick implementation) — the implementation landed but the stub return value survived.
2. **No `in_step` guard** (contrast key/mouse at 1509/1599): callable from an engine callback mid-step.
3. **Determinism asymmetry:** key/mouse events go through the sequenced `input_state` queue drained at step start (`drain_input_to_engine`, 1741-1781) and are hashed (2577-2603); joystick state writes guest RAM immediately, unordered relative to queued input, and is invisible to the Fast hash (conc-07). Replays that include joystick input will not be faithfully ordered.

**Fix:** return `LEGENDS_OK`, add the `in_step` guard, and route joystick through the input queue as a third `InputEventType`. Effort S.

### conc-09 — IPC proxy never matches responses to requests; one timeout permanently desynchronizes the channel (HIGH)

`ProxyConnection::request<Resp>` (src/legends_proxy/proxy_connection.h:39-45) deserializes whatever message arrives next; `send_and_recv` (proxy_connection.cpp:74-88) sends with a fresh `sequence_id` (line 80) and then `recv(5000)` (line 85) — but **neither `msg->header.msg_type` nor `sequence_id` is ever compared** against the request. The engine host dutifully echoes `sequence_id` (src/engine_host/main.cpp:94-96), so the data needed for matching is on the wire and ignored.

Failure scenario: `legends_step_ms` with a large `ms`, or `legends_save_state` of a 64 MB RAM image, takes >5 s on the host side. `recv` times out, `request` returns an error to the caller, the host's late response stays queued in the pipe. The **next** request reads the stale response and `Resp::deserialize` reinterprets the wrong payload type (sizes permitting) — silently wrong step results, hashes, or capture data from then on, every response off by one. The hardcoded 5000 ms (proxy_connection.cpp:85) is not configurable per-operation.

The dormant `HeartbeatMonitor` (src/legends_proxy/heartbeat.cpp:36-72) compounds this when wired: it sends on the same `ControlChannel` from its own thread (line 48-49) **without** taking `ProxyConnection::mutex_`, and its `HeartbeatAck` responses would be consumed by `send_and_recv` as RPC responses. (Currently no production code instantiates `HeartbeatMonitor` — verify before wiring.)

**Fix:** in `send_and_recv`, loop on `recv` discarding messages whose `sequence_id != seq` (and assert expected response type in `request<Resp>` via a `Resp::type` check); on timeout, mark the channel desynced and force reconnect; route heartbeats through the same mutex with their own sequence space. Effort S-M.

### conc-10 — Cross-process audio ring violates SPSC: writer mutates `read_index` (MEDIUM)

`AudioRingBuffer::push` (src/legends_ipc/audio_ring.cpp:71-80): when full, the **writer** advances `read_index` (`++ri; header_->read_index.store(ri, release)`, lines 73-74) to drop the oldest frame. The reader concurrently does a read-modify-write of the same index (`pop`, lines 87-108: relaxed load at 87, unconditional store of its local `ri` at 108). Both sides storing `read_index` means lost updates: the reader can clobber the writer's bump and then re-read frames the writer is simultaneously overwriting (torn/duplicated audio), or the lap-detection at 91-95 mis-computes `avail`. Memory safety holds (`% capacity_` before indexing), but the queue is not linearizable. Additionally, `open()` trusts `header_->capacity_frames` from the shared region (`map_pointers`, lines 10-16) — a zero/corrupted header value makes `wi % capacity_` a divide-by-zero in the embedder process.

**Fix:** standard SPSC overflow policy — writer drops the *incoming* frames when full (never touches `read_index`), or use compare_exchange on `read_index` for the drop-oldest path; validate `capacity_frames`/`channels` from the header against the values passed to `open()`. Note the recent `static_assert(is_always_lock_free)` commit (`3e5f8ea`) addressed atomicity but not the protocol. Effort S.

### conc-11 — TSan is allow-failure in CI with known, named data races (MEDIUM)

`.github/workflows/ci.yml:347-355`: the thread-sanitizer job is `allow_failure: true`, with the comment *"TSan detects pre-existing data races in engine global state (g_active_instance), CrashBreadcrumb::add(), and cross-thread tests… Mark allow-failure until REQ-TH-004 mixer/global state fixes land."* REQ-TH-004's mixer fix has substantially landed (M3 above), but the gate was never re-tightened, so any new race introduced since lands silently. The named `CrashBreadcrumb::add()` race (src/app/crash_breadcrumb.cpp) is still untriaged in any audit doc.

**Fix:** triage the remaining TSan reports, add suppressions only for the intentional wrong-thread tests, then remove `allow_failure`. Effort M.

### conc-12 — Conformance/architecture documents stale vs HEAD (LOW)

`TLA_CONFORMANCE.md` (and the AUDIT.md conformance appendix) still report H5/M2/M7-derived non-conformances that are fixed, while reporting `TraceDeterminism` as CONFORMANT despite conc-07, and `EventCount/EventDigestPreserved` as meaningful despite the event queue having no producer. Stale conformance claims are themselves a process risk in a project whose selling point is verified determinism. Effort S (regenerate + add anchors).

### conc-13 — IPC runtime parity gap: SHM framebuffer/audio have no producer in engine_host (MEDIUM)

The proxy's `legends_capture_rgb` reads the shared-memory framebuffer (`src/legends_proxy/proxy_api.cpp:214-233` via `fb->read_if_new(0)`), and `connect()` creates both the framebuffer and audio SHM regions (proxy_connection.cpp:25-29). But on the host side, `FramebufferShm`/`AudioRingBuffer` are only `#include`d in `src/engine_host/main.cpp:9-10` — the dispatcher (engine_dispatcher.cpp, 43 cases) never opens or writes either region; there is no frame-publish step after `StepMsReq`/`StepCyclesReq` (engine_dispatcher.cpp:82-111). IPC-mode `capture_rgb` therefore always takes the `!frame` path and returns 0 bytes with `LEGENDS_OK` (proxy_api.cpp:223-226), silently diverging from in-process behavior. This is the modern reincarnation of M10's "dual paths with different behavior", one layer up — embedders switching `InProcessEngineRuntime` ↔ `IpcEngineRuntime` (include/legends/runtime_host.h:145, 263) get different observable results. TODO.md's "GPL v2 Process Isolation 2/16" suggests this is known-incomplete; it still deserves a tracked finding because the failure is silent success. Effort M (publish framebuffer + audio after each step in the host loop; bump SHM sequence).

---

## 5. Determinism assessment (step_ms / step_cycles / events / audio-timer)

**What is deterministic today (and verified):**
- `legends_step_ms` converts ms→cycles with the instance's fixed `cycles_per_ms` ratio (legends_embed_api.cpp:1196, `time_state.ms_to_cycles`), and `dosbox_lib_step_ms` likewise (dosbox_library.cpp:619-622). No wall clock enters the step path; `TimingState::hash_into` deliberately excludes wall-clock fields (dosbox_context.cpp:80-97).
- The single-owner-thread model is enforced consistently at both layers (`LEGENDS_CHECK_THREAD` everywhere in the C API; `LIB_CHECK_THREAD` on 40+ engine functions including, since this period, `dosbox_lib_get_context_ptr`).
- Input ordering is deterministic: monotonic sequence numbers, FIFO drain at step start (`drain_input_to_engine`, legends_embed_api.cpp:1741-1781), queue contents hashed.
- The engine host IPC loop is strictly single-threaded request/response (src/engine_host/main.cpp:69-105) — good for determinism by construction.
- Test design is right-shaped: two-instance hash identity, midpoint save/load vs straight run, replay traces (tests/unit/test_determinism_at_scale.cpp:78-127, engine/tests/determinism/).

**What undermines the determinism story:**
1. **No device time** (C2/conc-01): without PIC/PIT/timer ticks, "deterministic emulation" is currently "deterministic instruction interpretation". Any guest software that waits on IRQ0/BIOS tick will hang or spin identically-but-uselessly.
2. **Weak oracle** (conc-07): the hash compared by all determinism machinery misses registers and memory.
3. **Unordered side-channels** (conc-08): joystick writes bypass the sequenced input queue.
4. **Vestigial event queue**: `EventQueueState` is hashed and serialized but never populated — determinism evidence that looks stronger on paper than in code.
5. **Audio**: in library mode no audio is produced at all (vacuously deterministic); in IPC mode the ring has an SPSC defect (conc-10) and no producer (conc-13). When mixer integration lands, the per-ms mixer tick must be driven from virtual time (the step loop), not the SDL callback clock, or determinism breaks.

---

## 6. Suggested sprint themes

1. **"Make time real" — PIC/PIT integration into library mode (the C2 sprint, for real this time).** Compile a deterministic event queue (either `hardware/pic.cpp` behind `DOSBOX_LIBRARY_MODE` guards or a purpose-built minimal scheduler honoring `Scheduler.tla` tie-break rules), restructure `execute_cycles` into per-ms slices calling `PIC_RunQueue` → decoder → `TIMER_AddTick`, fix the `CPU_Cycles`/`CPU_CycleLeft` accounting interaction, serialize the queue in save states, and make `events_processed` truthful. Acceptance: PIC.tla / SchedulerMinimal invariants become testable; a guest BIOS tick counter advances under `legends_step_ms`.
2. **"Trustworthy oracle" — determinism hash and test hardening.** GPR/EIP/EFLAGS/segments into Fast hash; Full-hash (RAM+VRAM) variants of the at-scale tests in CI; fix `legends_joystick_event` (error code, guard, queue routing); delete or wire the vestigial `EventQueueState`; re-baseline TLA_CONFORMANCE.md.
3. **"IPC you can step on" — protocol robustness for the process-isolation runtime.** Sequence/type matching + timeout-desync recovery in `ProxyConnection`; SPSC-correct audio ring; framebuffer/audio producers in engine_host after each step; heartbeat wiring through the connection mutex.
4. **"Green TSan" — close the sanitizer gate.** Fix `g_active_instance` and `CrashBreadcrumb::add()` races, suppress intentional wrong-thread tests, remove `allow_failure` from the TSan job, and add the residual `BufferAudio`/`volume_` nits while in there.

---

## Appendix: file:line index of key evidence

| Claim | Evidence |
|---|---|
| Bridge calls PIC_RunQueue/CPU_Check_NMI | engine/src/misc/cpu_bridge.cpp:112-119 |
| Stub PIC_RunQueue | engine/src/cpu/cpu_library_stubs.cpp:53-60 |
| Stub compiled into aibox_core; pic.cpp absent | engine/CMakeLists.txt:156-199 (198) |
| legends_core links aibox_core | CMakeLists.txt:201-203 |
| No TIMER_AddTick on step path | grep: only engine/src/dosbox.cpp:512 + pic.cpp:807 (neither in aibox_core) |
| Two thread_local context globals | engine/src/aibox/machine_context.cpp:20; engine/src/misc/dosbox_context.cpp:65 |
| Dual guards during step | src/legends/legends_embed_api.cpp:1098, 1101 |
| step() stub deprecated | engine/src/aibox/machine_context.cpp:201-246 |
| dosbox_step deprecated, test-only callers | engine/src/misc/dosbox_context.cpp:973-1007; engine/tests/unit/test_dosbox_context.cpp:382,404 |
| init_* stubs | engine/src/aibox/machine_context.cpp:376-418 |
| in_step guard sites | legends_embed_api.cpp:1010,1076,1509,1527,1544,1599,1854,2287 |
| get_context_ptr thread check | engine/src/misc/dosbox_library.cpp:655-666 |
| get_instance strict match | legends_embed_api.cpp:79-82 |
| cpu_cycles validation; memory_kb unvalidated | legends_embed_api.cpp:841-847, 871 |
| text_input transactional | legends_embed_api.cpp:1554-1559 |
| MixerState atomics | engine/include/dosbox/dosbox_context.h:458-459 |
| BufferAudio locking (+pre-lock flag read) | engine/src/platform/headless/buffer_audio.cpp:60-63, 109-111 |
| PAL SPSC ring; volume_ race | src/pal/sdl2/audio_sink_sdl2.cpp:26-74, 249-252, 275-279 |
| No audio producer in library mode | engine/src/aibox/headless_stub.cpp:270-276 (callers: tests only) |
| Fast hash excludes GPRs/RAM | engine/src/misc/dosbox_library.cpp:684; engine/src/misc/state_hash.cpp:300-305; engine/src/misc/dosbox_context.cpp:103-130, 685-688 |
| GPRs serialized in save_state | engine/src/misc/dosbox_library.cpp:964, 1400; RAM/VGA sub-blocks 713-719 |
| verify_determinism uses weak hash | legends_embed_api.cpp:2552-2696 |
| Event queue has no producer | src/legends/internal/instance_state.h:332-342; writes only at legends_embed_api.cpp:1921-1928, 2205-2206, 2480-2481 |
| joystick_event defects | legends_embed_api.cpp:2906-2956 (write 2938/2953, return 2955) |
| Proxy no seq/type matching, 5s timeout | src/legends_proxy/proxy_connection.h:39-45; proxy_connection.cpp:74-88 |
| Host echoes sequence_id | src/engine_host/main.cpp:94-96 |
| Heartbeat sends off-mutex (dormant) | src/legends_proxy/heartbeat.cpp:36-72 |
| Audio ring writer mutates read_index | src/legends_ipc/audio_ring.cpp:71-80, 86-110 |
| IPC capture_rgb reads SHM nobody writes | src/legends_proxy/proxy_api.cpp:214-233; engine_dispatcher.cpp (no FB cases) |
| TSan allow-failure with named races | .github/workflows/ci.yml:347-355 |
| TLC CI specs | .github/workflows/ci.yml:572-615 |
