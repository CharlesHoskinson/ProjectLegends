# DOSBox-X Library Contract

**Version:** 1.0 (V1 Contract)
**Status:** Draft
**Effective:** When library mode is enabled (`DOSBOX_LIBRARY_MODE=1`)

This document defines the invariants, guarantees, and restrictions that govern DOSBox-X when built as an embeddable library. Hosts embedding DOSBox-X may rely on these guarantees; violations are considered bugs.

---

## 1. Instance Model

### V1 Contract (Current)

**Single instance per process.**

- Only ONE active DOSBox context may exist at any time
- Sequential usage is supported: `create → use → destroy → create → use → destroy`
- Simultaneous contexts are NOT supported in V1
- Attempting to create a second context while one is active returns `ERR_ALREADY_INITIALIZED`

**Rationale:** DOSBox-X contains extensive global state. Full context isolation requires completing the global-to-context migration (Phase 2).

### V2 Contract (Future)

After Phase 2 context migration is complete, the contract will be revised to:

- Multiple simultaneous contexts per process
- Each context fully isolated
- Thread-safe creation/destruction

**Migration Milestone:** V2 becomes effective when the global registry shows 100% of determinism-relevant globals migrated.

---

## 2. Threading Model

**The core spawns NO threads in library mode.**

| Guarantee | Description |
|-----------|-------------|
| No background threads | Core does not create threads for timing, audio mixing, or I/O |
| Single-threaded execution | All emulation runs on the calling thread during `step_*()` |
| Callback safety | All host callbacks invoked from the calling thread |
| Thread affinity | Context must be used from the thread that created it |

**Rationale:** Thread spawning inside library code creates uncontrollable concurrency for the host. The host owns threading decisions.

**Host Responsibility:** If the host needs background emulation, the host spawns the thread and calls `step_*()` from that thread.

---

## 3. Time Model

**Emulated time advances ONLY via explicit `step_*()` API calls.**

| Guarantee | Description |
|-----------|-------------|
| Deterministic stepping | Same inputs + same step counts = same state |
| No wall-clock coupling | Core never reads host system time for emulation |
| Host-controlled pacing | Host decides when and how much to step |
| Frame timing | Display frames produced during stepping, not on timers |

**API:**
```c
// Advance emulation by milliseconds (converted to cycles internally)
int dosbox_step_ms(dosbox_handle h, uint32_t ms);

// Advance emulation by exact CPU cycles (for precise control)
int dosbox_step_cycles(dosbox_handle h, uint64_t cycles);
```

**Rationale:** Deterministic execution requires the host to control time. Wall-clock dependencies make replay, testing, and headless operation impossible.

---

## 4. Side Effect Prohibition

**The core does NOT perform process-affecting side effects.**

| Prohibited | Replacement |
|------------|-------------|
| `exit()` | Return error code via API |
| `abort()` | `DOSBOX_PANIC` → context enters Failed state |
| `_exit()` | Return error code via API |
| `chdir()` | Host provides working directory via config |
| `putenv()` / `setenv()` | Host provides environment via config |
| Signal handlers | Host owns signal handling |

**Rationale:** Process-affecting side effects prevent safe embedding. A library that calls `exit()` kills the host application.

**Migration Path:** Legacy code using `E_Exit()` is converted to:
- `DOSBOX_FAIL` for recoverable errors (returns error code)
- `DOSBOX_PANIC` for invariant violations (context enters Failed state)
- `DOSBOX_TRAP` for memory corruption (extremely rare, calls host handler)

---

## 5. Output Channels

**All output goes through callbacks or return values, never stdout/stderr.**

| Output Type | Channel |
|-------------|---------|
| Log messages | `dosbox_set_log_callback()` |
| Error details | `dosbox_get_last_error_string()` |
| Display frames | `IDisplay::upload_frame()` |
| Audio samples | `IAudio::push_samples()` |
| Emulation results | API return values |

**Prohibited:**
```c
printf(...)           // Use LOG_* macros instead
fprintf(stderr, ...)  // Use LOG_ERROR instead
std::cout << ...      // Use LOG_* macros instead
std::cerr << ...      // Use LOG_ERROR instead
```

**Rationale:** Direct console output interferes with host applications, especially GUI hosts, services, and embedded systems.

---

## 6. Error Handling

### Error Taxonomy

| Level | Macro | Behavior | Use Case |
|-------|-------|----------|----------|
| **FAIL** | `DOSBOX_FAIL(code, msg)` | Returns error, continues | Invalid input, missing file, parse error |
| **PANIC** | `DOSBOX_PANIC(msg)` | Context → Failed state | Internal invariant violation |
| **TRAP** | `DOSBOX_TRAP(msg)` | Calls host handler | Memory corruption (rare) |

### Error Recovery

| Context State | Allowed Operations |
|---------------|-------------------|
| `Created` | `init`, `destroy` |
| `Initialized` | `step_*`, `save_state`, `load_state`, `destroy` |
| `Running` | (internal state during step) |
| `Failed` | `destroy` only |
| `Destroyed` | None (handle invalid) |

After `DOSBOX_PANIC`, the context enters `Failed` state. Only `destroy` is valid; all other operations return `ERR_INVALID_STATE`.

### Host Handlers

```c
// Set custom panic handler (called on DOSBOX_PANIC)
void dosbox_set_panic_handler(
    void (*handler)(const dosbox_error* err, void* userdata),
    void* userdata
);

// Set custom trap handler (called on DOSBOX_TRAP)
void dosbox_set_trap_handler(
    void (*handler)(const dosbox_error* err, void* userdata),
    void* userdata
);
```

---

## 7. Memory Model

### Ownership

| Resource | Owner | Cleanup |
|----------|-------|---------|
| `dosbox_handle` | Host | `dosbox_destroy()` |
| Config strings | Host (copied on init) | Host frees after init |
| Callback userdata | Host | Host manages lifetime |
| Frame buffers | Core (during callback) | Invalid after callback returns |
| Error strings | Core (thread-local) | Valid until next API call |

### Allocation

- Core uses standard allocators (overridable in future)
- No custom allocator hooks in V1
- Host must not free core-owned memory
- Core must not free host-owned memory

---

## 8. Platform Abstraction

### Backend Model

The core uses abstract platform interfaces:

| Interface | Purpose |
|-----------|---------|
| `IDisplay` | Frame upload, mode setting |
| `IAudio` | Sample push (producer/consumer) |
| `IInput` | Event polling |
| `ITiming` | Host time queries (for throttling only) |

### Headless Mode

When `DOSBOX_HEADLESS=1`:
- Display backend accepts frames but does not present
- Audio backend accepts samples but does not play
- Input backend returns no events (or synthetic events from API)
- Full emulation runs without any host UI

---

## 9. Determinism Guarantees

### Tier 1 (Guaranteed)

Same binary + same OS + same CPU + same inputs = identical state hashes

**Requirements:**
- No uninitialized memory reads
- No host time dependencies in emulation
- No random sources in determinism-relevant code

### Tier 2 (Stretch Goal)

Same binary across OSes = identical state hashes

**Additional Requirements:**
- Portable floating-point behavior
- No OS-specific behavior in core

### Verification

```c
// Get SHA-256 hash of observable state
int dosbox_get_state_hash(dosbox_handle h, uint8_t out[32], int full_mode);
```

---

## 10. API Stability

### Stable (V1)

These APIs will not change incompatibly:
- `dosbox_create`, `dosbox_destroy`
- `dosbox_step_ms`, `dosbox_step_cycles`
- `dosbox_save_state`, `dosbox_load_state`
- `dosbox_get_state_hash`
- Error codes and their meanings

### Experimental

These APIs may change:
- Platform interface details (`IDisplay`, `IAudio`, etc.)
- Internal configuration options
- Debug/profiling APIs

---

## 11. Build Modes

| Mode | Define | Behavior |
|------|--------|----------|
| **Standalone** | (default) | Traditional executable, may use exit/printf |
| **Library** | `DOSBOX_LIBRARY_MODE=1` | All contract guarantees enforced |
| **Headless** | `DOSBOX_HEADLESS=1` | No host display/audio (implies Library) |

---

## 12. Contract Violations

If the core violates any guarantee in this contract while `DOSBOX_LIBRARY_MODE=1`, it is a bug. Please report:

1. Which guarantee was violated
2. Steps to reproduce
3. Build configuration
4. Host environment

---

## Appendix A: Quick Reference

### Safe to Call

```c
dosbox_create(&config, &handle);  // Create context
dosbox_step_ms(handle, 16);       // Advance ~1 frame
dosbox_step_cycles(handle, 1000); // Advance exactly 1000 cycles
dosbox_save_state(handle, ...);   // Serialize state
dosbox_load_state(handle, ...);   // Deserialize state
dosbox_get_state_hash(handle, hash, 0); // Quick hash
dosbox_get_state_hash(handle, hash, 1); // Full hash
dosbox_destroy(handle);           // Cleanup
```

### Forbidden in Library Mode

```c
exit(1);              // FORBIDDEN - use DOSBOX_FAIL
abort();              // FORBIDDEN - use DOSBOX_PANIC
printf("...");        // FORBIDDEN - use LOG_* macros
chdir("/path");       // FORBIDDEN - use config
system("cmd");        // FORBIDDEN - no shell access
```

---

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-01-14 | Initial V1 contract |
