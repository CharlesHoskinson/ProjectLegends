# Thread Safety Contract

## Overview

Project Legends enforces a single-owner-thread model. All API calls for a
given `legends_handle` must be serialized by the caller on the same thread
that created the handle.

## Thread-Safe Functions

These functions may be called from any thread:

- `legends_get_api_version()` — stateless query
- `legends_force_destroy()` — uses atomic CAS on the global instance pointer

## Thread-Affine Functions (Owner Thread Only)

All other `legends_*` functions must be called from the thread that called
`legends_create()`. Violation returns `LEGENDS_ERR_WRONG_THREAD`.

This is enforced at runtime via `LEGENDS_CHECK_THREAD()`, which compares
`std::this_thread::get_id()` against `inst->owner_thread_id`.

## Reentrancy

Calling `legends_step_ms()` or `legends_step_cycles()` from within a
callback (log callback, event callback) returns `LEGENDS_ERR_REENTRANT_CALL`.

The guard is `inst->in_step`, set to `true` for the duration of each step.

## Callbacks

- **Log callback** (`legends_set_log_callback`): Invoked on the owner thread
  during step execution. Must not call any `legends_*` function.
- **Event callback** (`legends_register_event_callback`): Invoked on the owner
  thread when the corresponding event fires. Must not call any `legends_*`
  function.

## Internal Engine State

The DOSBox-X engine subsystems (CPU, PIC, VGA, keyboard, DMA) are not
thread-safe. All engine access goes through the single `legends_handle`
and is protected by the owner-thread constraint.

## CI Enforcement

ThreadSanitizer (TSan) is enabled in the CI pipeline as a Linux-only
Clang build variant. TSan detects data races, lock-order inversions,
and thread-safety annotation violations at runtime.
