# TLA+ Enhancement Audit

Date: 2026-02-27
Scope reviewed: all `spec/tla/*.tla` and `spec/tla/*.cfg` files in `C:\projectLegends`.

## What This Audit Covers

This audit is about **spec enhancement work** (not implementation conformance). It lists what should be added or strengthened so the TLA+ suite is more executable, less vacuous, and more useful for regression detection.

## Executive Summary

Current strengths:
- Broad module coverage across lifecycle, threading, PAL, determinism, capture, input, save/load, and error semantics.
- Good use of minimal CI models to control TLC state space.
- Explicit gate naming in several modules.

Main gaps to fix:
1. Composition/integration is still mostly documentation (`Composition.tla` is a dummy spec).
2. Several critical properties are placeholders, comments, or tautologies.
3. Some full specs and minimal specs diverge semantically (e.g., input extended-key domains).
4. Core device/operator modules are not all executable under CI (missing harness + `.cfg` coverage).
5. Action-level guarantees (wrong-thread, reentrancy, monotonic counters, tie-break determinism) are often under-specified as state predicates.

## Priority P0 (Add First)

### 1) Replace non-executable integration stubs with real composition
- `spec/tla/Composition.tla`:
  - Replace `dummy__` placeholder spec (`Init/Next/Spec` around lines 245-249) with real `INSTANCE`-based composition.
  - Add shared-variable wiring between subsystem modules (at minimum lifecycle/threading/reentrancy/PAL/determinism/save-state).
  - Add actual cross-module invariants (currently commented docs only).

### 2) Remove placeholder operators from top-level kernel spec
- `spec/tla/EmuKernel.tla`:
  - Replace placeholder `Serialize`/`Deserialize` (lines ~347-349) with real linkage to save-state model.
  - Replace `TraceMatchesExpected == TRUE` placeholder (line ~392) with concrete trace-matching predicate.
  - Move scheduler logic to a real integration with `Scheduler` operators instead of duplicated inline helpers.

### 3) Eliminate vacuous/tautological safety formulas
Add real predicates where formulas are currently always true or structurally trivial.
- `APIContract.tla`:
  - `Gate_CaptureFormat` (`x = x`), `Gate_CaptureBackendIndependent` (`f(x)=f(x)`), and several permissive gates should become concrete behavioral constraints.
- `Capture.tla` / `CaptureMinimal.tla`:
  - `FormatFixed` currently tautological; model actual `pitch`, `bytes_per_pixel`, and row-size constraints.
- `Determinism.tla` / `DeterminismMinimal.tla`:
  - `HashStability` is tautological; replace with transition-sensitive property (hash changes iff modeled hash inputs change).

### 4) Fix determinism replay semantics in full model
- `spec/tla/Determinism.tla`:
  - `StartReplay`/`CompleteReplay` needs a real replay execution path; current transition sequence can violate replay intent.
  - Add explicit replay cursor/index and replay step action.
  - Add invariant linking replay progression to recorded trace, not just a single equality check.

### 5) Fix type-domain mismatch in full input model
- `spec/tla/Input.tla`:
  - `TypeOK` constrains `keyState \subseteq 1..127`, but extended key handling stores `scancode + 256`.
  - Add explicit extended-key domain (as done in `InputMinimal.tla`) and align full/minimal semantics.

## Priority P1 (High-Value Additions)

### Scheduler family
- `Scheduler.tla`:
  - Add executable state-machine actions (currently commented placeholders around `ProcessOneEvent`/`AdvanceTimeAction`).
  - Add total deterministic ordering when deadline and tieKey collide (e.g., add `id` tie-break).
  - Add explicit liveness formulas (`NoEventsLost`, progress) and check them in a model harness.
- `SchedulerMinimal.tla` and `SchedulerTest.tla`:
  - Add `.cfg` files and run in CI.
  - Add properties for cancellation correctness and time-jump correctness as checked properties.

### Bus/PIC/PIT/DMA family
- `Bus.tla`:
  - Add executable bus harness with state and `Spec` (currently operator library only).
  - Convert ownership-discipline comments into actual action invariants.
  - Add deterministic overlap policy if overlaps are allowed, or enforce disjointness globally.
- `PIC.tla`, `PIT.tla`, `DMA.tla`:
  - Add dedicated harness modules/configs (or upgrade existing tests to first-class CI specs).
  - For PIC: model cascaded PIC behavior and EOI variants.
  - For PIT: add mode-specific correctness + periodicity checks.
  - For DMA: add richer transfer semantics (address/base/terminal-count protocol), not only count/mask.
- `DMATest.tla`, `InterruptTest.tla`, `BusTest.tla`:
  - Add standard `Init/Next/Spec` naming for main scenario and provide `.cfg` for CI.

### Save-state family
- `SaveState.tla`:
  - Fix snapshot typing (`DOMAIN Serialize` usage in `TypeOK` is not a good type model).
  - Add deterministic ID regeneration (avoid unconstrained `CHOOSE` per event).
  - Add CRC/version/migration semantics comparable to `SaveStateTest.tla`.
  - Add `.cfg` and CI execution for this module directly.
- `SaveStateTest.tla`:
  - Add stronger structure checks for `snap`/`loaded` records in `TypeOK`.
  - Add property for version migration correctness (`V2 -> V3`) as a checked invariant/property.

### Lifecycle/Threading/Reentrancy families
- Replace permissive wrong-thread/reentrancy formulas with strict error guarantees.
- Convert action-like expectations into temporal/action properties where needed (instead of loose state predicates).

Specific upgrades:
- `Lifecycle.tla`:
  - `ReentrancySafe` currently references primed state in a state-style invariant; restructure as action property or temporal formula.
  - Add explicit property for "wrong-thread call cannot return OK" under call attempt conditions.
- `Threading.tla` and `ThreadingMinimal.tla`:
  - Strengthen `WrongThreadDetected` / `WrongThreadBlocked` so they are not satisfied by permissive disjunctions.
  - Add explicit mutual exclusion property for core entry/exit segments.
- `Reentrancy.tla` and `ReentrancyMinimal.tla`:
  - Add explicit invariant/property for reentrant attempt implies `REENTRANT_CALL`.
  - Add callback-origin constraints to tie API calls to phase transitions.

### PAL/Capture/Input/API contract strengthening
- `PAL.tla`/`PALMinimal.tla`:
  - Add explicit monotonic drop-counter property (action/temporal), not just non-negative bound.
  - Add fairness assumptions tied to drain actions with non-empty queue preconditions.
- `Capture.tla`/`CaptureMinimal.tla`:
  - Add content-level capture invariants (not only dimensions).
  - Add per-mode coordinate domains in actions (avoid hardcoded `0..79`, `0..24` exploration bounds in full spec).
- `Input.tla`/`InputMinimal.tla`:
  - Add transactional text-input semantics (all-or-nothing multi-byte/key sequence append).
  - Add explicit relation between make/break bytes and key-state transitions.
- `APIContract.tla`:
  - Replace synthetic gate formulas with projections/refinement of subsystem properties.
  - Add explicit coverage checks for all 23 gates with non-vacuous formulas.

## Priority P2 (Spec Hygiene and Maintainability)

### 1) Add theorem/proof scaffolding
- Introduce `THEOREM` blocks (or proof obligations) for key lemmas currently only in comments.
- Candidate modules: `BusTest.tla`, `Scheduler.tla`, `Composition.tla`.

### 2) Add explicit assumptions and constraints
- Add assumptions on bound constants (`Max* > 0`) where missing.
- Add state constraints in `.cfg` for expensive full specs to avoid accidental explosion.

### 3) Standardize modeling idioms across full/minimal specs
- Keep type domains, naming, and error semantics aligned between full and minimal variants.
- Track intentional abstraction differences in a single section in each minimal spec.

### 4) CI coverage completion
Add CI TLC runs for currently uncovered models:
- `BusMinimal` or `BusTest`
- `SchedulerMinimal` and `SchedulerTest`
- `InterruptTest`
- `DMATest`
- (optionally) `SaveState` full model with restricted constants

## Concrete File-Level Additions Checklist

### `spec/tla/Composition.tla`
- Add real module composition via `INSTANCE`.
- Add cross-module invariants executable by TLC.
- Remove dummy variable/spec scaffold.

### `spec/tla/EmuKernel.tla`
- Integrate `Scheduler`, `PIC`, `PIT`, `DMA`, `Bus` semantics directly.
- Replace placeholders (`Serialize`, `Deserialize`, `TraceMatchesExpected`).
- Add kernel-level deadlock/progress properties and check them.

### `spec/tla/Scheduler.tla`
- Add concrete `VARIABLES`, `Init`, `Next`, `Spec` harness (or dedicated wrapper module).
- Add deterministic tie-break by `(deadline, tieKey, id)`.
- Add checked liveness properties (`NoEventsLost`, progress).

### `spec/tla/PIC.tla`, `spec/tla/PIT.tla`, `spec/tla/DMA.tla`, `spec/tla/Bus.tla`
- Add executable harness specs and CI configs.
- Promote comment-only lemmas to checked invariants/properties.

### `spec/tla/SaveState.tla`
- Rework snapshot typing and event-ID restoration.
- Add integrity/corruption/version semantics.
- Add standalone model config and CI check.

### `spec/tla/Determinism.tla`
- Rebuild replay semantics with explicit replay execution.
- Replace weak `HashCollisionFree`/`HashStability` with meaningful checks.

### `spec/tla/Input.tla`
- Align key-state type domain with extended key encoding.
- Add transactional/atomic text-input modeling.

### `spec/tla/APIContract.tla`
- Replace gate tautologies with behavior-coupled formulas.
- Use subsystem-derived properties instead of duplicate lightweight formulas.

### `spec/tla/*.cfg`
- Add missing cfg files for uncovered test/harness modules.
- Add `PROPERTIES` coverage where liveness exists but is not currently checked.

## Suggested Execution Order

1. Composition + EmuKernel placeholders removal.
2. Tautology cleanup (APIContract, Capture, Determinism).
3. Input type mismatch and replay semantics fix.
4. Scheduler/Bus/PIC/PIT/DMA harness + cfg + CI integration.
5. SaveState full-model hardening.
6. Cross-module theorem/proof scaffolding and final CI tuning.

## Definition of Done for This Audit Backlog

- No placeholder `TRUE`/identity formulas used as contract gates.
- No dummy composition module.
- All core subsystems have at least one executable TLC harness in CI.
- Full/minimal variants are semantically aligned (or differences explicitly documented).
- Liveness properties are present and actually checked where fairness is declared.
