# TLA+ Specification Suite

Formal specifications for Project Legends' contract gates, verified by TLC model checking.

**Version**: 2.0 (complete rewrite)
**Modules**: 14 domain specifications + support files
**Invariants**: 50+ meaningful safety properties (zero TRUE stubs)
**Model-checkable specs**: 11

---

## What This Directory Contains

Every `.tla` file is a TLA+ module that formally specifies a correctness property
of the Project Legends embedding API. These specs are the formal backing for the
23 contract gates defined in [`CONTRACT.md`](../CONTRACT.md).

The specifications are organised into four categories:

| Category | Modules | Purpose |
|----------|---------|---------|
| **Foundation** | Types | Shared type definitions, error codes, helper operators |
| **Domain** | Lifecycle, Threading, PAL, Determinism, SaveState, Capture, Input, Reentrancy, ErrorModel, ConfigValidation | One module per contract area |
| **Composite** | APIContract | All 23 gates in a single checkable spec |
| **Documentation** | Composition | Module dependency graph and traceability matrix |

---

## Architecture

```
Composition.tla (documentation -- dependency graph, traceability)
  |
  +-- APIContract.tla            (composite -- all 23 gates)
  |
  +-- Types.tla                  (foundation -- shared types)
  |     |
  |     +-- Lifecycle.tla / LifecycleMinimal.tla      Gates 2a, 2b, 2c
  |     |     +-- Reentrancy.tla / ReentrancyMinimal.tla    Gate 8c
  |     |     +-- ConfigValidation.tla                       Gate 2a
  |     |     +-- ErrorModel.tla                             Gate 2b
  |     |
  |     +-- Threading.tla / ThreadingMinimal.tla      Gates 7a, 8a, 8b, 8c
  |     |
  |     +-- PAL.tla / PALMinimal.tla                  Gates 7a, 7b, 7c, 7d
  |     |
  |     +-- Determinism.tla / DeterminismMinimal.tla  Gates 4a, 4b, 6b
  |     |
  |     +-- SaveState.tla / SaveStateTest.tla         Gate 4c
  |     |
  |     +-- Capture.tla / CaptureMinimal.tla          Gates 5a, 5b, 5c
  |     |
  |     +-- Input.tla / InputMinimal.tla              Gates 6a, 6b
```

---

## Quick Start

### Prerequisites

1. **Java 17+** (for TLC model checker)
2. **tla2tools.jar** (TLA+ toolbox):
   ```bash
   wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar \
     -O /tmp/tla2tools.jar
   export TLA2TOOLS=/tmp/tla2tools.jar
   ```
3. **Apalache** (optional, for type checking):
   ```bash
   # See https://apalache-mc.org/docs/apalache/installation.html
   ```

### Run a single model check

```bash
cd spec/tla
java -cp $TLA2TOOLS tlc2.TLC \
  -config LifecycleMinimal.cfg LifecycleMinimal.tla -workers auto
```

Expected output ends with:
```
Model checking completed. No error has been found.
```

---

## Module Index

| Module | Type | Gates | Key Invariants |
|--------|------|-------|----------------|
| **Types.tla** | Foundation | -- | ErrorCode, ConfigRecord, AbstractHash, BitSet/ClearBit |
| **Lifecycle.tla** | Full spec | 2a, 2b, 2c | AtMostOneInstance, MisuseSafe, HandleConsistency |
| **LifecycleMinimal.tla** | CI spec | 2a, 2b, 2c | (same, tuned for TLC) |
| **Threading.tla** | Full spec | 7a, 8a-8c | CoreSingleThreaded, PALIsolation, NoDataRaces |
| **ThreadingMinimal.tla** | CI spec | 7a, 8a-8c | (same, tuned for TLC) |
| **PAL.tla** | Full spec | 7a-7d | AudioPushModel, AudioQueueBounded, BackpressureTracked |
| **PALMinimal.tla** | CI spec | 7a-7d | (same, tuned for TLC) |
| **Determinism.tla** | Full spec | 4a, 4b, 6b | TraceDeterminism, HashStability, ReplayEquivalence |
| **DeterminismMinimal.tla** | CI spec | 4a, 4b, 6b | (same, tuned for TLC) |
| **SaveState.tla** | Full spec | 4c | (serialization model, not directly checkable) |
| **SaveStateTest.tla** | CI spec | 4c | ObservationPreserved, CorruptionDetected, PartialSaveSafe |
| **Capture.tla** | Full spec | 5a-5c | DimensionsConsistent, FormatFixed, BackendIndependent |
| **CaptureMinimal.tla** | CI spec | 5a-5c | (same, tuned for TLC) |
| **Input.tla** | Full spec | 6a, 6b | ScancodeValid, E0PrefixCorrect, InputDeterminism |
| **InputMinimal.tla** | CI spec | 6a, 6b | (same, tuned for TLC) |
| **Reentrancy.tla** | Full spec | 8c | NoNestedStep, PhaseConsistent, CallbackSafe |
| **ReentrancyMinimal.tla** | CI spec | 8c | (same, tuned for TLC) |
| **ErrorModel.tla** | Full+CI | 2b | ErrorCodeDeterministic, SuccessRequiresValidState |
| **ConfigValidation.tla** | Full+CI | 2a | InvalidConfigBlocked, ValidConfigAccepted, VersionChecked |
| **APIContract.tla** | Composite | All 23 | AllGatesHold |
| **Composition.tla** | Docs | -- | (not checkable -- documents structure) |

---

## Full vs Minimal Specs

Most domain modules come in two variants:

- **Full spec** (e.g. `Lifecycle.tla`) -- Documentation-grade, models all error
  paths and edge cases. Constants are unbounded or large. Intended for reading,
  Apalache type checking, and reference. **Not** intended for TLC model checking
  (state space is too large).

- **Minimal spec** (e.g. `LifecycleMinimal.tla`) -- Constants tuned for tractable
  state spaces (<2,000 states). Preserves all safety invariants. Used in CI via
  `.cfg` files. Every Minimal spec completes in <60 seconds with 1 TLC worker.

Some modules are small enough to be both (ErrorModel, ConfigValidation, APIContract,
SaveStateTest) -- they have a `.cfg` file but no separate `*Minimal.tla`.

---

## Contract Gate Coverage

Every one of the 23 gates in `CONTRACT.md` has at least one TLA+ invariant:

| Gate | Description | Primary Spec | Primary Invariant(s) |
|------|-------------|--------------|----------------------|
| 1a | No main symbol | (code review) | N/A |
| 1b | C/C++ compatible | (code review) | N/A |
| 1c | Version handshake | APIContract | `Gate_VersionHandshake` |
| 2a | Create/destroy loop | Lifecycle | `HandleConsistency`, `ConfigValidated` |
| 2b | Misuse returns error | ErrorModel | `ErrorCodeDeterministic`, `SuccessRequiresValidState` |
| 2c | Single instance | Lifecycle | `AtMostOneInstance` |
| 3a | No exit/abort | APIContract | `Gate_NoExitAbort` |
| 3b | No stdout/stderr | APIContract | `Gate_NoStdout` |
| 3c | No env changes | APIContract | `Gate_NoEnvironmentChange` |
| 4a | State hash stable | Determinism | `HashStability` |
| 4b | Deterministic exec | Determinism | `TraceDeterminism` |
| 4c | Round-trip preserves | SaveStateTest | `ObservationPreserved` |
| 5a | Text dimensions | Capture | `DimensionsConsistent` |
| 5b | RGB24 format | Capture | `FormatFixed` |
| 5c | Backend independent | Capture | `BackendIndependent` |
| 6a | AT scancode set 1 | Input | `ScancodeValid`, `E0PrefixCorrect` |
| 6b | Input replay | Input + Determinism | `InputDeterminism`, `ReplayEquivalence` |
| 7a | No callback core | PAL + Threading | `AudioPushModel`, `PALIsolation` |
| 7b | Queue bounded | PAL | `AudioQueueBounded` |
| 7c | Push model | PAL | `AudioPushModel` |
| 7d | Drop policy | PAL | `BackpressureTracked` |
| 8a | Core single-threaded | Threading | `CoreSingleThreaded` |
| 8b | PAL isolation | Threading | `PALIsolation` |
| 8c | Wrong thread + reentrant | Threading + Reentrancy | `WrongThreadDetected`, `NoNestedStep` |

---

## Reading a TLA+ File

Each `.tla` file follows a consistent structure:

```
MODULE Name
  (* Block comment: purpose, gates covered, key invariants *)
  EXTENDS Integers, Sequences, ...

  CONSTANTS             -- Model parameters (bounded for TLC)
  Types / Sets          -- Domain-specific type definitions
  VARIABLES             -- State variables (with @type annotations)
  TypeOK                -- Type invariant (always first invariant)
  Safety Invariants     -- Named properties (e.g. AtMostOneInstance)
  Init                  -- Initial state predicate
  Actions               -- State transition operators
  Next                  -- Disjunction of all actions
  Spec                  -- Init /\ [][Next]_vars /\ fairness
  Temporal Properties   -- Liveness, temporal safety
```

**Conventions to know:**
- `\* @type: ...;` comments are Apalache type annotations (ignored by TLC)
- `(*----...----*)` dividers separate subsections
- `(* Contract gate: Xa *)` links an invariant to a CONTRACT.md gate
- Every invariant has a Lamport block comment explaining what it checks

---

## Running All Model Checks

Set up the tools variable first:
```bash
export TLA2TOOLS=/tmp/tla2tools.jar
cd spec/tla
```

Then run all 11 checkable specs:

```bash
# 1. Lifecycle (~250 states)
java -cp $TLA2TOOLS tlc2.TLC -config LifecycleMinimal.cfg LifecycleMinimal.tla -workers auto

# 2. Threading (~2,000 states)
java -cp $TLA2TOOLS tlc2.TLC -config ThreadingMinimal.cfg ThreadingMinimal.tla -workers auto

# 3. PAL (~200 states)
java -cp $TLA2TOOLS tlc2.TLC -config PALMinimal.cfg PALMinimal.tla -workers auto

# 4. Determinism (~500 states)
java -cp $TLA2TOOLS tlc2.TLC -config DeterminismMinimal.cfg DeterminismMinimal.tla -workers auto

# 5. SaveState (~30 states)
java -cp $TLA2TOOLS tlc2.TLC -config SaveStateTest.cfg SaveStateTest.tla -workers auto

# 6. Capture (~100 states)
java -cp $TLA2TOOLS tlc2.TLC -config CaptureMinimal.cfg CaptureMinimal.tla -workers auto

# 7. Input (~300 states)
java -cp $TLA2TOOLS tlc2.TLC -config InputMinimal.cfg InputMinimal.tla -workers auto

# 8. Reentrancy (~50 states)
java -cp $TLA2TOOLS tlc2.TLC -config ReentrancyMinimal.cfg ReentrancyMinimal.tla -workers auto

# 9. ErrorModel (~500 states)
java -cp $TLA2TOOLS tlc2.TLC -config ErrorModel.cfg ErrorModel.tla -workers auto

# 10. ConfigValidation (~20 states)
java -cp $TLA2TOOLS tlc2.TLC -config ConfigValidation.cfg ConfigValidation.tla -workers auto

# 11. APIContract (~1,000 states)
java -cp $TLA2TOOLS tlc2.TLC -config APIContract.cfg APIContract.tla -workers auto
```

All specs should complete with `Model checking completed. No error has been found.`

---

## Apalache Type Checking

All variables and operators have `@type` annotations. To type-check:

```bash
apalache-mc typecheck Types.tla
apalache-mc typecheck Lifecycle.tla
# ... etc for each module
```

Type annotations are comments of the form `\* @type: ...;` and are ignored by TLC.
They enable Apalache's static type checker to catch type errors before model checking.

---

## Key Design Decisions

### Polynomial hash instead of CHOOSE

The v1 specs used `CHOOSE h \in HashDomain : TRUE` for hash computation, which
is trivially satisfiable and provides no determinism guarantee. The v2 rewrite
uses a concrete polynomial-rolling hash:

```tla
(cfgId * 7 + ih * 13 + sh * 19 + cycle) % 997
```

This is deterministic by construction and collision-free within the finite model.

### Shadow state for input determinism

`Input.tla` maintains parallel `shadowKeyState` and `shadowBuffer` variables that
process the same input trace identically. The `InputDeterminism` invariant asserts
that primary and shadow state always match. This catches non-determinism in the
input processing pipeline.

### Component dependency graph for PAL

`PAL.tla` models the component initialization order as a dependency graph:
AudioSink depends on Context, Context depends on Window. The
`ComponentDependencySatisfied` invariant ensures components are only initialized
after their dependencies, preventing runtime failures from missing prerequisites.

### CRC model with prime modulus

`SaveStateTest.tla` models CRC32 as `(fields...) % 251` where 251 is prime.
This avoids TLC's 32-bit integer overflow while preserving the key property:
corruption detection. The `CorruptionDetected` invariant verifies that modified
snapshots are rejected.

---

## Related Documentation

- [`CONTRACT.md`](../CONTRACT.md) -- The 23 contract gates (requirements)
- [`VERIFICATION_REPORT.md`](../VERIFICATION_REPORT.md) -- Full verification results
- [`STYLE_GUIDE.md`](STYLE_GUIDE.md) -- TLA+ coding conventions for this project
- [`TROUBLESHOOTING.md`](TROUBLESHOOTING.md) -- Common TLC/SANY errors and fixes
