# TLA+ Style Guide

Coding conventions for the Project Legends TLA+ specification suite.

---

## File Structure

Every `.tla` module follows this order:

```
1. MODULE declaration
2. Block comment: purpose, contract gates, key invariants, liveness
3. EXTENDS
4. CONSTANTS (with @type annotations)
5. Type definitions (sets, records)
6. Helper operators
7. VARIABLES (with @type annotations)
8. TypeOK (type invariant -- always first invariant)
9. Safety invariants (each with block comment + gate reference)
10. Init (initial state)
11. Actions (each with descriptive name + block comment)
12. Next (disjunction of all actions)
13. Spec (Init /\ [][Next]_vars /\ fairness)
14. Temporal properties (liveness, temporal safety)
```

---

## Naming Conventions

| Element | Style | Examples |
|---------|-------|---------|
| Module names | PascalCase | `Lifecycle`, `SaveStateTest`, `PALMinimal` |
| Operators / Invariants | PascalCase | `AtMostOneInstance`, `HashStability` |
| Variables | camelCase | `stateHash`, `audioQueue`, `ownerThread` |
| Constants | PascalCase | `MaxCycle`, `MaxEvents`, `MaxOperations` |
| Type sets | PascalCase | `ErrorCode`, `InstanceState`, `Backend` |
| Actions | PascalCase (verb phrase) | `Create`, `PushAudioSamples`, `BeginStep` |

### Invariant Naming Pattern

Use `[Property][Qualifier]`:

- `HandleConsistency` -- handle state is consistent
- `AudioQueueBounded` -- audio queue respects bounds
- `E0PrefixCorrect` -- E0 prefix encoding is correct
- `CoreSingleThreaded` -- core access is single-threaded
- `ErrorCodeDeterministic` -- error codes are deterministic

Gate-specific invariants in APIContract use `Gate_` prefix:
`Gate_VersionHandshake`, `Gate_NoExitAbort`, `Gate_NoStdout`

---

## Comment Style

### Module header

Every module starts with a Lamport block comment:

```tla
(**************************************************************************)
(* Module Name -- Brief Description                                      *)
(*                                                                        *)
(* Detailed explanation of what this module models.                       *)
(*                                                                        *)
(* Contract gates covered:                                                *)
(*   Xa  description                                                      *)
(*   Xb  description                                                      *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   InvariantName  -- one-line explanation                               *)
(**************************************************************************)
```

### Section dividers

Major sections use full-width comment blocks:

```tla
(**************************************************************************)
(* SECTION NAME                                                           *)
(**************************************************************************)
```

### Subsection dividers

Invariants and important operators use `(*----...----*)`:

```tla
(*--------------------------------------------------------------------*)
(* InvariantName -- Gate Xa                                            *)
(*                                                                    *)
(* Explanation of what this invariant checks.                          *)
(*--------------------------------------------------------------------*)
```

### Inline comments

Use `\*` for single-line comments:

```tla
\* @type: Int;
MaxCycle  \* Maximum virtual time (cycles)
```

---

## Type Annotations

Every variable and every operator with a non-obvious return type gets an
Apalache `@type` annotation:

```tla
VARIABLES
    stateHash,      \* @type: Int;
    inputTrace,     \* @type: Seq(Str);
    instance        \* @type: Str;

\* @type: (Int, Seq(Str), Seq(Int), Int) -> Int;
ComputeHash(cfgId, inputs, steps, cycles) == ...

\* @type: Set(Str);
ErrorCode == {"OK", "NULL_HANDLE", ...}
```

Common Apalache types used in this project:
- `Int`, `Str`, `Bool`
- `Set(T)`, `Seq(T)`
- `T -> U` (function types)
- `{field1: T1, field2: T2}` (record types)

---

## Full vs Minimal Pattern

### When to create a Minimal variant

Create a `*Minimal.tla` + `.cfg` pair when the full spec's state space exceeds
~2,000 distinct states. Modules small enough to check directly (ErrorModel,
ConfigValidation, SaveStateTest) do not need a Minimal variant.

### How to create a Minimal spec

1. Copy the full spec's core logic (Init, actions, invariants)
2. Reduce constant values to keep states < 2,000
3. Remove features that explode state space (e.g., replay mode, history sequences)
4. Keep all safety invariants -- never weaken correctness
5. Create a matching `.cfg` file with concrete CONSTANT values and INVARIANT list

### Constants for tractable state space

Target < 2,000 distinct states. Typical settings:

```
MaxOperations = 5
MaxInputs = 2
MaxSteps = 2
MaxCycles = 10
MaxAudioFrames = 3
MaxEvents = 2
```

---

## Gate References

Every invariant that covers a contract gate includes the gate number in its
block comment:

```tla
(*--------------------------------------------------------------------*)
(* AudioPushModel -- Gate 7c                                          *)
(*                                                                    *)
(* Audio flows core -> PAL only. The audio callback thread            *)
(* never invokes core functions.                                      *)
(*--------------------------------------------------------------------*)
AudioPushModel ==
    currentThread = "AudioCallback" => lastCaller \in {"PAL", "None"}
```

The gate-to-invariant mapping is maintained in `Composition.tla` and
`VERIFICATION_REPORT.md`.

---

## Forbidden Patterns

1. **No `== TRUE` stubs.** Every invariant must check a real property:
   ```tla
   \* BAD:
   InputDeterminism == TRUE

   \* GOOD:
   InputDeterminism ==
       /\ keyState = shadowKeyState
       /\ keyboardBuffer = shadowBuffer
   ```

2. **No meaningless `CHOOSE`.** `CHOOSE x \in S : TRUE` provides no guarantee:
   ```tla
   \* BAD:
   ComputeHash(x) == CHOOSE h \in 0..999 : TRUE

   \* GOOD:
   ComputeHash(cfgId, inputs, steps, cycle) ==
       (cfgId * 7 + ih * 13 + sh * 19 + cycle) % 997
   ```

3. **No untyped variables.** Every variable needs `\* @type:` annotation.

4. **No invariants without comments.** Every safety invariant gets a block
   comment explaining what it checks and which gate it covers (if any).
