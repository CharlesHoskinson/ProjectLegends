# TLA+ Troubleshooting Guide

Common issues and solutions when working with the Project Legends TLA+ specs.

---

## SANY Parse Errors

### "Could not find module"

```
Error: Could not find module Integers
```

**Fix:** Ensure `tla2tools.jar` is on the classpath:
```bash
java -cp /tmp/tla2tools.jar tlc2.TLC -config Spec.cfg Spec.tla
```

### "MODULE name mismatch"

```
Error: Was expecting MODULE Foo but found MODULE Bar
```

**Fix:** The `MODULE` declaration at the top of the `.tla` file must match the
filename (without extension). Rename the file or fix the declaration.

### "Unknown operator"

```
Error: Unknown operator: FiniteSets!Cardinality
```

**Fix:** Add `FiniteSets` to the `EXTENDS` clause:
```tla
EXTENDS Integers, Sequences, FiniteSets
```

---

## TLC State Explosion

### Symptoms

TLC runs for minutes/hours, reporting millions of states, or runs out of memory.

### Causes and Fixes

1. **Using a Full spec instead of Minimal.** Full specs (Lifecycle.tla,
   Threading.tla, PAL.tla, etc.) have large/unbounded constants. Use the
   corresponding `*Minimal.tla` + `.cfg` pair instead.

2. **Constants too large.** Reduce `MaxOperations`, `MaxInputs`, `MaxCycles` etc.
   Target < 2,000 distinct states. Check `STYLE_GUIDE.md` for recommended values.

3. **Set comprehensions with large domains.** `{f(x) : x \in 0..65535}` creates
   65,536 elements. Bound domains for TLC.

### Reading TLC Progress Output

```
Progress(12) at 2024-01-15 10:30:22: 1,847 states generated, 423 distinct states found
```

- `states generated` = total transitions explored (including duplicates)
- `distinct states found` = unique states in state graph
- If distinct states grow past ~10,000, consider reducing constants

---

## Invariant Violations

### Reading a Counterexample Trace

When TLC finds a violation, it prints a trace:

```
Error: Invariant AtMostOneInstance is violated.
The following behavior constitutes a counterexample:

State 1: <Initial predicate>
/\ instance = "NONE"
/\ ownerThread = "None"

State 2: <Create line 45, col 5 to line 60, col 30>
/\ instance = "CREATED"
/\ ownerThread = "Main"

State 3: <Create line 45, col 5 to line 60, col 30>
/\ instance = "CREATED"  <-- VIOLATION: second Create succeeded
```

**How to debug:**
1. Read the trace bottom-up -- the last state shows the violation
2. Check which action caused the transition (shown in `<...>`)
3. Look for a missing guard in that action (e.g., missing `instance = "NONE"` check)

### Common Causes

- **Missing precondition in action:** An action allows a transition it shouldn't
- **Invariant too strict:** The invariant forbids a state that is actually reachable
- **Init state violates invariant:** Check that Init satisfies all invariants

---

## Apalache Type Errors

### "Type error in annotation"

```
Type error in annotation: expected Int, found Str
```

**Fix:** Check the `\* @type:` annotation matches the actual operator signature.
Common mistakes:

```tla
\* BAD: returns Int but annotated as Str
\* @type: Str;
ComputeHash(x) == x * 7 % 997

\* GOOD:
\* @type: Int;
ComputeHash(x) == x * 7 % 997
```

### Running type checking

```bash
apalache-mc typecheck Types.tla
apalache-mc typecheck Lifecycle.tla
```

---

## Java/TLC Setup

### JDK Requirements

TLC requires Java 11+. Java 17 is recommended (matches CI):

```bash
java -version   # Should show 17+
```

### Downloading tla2tools.jar

```bash
wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar \
  -O /tmp/tla2tools.jar
export TLA2TOOLS=/tmp/tla2tools.jar
```

### Memory Settings for Large Specs

If TLC runs out of memory:
```bash
java -Xmx4g -cp $TLA2TOOLS tlc2.TLC -config Spec.cfg Spec.tla -workers auto
```

The `-workers auto` flag uses all available CPU cores.

---

## "Spec Too Large" / Full Specs

The following full specs are **not** meant for direct TLC model checking:

| Module | Why | Use Instead |
|--------|-----|-------------|
| Lifecycle.tla | Large constant domains | LifecycleMinimal.tla |
| Threading.tla | Many thread interleavings | ThreadingMinimal.tla |
| PAL.tla | Audio queue + component graph | PALMinimal.tla |
| Determinism.tla | History sequences | DeterminismMinimal.tla |
| Capture.tla | Pixel dimensions | CaptureMinimal.tla |
| Input.tla | Scancode × state space | InputMinimal.tla |
| Reentrancy.tla | Small enough in practice | ReentrancyMinimal.tla |
| SaveState.tla | Serialization model | SaveStateTest.tla |
| Composition.tla | Documentation only | N/A |

---

## CI Failures

### Reproducing a CI TLA+ check failure locally

CI runs specs from `.github/workflows/ci.yml`. To reproduce:

```bash
# 1. Download the same TLC version as CI
wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar \
  -O /tmp/tla2tools.jar

# 2. Run the failing spec
cd spec/tla
java -cp /tmp/tla2tools.jar tlc2.TLC \
  -config LifecycleMinimal.cfg LifecycleMinimal.tla -workers auto
```

### Common CI failure causes

1. **Syntax error in `.tla` file** -- SANY will report the line number
2. **Invariant violation** -- TLC prints a counterexample trace (see above)
3. **Missing `.cfg` file** -- ensure both `.tla` and `.cfg` are committed
4. **Java version mismatch** -- CI uses Java 17 (temurin)
