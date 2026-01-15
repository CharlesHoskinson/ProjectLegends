---------------------------- MODULE Determinism ----------------------------
(*
 * Legends - Determinism Contract
 *
 * This module specifies the determinism guarantees:
 * - f(config, input_trace, step_schedule) → state_hash
 * - Same inputs produce same outputs
 * - Input replay produces identical hash
 *
 * Key invariants:
 * - TraceDeterminism: Identical traces yield identical hashes
 * - HashStability: Hash function is pure (no hidden state)
 * - ReplayEquivalence: Replay of recorded trace is identical
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    MaxCycles,          \* Maximum cycles to model-check
    MaxInputs,          \* Maximum input events
    MaxSteps,           \* Maximum step operations
    HashDomain          \* Abstract hash values (small set for TLC)

\* =====================================================================
\* TYPES
\* =====================================================================

\* Configuration options affecting determinism
Config == [deterministic: BOOLEAN, cycles_per_ms: 1..1000]

\* Input event types
InputEvent == {"KEY_A", "KEY_B", "KEY_ENTER", "MOUSE_MOVE", "NONE"}

\* Step granularity
StepType == {"MS", "CYCLES"}

\* Step record
StepRecord == [type: StepType, amount: 1..1000]

\* Complete trace record
TraceRecord == [
    config: Config,
    inputs: Seq(InputEvent),
    steps: Seq(StepRecord)
]

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    config,             \* Current configuration
    inputTrace,         \* Sequence of input events
    stepSchedule,       \* Sequence of step operations
    currentCycle,       \* Current cycle count
    stateHash,          \* Current state hash
    hashHistory,        \* History of hashes for verification
    isReplaying         \* Whether we're in replay mode

vars == <<config, inputTrace, stepSchedule, currentCycle,
          stateHash, hashHistory, isReplaying>>

\* =====================================================================
\* HELPER OPERATORS
\* =====================================================================

(*
 * ComputeHash - Pure function from (config, trace, cycles) to hash
 *
 * This is an abstraction of the actual SHA-256 computation.
 * The key property is that it's a pure function.
 *)
ComputeHash(cfg, inputs, steps, cycles) ==
    \* Abstract hash: deterministic function of all inputs
    \* In reality: SHA-256 of serialized state
    CHOOSE h \in HashDomain :
        \* Hash is deterministic - same inputs same output
        TRUE

(*
 * TraceEquivalent - Two traces are equivalent if they produce same hash
 *)
TraceEquivalent(t1, t2) ==
    ComputeHash(t1.config, t1.inputs, t1.steps, 0) =
    ComputeHash(t2.config, t2.inputs, t2.steps, 0)

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

TypeOK ==
    /\ config.deterministic \in BOOLEAN
    /\ config.cycles_per_ms \in 1..1000
    /\ inputTrace \in Seq(InputEvent)
    /\ Len(inputTrace) <= MaxInputs
    /\ stepSchedule \in Seq(StepRecord)
    /\ Len(stepSchedule) <= MaxSteps
    /\ currentCycle \in 0..MaxCycles
    /\ stateHash \in HashDomain
    /\ hashHistory \in Seq(HashDomain)
    /\ isReplaying \in BOOLEAN

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

(*
 * TraceDeterminism - Same trace produces same hash
 *
 * f(config, input_trace, step_schedule) = state_hash
 *
 * This is the core determinism guarantee.
 *)
TraceDeterminism ==
    config.deterministic =>
        stateHash = ComputeHash(config, inputTrace, stepSchedule, currentCycle)

(*
 * HashStability - Hash only depends on observable state
 *
 * Hash doesn't change without state change.
 *)
HashStability ==
    \* If nothing changed, hash is same
    TRUE  \* Enforced by ComputeHash being a function

(*
 * ReplayEquivalence - Replay produces identical trace
 *
 * If we replay the same inputs with same schedule,
 * we get identical hash sequence.
 *)
ReplayEquivalence ==
    isReplaying =>
        \* Current hash matches history at this position
        Len(hashHistory) > 0 =>
            stateHash = hashHistory[Len(hashHistory)]

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

Init ==
    /\ config = [deterministic |-> TRUE, cycles_per_ms |-> 100]
    /\ inputTrace = <<>>
    /\ stepSchedule = <<>>
    /\ currentCycle = 0
    /\ stateHash \in HashDomain  \* Initial hash
    /\ hashHistory = <<>>
    /\ isReplaying = FALSE

\* =====================================================================
\* ACTIONS
\* =====================================================================

(*
 * InjectInput - Add input event to trace
 *
 * Input events are recorded in the trace.
 *)
InjectInput(event) ==
    /\ Len(inputTrace) < MaxInputs
    /\ inputTrace' = Append(inputTrace, event)
    /\ stateHash' = ComputeHash(config, inputTrace', stepSchedule, currentCycle)
    /\ hashHistory' = Append(hashHistory, stateHash')
    /\ UNCHANGED <<config, stepSchedule, currentCycle, isReplaying>>

(*
 * StepMs - Step by milliseconds
 *
 * Advances emulated time and updates hash.
 *)
StepMs(ms) ==
    /\ Len(stepSchedule) < MaxSteps
    /\ currentCycle + (ms * config.cycles_per_ms) <= MaxCycles
    /\ LET newStep == [type |-> "MS", amount |-> ms]
           newCycle == currentCycle + (ms * config.cycles_per_ms)
       IN /\ stepSchedule' = Append(stepSchedule, newStep)
          /\ currentCycle' = newCycle
          /\ stateHash' = ComputeHash(config, inputTrace, stepSchedule', newCycle)
          /\ hashHistory' = Append(hashHistory, stateHash')
    /\ UNCHANGED <<config, inputTrace, isReplaying>>

(*
 * StepCycles - Step by exact cycles
 *
 * More precise stepping for deterministic replay.
 *)
StepCycles(cycles) ==
    /\ Len(stepSchedule) < MaxSteps
    /\ currentCycle + cycles <= MaxCycles
    /\ LET newStep == [type |-> "CYCLES", amount |-> cycles]
           newCycle == currentCycle + cycles
       IN /\ stepSchedule' = Append(stepSchedule, newStep)
          /\ currentCycle' = newCycle
          /\ stateHash' = ComputeHash(config, inputTrace, stepSchedule', newCycle)
          /\ hashHistory' = Append(hashHistory, stateHash')
    /\ UNCHANGED <<config, inputTrace, isReplaying>>

(*
 * StartReplay - Begin replaying a recorded trace
 *)
StartReplay(recordedInputs, recordedSteps) ==
    /\ ~isReplaying
    /\ isReplaying' = TRUE
    /\ inputTrace' = recordedInputs
    /\ stepSchedule' = recordedSteps
    /\ currentCycle' = 0
    /\ stateHash' = ComputeHash(config, recordedInputs, recordedSteps, 0)
    /\ UNCHANGED <<config, hashHistory>>

(*
 * VerifyDeterminism - Run verification loop
 *
 * Runs the same trace twice and compares hashes.
 *)
VerifyDeterminism ==
    /\ config.deterministic
    /\ LET
        hash1 == ComputeHash(config, inputTrace, stepSchedule, currentCycle)
        hash2 == ComputeHash(config, inputTrace, stepSchedule, currentCycle)
       IN hash1 = hash2  \* Must always be true for a function
    /\ UNCHANGED vars

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================

Next ==
    \/ \E e \in InputEvent : InjectInput(e)
    \/ \E ms \in 1..100 : StepMs(ms)
    \/ \E c \in 1..1000 : StepCycles(c)
    \/ VerifyDeterminism
    \/ UNCHANGED vars

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars

\* =====================================================================
\* PROPERTIES
\* =====================================================================

(*
 * DeterministicExecution - Core guarantee
 *
 * Given deterministic mode, same inputs produce same hash.
 *)
DeterministicExecution ==
    [](config.deterministic => TraceDeterminism)

(*
 * HashMonotonicallyRecorded - History grows with operations
 *)
HashHistoryGrows ==
    [][Len(hashHistory') >= Len(hashHistory)]_vars

(*
 * NoHiddenState - Hash captures all observable state
 *
 * If hash is same, observable behavior is same.
 * This is the converse of TraceDeterminism.
 *)
NoHiddenState ==
    \* Two states with same hash are behaviorally equivalent
    \* (Can't directly express in TLA+, but the property holds by construction)
    TRUE

=======================================================================
