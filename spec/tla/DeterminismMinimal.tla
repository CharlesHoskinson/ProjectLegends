---------------------- MODULE DeterminismMinimal ----------------------
(**************************************************************************)
(* Legends -- Minimal Determinism for CI Model Checking                   *)
(*                                                                        *)
(* Strips history and replay to keep state space tractable.               *)
(* Focuses on the core property: hash = f(cfg, inputs, steps, cycle).     *)
(*                                                                        *)
(* Expected: ~500 distinct states at MaxInputs=2, MaxSteps=2              *)
(**************************************************************************)
EXTENDS Integers, Sequences, TLC

CONSTANTS
    MaxCycles,      \* @type: Int;
    MaxInputs,      \* @type: Int;
    MaxSteps        \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
InputEvent == {"KEY_A", "KEY_B", "MOUSE_MOVE"}

(**************************************************************************)
(* CONCRETE HASH (same algorithm as full spec)                            *)
(**************************************************************************)

\* @type: Str -> Int;
InputCode(evt) ==
    CASE evt = "KEY_A"      -> 1
      [] evt = "KEY_B"      -> 2
      [] evt = "MOUSE_MOVE" -> 4

\* @type: (Seq(Str), Int) -> Int;
RECURSIVE HashInputs(_, _)
HashInputs(seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE HashInputs(Tail(seq), (acc * 31 + InputCode(Head(seq))) % 997)

\* @type: (Seq(Int), Int) -> Int;
RECURSIVE HashSteps(_, _)
HashSteps(seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE HashSteps(Tail(seq), (acc * 37 + Head(seq)) % 997)

\* @type: (Int, Seq(Str), Seq(Int), Int) -> Int;
ComputeHash(cfgId, inputs, steps, cycles) ==
    LET ih == HashInputs(inputs, 0)
        sh == HashSteps(steps, 0)
    IN (cfgId * 7 + ih * 13 + sh * 19 + cycles) % 997

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    cfgId,          \* @type: Int;
    inputTrace,     \* @type: Seq(Str);
    stepAmounts,    \* @type: Seq(Int);
    currentCycle,   \* @type: Int;
    stateHash       \* @type: Int;

vars == <<cfgId, inputTrace, stepAmounts, currentCycle, stateHash>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ cfgId \in {0, 1}
    /\ inputTrace \in Seq(InputEvent)
    /\ Len(inputTrace) <= MaxInputs
    /\ stepAmounts \in Seq(1..MaxCycles)
    /\ Len(stepAmounts) <= MaxSteps
    /\ currentCycle \in 0..MaxCycles
    /\ stateHash \in 0..996

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

\* Core determinism: hash always equals f(cfg, inputs, steps, cycle)
TraceDeterminism ==
    stateHash = ComputeHash(cfgId, inputTrace, stepAmounts, currentCycle)

\* Hash stability: pure function, no hidden state
HashStability ==
    stateHash = ComputeHash(cfgId, inputTrace, stepAmounts, currentCycle)

\* Config sensitivity: different cfgId at same state => different hash
\* (checked by TLC exploring both cfgId=0 and cfgId=1)
ConfigSensitivity ==
    (inputTrace # <<>> \/ stepAmounts # <<>> \/ currentCycle > 0) =>
        ComputeHash(0, inputTrace, stepAmounts, currentCycle) #
        ComputeHash(1, inputTrace, stepAmounts, currentCycle)
        \/ (inputTrace = <<>> /\ stepAmounts = <<>> /\ currentCycle = 0)

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ cfgId \in {0, 1}
    /\ inputTrace = <<>>
    /\ stepAmounts = <<>>
    /\ currentCycle = 0
    /\ stateHash = ComputeHash(cfgId, <<>>, <<>>, 0)

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

InjectInput(event) ==
    /\ Len(inputTrace) < MaxInputs
    /\ LET newTrace == Append(inputTrace, event)
       IN /\ inputTrace' = newTrace
          /\ stateHash' = ComputeHash(cfgId, newTrace, stepAmounts, currentCycle)
    /\ UNCHANGED <<cfgId, stepAmounts, currentCycle>>

StepCycles(cycles) ==
    /\ Len(stepAmounts) < MaxSteps
    /\ currentCycle + cycles <= MaxCycles
    /\ LET newSteps == Append(stepAmounts, cycles)
           newCycle == currentCycle + cycles
       IN /\ stepAmounts' = newSteps
          /\ currentCycle' = newCycle
          /\ stateHash' = ComputeHash(cfgId, inputTrace, newSteps, newCycle)
    /\ UNCHANGED <<cfgId, inputTrace>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E e \in InputEvent : InjectInput(e)
    \/ \E c \in {1, 5, 10} : StepCycles(c)
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================

