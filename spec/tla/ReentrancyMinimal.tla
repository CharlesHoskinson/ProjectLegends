---------------------- MODULE ReentrancyMinimal ----------------------
(**************************************************************************)
(* Legends -- Minimal Reentrancy Guard for CI Model Checking              *)
(*                                                                        *)
(* Focused test of the reentrancy guard state machine.                    *)
(* Verifies no nested step succeeds and reentrant calls return error.     *)
(*                                                                        *)
(* Expected: ~50 distinct states at MaxOps=6                              *)
(**************************************************************************)
EXTENDS Integers, TLC

CONSTANTS
    MaxOps  \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
Phase == {"IDLE", "IN_STEP", "IN_CALLBACK"}

\* @type: Set(Str);
ErrCode == {"OK", "REENTRANT_CALL", "NULL_HANDLE"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    phase,      \* @type: Str;
    lastError,  \* @type: Str;
    opCount,    \* @type: Int;
    hasInst,    \* @type: Bool;
    stepDepth   \* @type: Int;

vars == <<phase, lastError, opCount, hasInst, stepDepth>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ phase \in Phase
    /\ lastError \in ErrCode
    /\ opCount \in 0..MaxOps
    /\ hasInst \in BOOLEAN
    /\ stepDepth \in 0..2

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

\* Step depth never exceeds 1
NoNestedStep ==
    stepDepth <= 1

\* Phase and depth consistent
PhaseConsistent ==
    /\ (phase = "IDLE" => stepDepth = 0)
    /\ (phase \in {"IN_STEP", "IN_CALLBACK"} => stepDepth = 1)

\* Callback always has step on stack
CallbackSafe ==
    phase = "IN_CALLBACK" => stepDepth = 1

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ phase = "IDLE"
    /\ lastError = "OK"
    /\ opCount = 0
    /\ hasInst = FALSE
    /\ stepDepth = 0

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

Create ==
    /\ ~hasInst
    /\ opCount < MaxOps
    /\ hasInst' = TRUE
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<phase, stepDepth>>

Destroy ==
    /\ hasInst
    /\ phase = "IDLE"
    /\ opCount < MaxOps
    /\ hasInst' = FALSE
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<phase, stepDepth>>

BeginStep ==
    /\ hasInst
    /\ opCount < MaxOps
    /\ IF phase = "IDLE"
       THEN /\ phase' = "IN_STEP"
            /\ stepDepth' = 1
            /\ lastError' = "OK"
       ELSE /\ lastError' = "REENTRANT_CALL"
            /\ UNCHANGED <<phase, stepDepth>>
    /\ opCount' = opCount + 1
    /\ UNCHANGED hasInst

EnterCallback ==
    /\ phase = "IN_STEP"
    /\ phase' = "IN_CALLBACK"
    /\ UNCHANGED <<lastError, opCount, hasInst, stepDepth>>

ReturnCallback ==
    /\ phase = "IN_CALLBACK"
    /\ phase' = "IN_STEP"
    /\ UNCHANGED <<lastError, opCount, hasInst, stepDepth>>

ReentrantAttempt ==
    /\ phase = "IN_CALLBACK"
    /\ opCount < MaxOps
    /\ lastError' = "REENTRANT_CALL"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<phase, hasInst, stepDepth>>

EndStep ==
    /\ phase = "IN_STEP"
    /\ phase' = "IDLE"
    /\ stepDepth' = 0
    /\ UNCHANGED <<lastError, opCount, hasInst>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ Create
    \/ Destroy
    \/ BeginStep
    \/ EnterCallback
    \/ ReturnCallback
    \/ ReentrantAttempt
    \/ EndStep
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================
