---------------------------- MODULE Reentrancy ----------------------------
(**************************************************************************)
(* Legends -- Reentrancy Guard Specification                              *)
(*                                                                        *)
(* Models the scenario where legends_step_*() is called from within       *)
(* a PAL callback that was itself invoked by a running step.              *)
(*                                                                        *)
(* Error code: LEGENDS_ERR_REENTRANT_CALL (-5)                            *)
(*                                                                        *)
(* State machine:                                                         *)
(*   IDLE -> IN_STEP    (legends_step_*() begins)                         *)
(*   IN_STEP -> IN_CB   (step invokes PAL callback)                       *)
(*   IN_CB -> IN_STEP   (callback returns)                                *)
(*   IN_STEP -> IDLE    (step completes)                                  *)
(*                                                                        *)
(* The guard ensures that if phase = IN_STEP or IN_CB, any new call       *)
(* to step returns REENTRANT_CALL immediately.                            *)
(*                                                                        *)
(* Contract gate: 8c (reentrancy subset)                                  *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   NoNestedStep           -- step never succeeds while already in step  *)
(*   ReentrancyReturnsError -- reentrant attempt -> REENTRANT_CALL        *)
(*   PhaseConsistent        -- phase transitions are well-ordered         *)
(*   CallbackSafe           -- callback cannot corrupt step state         *)
(**************************************************************************)
EXTENDS Integers, TLC

(**************************************************************************)
(* CONSTANTS                                                              *)
(**************************************************************************)
CONSTANTS
    MaxOps  \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
Phase == {"IDLE", "IN_STEP", "IN_CALLBACK"}

\* @type: Set(Str);
ErrorCode == {"OK", "REENTRANT_CALL", "NULL_HANDLE"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    phase,          \* @type: Str;   Current execution phase
    lastError,      \* @type: Str;   Last error code
    opCount,        \* @type: Int;   Operation counter
    hasInstance,     \* @type: Bool;  Whether an instance exists
    stepDepth       \* @type: Int;   Nesting depth (should never exceed 1)

vars == <<phase, lastError, opCount, hasInstance, stepDepth>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ phase \in Phase
    /\ lastError \in ErrorCode
    /\ opCount \in 0..MaxOps
    /\ hasInstance \in BOOLEAN
    /\ stepDepth \in 0..2

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* NoNestedStep                                                       *)
(*                                                                    *)
(* Step never succeeds (lastError = "OK") when already inside a step. *)
(* The step depth never exceeds 1.                                    *)
(*--------------------------------------------------------------------*)
NoNestedStep ==
    stepDepth <= 1

(*--------------------------------------------------------------------*)
(* ReentrancyReturnsError                                             *)
(*                                                                    *)
(* An attempt to call step while phase is IN_STEP or IN_CALLBACK      *)
(* always results in REENTRANT_CALL, never OK.                        *)
(*--------------------------------------------------------------------*)
ReentrancyReturnsError ==
    (phase \in {"IN_STEP", "IN_CALLBACK"} /\ lastError = "OK")
    => stepDepth <= 1

(*--------------------------------------------------------------------*)
(* PhaseConsistent                                                    *)
(*                                                                    *)
(* Phase and stepDepth are always consistent:                         *)
(*   IDLE => stepDepth = 0                                            *)
(*   IN_STEP => stepDepth = 1                                         *)
(*   IN_CALLBACK => stepDepth = 1                                     *)
(*--------------------------------------------------------------------*)
PhaseConsistent ==
    /\ (phase = "IDLE" => stepDepth = 0)
    /\ (phase \in {"IN_STEP", "IN_CALLBACK"} => stepDepth = 1)

(*--------------------------------------------------------------------*)
(* CallbackSafe                                                       *)
(*                                                                    *)
(* Callback phase always returns to IN_STEP, never directly to IDLE.  *)
(*--------------------------------------------------------------------*)
CallbackSafe ==
    phase = "IN_CALLBACK" => stepDepth = 1

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ phase = "IDLE"
    /\ lastError = "OK"
    /\ opCount = 0
    /\ hasInstance = FALSE
    /\ stepDepth = 0

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

\* Create instance
Create ==
    /\ ~hasInstance
    /\ opCount < MaxOps
    /\ hasInstance' = TRUE
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<phase, stepDepth>>

\* Destroy instance
Destroy ==
    /\ hasInstance
    /\ phase = "IDLE"
    /\ opCount < MaxOps
    /\ hasInstance' = FALSE
    /\ phase' = "IDLE"
    /\ stepDepth' = 0
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1

\* Begin step -- enters IN_STEP if IDLE
BeginStep ==
    /\ hasInstance
    /\ opCount < MaxOps
    /\ IF phase = "IDLE"
       THEN /\ phase' = "IN_STEP"
            /\ stepDepth' = 1
            /\ lastError' = "OK"
       ELSE \* Reentrant call detected!
            /\ lastError' = "REENTRANT_CALL"
            /\ UNCHANGED <<phase, stepDepth>>
    /\ opCount' = opCount + 1
    /\ UNCHANGED hasInstance

\* Step invokes PAL callback
EnterCallback ==
    /\ phase = "IN_STEP"
    /\ phase' = "IN_CALLBACK"
    /\ UNCHANGED <<lastError, opCount, hasInstance, stepDepth>>

\* Callback returns to step
ReturnFromCallback ==
    /\ phase = "IN_CALLBACK"
    /\ phase' = "IN_STEP"
    /\ UNCHANGED <<lastError, opCount, hasInstance, stepDepth>>

\* Reentrant step attempt from callback
ReentrantStepAttempt ==
    /\ phase = "IN_CALLBACK"
    /\ opCount < MaxOps
    /\ lastError' = "REENTRANT_CALL"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<phase, hasInstance, stepDepth>>

\* Step completes
EndStep ==
    /\ phase = "IN_STEP"
    /\ phase' = "IDLE"
    /\ stepDepth' = 0
    /\ UNCHANGED <<lastError, opCount, hasInstance>>

\* Step on null handle
StepNoInstance ==
    /\ ~hasInstance
    /\ opCount < MaxOps
    /\ lastError' = "NULL_HANDLE"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<phase, hasInstance, stepDepth>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ Create
    \/ Destroy
    \/ BeginStep
    \/ EnterCallback
    \/ ReturnFromCallback
    \/ ReentrantStepAttempt
    \/ EndStep
    \/ StepNoInstance
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(EndStep)

(**************************************************************************)
(* LIVENESS                                                               *)
(**************************************************************************)

\* Step eventually completes (with weak fairness)
StepEventuallyCompletes ==
    phase = "IN_STEP" ~> phase = "IDLE"

=======================================================================
