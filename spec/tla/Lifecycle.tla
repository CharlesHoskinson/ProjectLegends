---------------------------- MODULE Lifecycle ----------------------------
(**************************************************************************)
(* Legends API -- Instance Lifecycle Contract                             *)
(*                                                                        *)
(* This is the FULL (documentation-grade) lifecycle specification.        *)
(* It models every API error path with all 14 error codes, reentrancy     *)
(* guard, wrong-thread detection, config validation, and reset.           *)
(*                                                                        *)
(* For CI model checking, use LifecycleMinimal.tla instead.               *)
(*                                                                        *)
(* Contract gates covered:                                                *)
(*   2a  create->step->destroy works in loop                              *)
(*   2b  Misuse returns error, never crash                                *)
(*   2c  Single-instance-per-process enforced                             *)
(*   8c  Wrong-thread detection                                           *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   AtMostOneInstance   -- at most one CREATED instance                  *)
(*   MisuseSafe          -- invalid ops return errors, never crash        *)
(*   HandleConsistency   -- handle = VALID iff instance active            *)
(*   ReentrancySafe      -- step from callback returns REENTRANT_CALL    *)
(*   WrongThreadSafe     -- call from wrong thread returns WRONG_THREAD  *)
(*   ConfigValidated     -- create with bad config returns INVALID_CONFIG *)
(*                                                                        *)
(* Liveness:                                                              *)
(*   EventualTermination -- CREATED ~> NONE (with fairness)               *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

(**************************************************************************)
(* CONSTANTS                                                              *)
(**************************************************************************)
CONSTANTS
    MaxOperations   \* @type: Int; Maximum API calls to model-check

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* All 14+1 error codes (matches legends_embed.h)
\* @type: Set(Str);
ErrorCode == {
    "OK", "NULL_HANDLE", "NULL_POINTER", "ALREADY_CREATED",
    "NOT_INITIALIZED", "REENTRANT_CALL", "BUFFER_TOO_SMALL",
    "INVALID_CONFIG", "INVALID_STATE", "VERSION_MISMATCH",
    "IO_FAILED", "OUT_OF_MEMORY", "NOT_SUPPORTED", "INTERNAL",
    "WRONG_THREAD"
}

\* @type: Set(Str);
InstanceState == {"NONE", "CREATED"}

\* @type: Set(Str);
Operation == {
    "CREATE", "DESTROY", "RESET", "STEP",
    "CAPTURE", "INPUT", "SAVE", "LOAD"
}

\* @type: Set(Str);
ThreadId == {"Main", "Other"}

\* Config validity (abstracted to boolean for this spec)
\* @type: Set(Str);
ConfigKind == {"VALID", "INVALID_CFG", "WRONG_VERSION"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    instance,       \* @type: Str;   Current instance state
    handle,         \* @type: Str;   "NULL" or "VALID"
    opCount,        \* @type: Int;   Operation counter (bounding)
    lastError,      \* @type: Str;   Last error code returned
    lastOp,         \* @type: Str;   Last operation attempted
    ownerThread,    \* @type: Str;   Thread that called create
    currentThread,  \* @type: Str;   Thread making current call
    inStep,         \* @type: Bool;  Reentrancy guard flag
    trace           \* @type: Seq(Str); Operation trace for debugging

vars == <<instance, handle, opCount, lastError, lastOp,
          ownerThread, currentThread, inStep, trace>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ instance \in InstanceState
    /\ handle \in {"NULL", "VALID"}
    /\ opCount \in 0..MaxOperations
    /\ lastError \in ErrorCode
    /\ lastOp \in Operation \cup {"NONE"}
    /\ ownerThread \in ThreadId \cup {"None"}
    /\ currentThread \in ThreadId
    /\ inStep \in BOOLEAN
    /\ trace \in Seq(Operation)

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* AtMostOneInstance -- Gate 2c                                        *)
(*                                                                    *)
(* There is at most one active instance at any time.  When an         *)
(* instance is CREATED, the handle must be VALID.                     *)
(*--------------------------------------------------------------------*)
AtMostOneInstance ==
    instance = "CREATED" => handle = "VALID"

(*--------------------------------------------------------------------*)
(* MisuseSafe -- Gate 2b                                              *)
(*                                                                    *)
(* Operations on a NULL handle return an error, never crash.          *)
(* The system never enters an undefined state.                        *)
(*--------------------------------------------------------------------*)
MisuseSafe ==
    /\ (instance = "NONE" /\ handle = "NULL") =>
        lastError \in {"OK", "NULL_HANDLE", "NULL_POINTER",
                       "ALREADY_CREATED", "INVALID_CONFIG",
                       "VERSION_MISMATCH", "WRONG_THREAD"}
    /\ instance = "CREATED" => handle = "VALID"

(*--------------------------------------------------------------------*)
(* HandleConsistency                                                  *)
(*                                                                    *)
(* Handle state is always consistent with instance state.             *)
(*--------------------------------------------------------------------*)
HandleConsistency ==
    (instance = "NONE") <=> (handle = "NULL")

(*--------------------------------------------------------------------*)
(* ReentrancySafe                                                     *)
(*                                                                    *)
(* If we are inside a step (inStep = TRUE), any attempt to call       *)
(* step again produces REENTRANT_CALL, not OK.                        *)
(*--------------------------------------------------------------------*)
ReentrancySafe ==
    (inStep /\ lastOp = "STEP" /\ lastError = "OK") =>
        ~inStep'  \* Can't happen: step succeeds while already in step

(*--------------------------------------------------------------------*)
(* WrongThreadSafe -- Gate 8c                                         *)
(*                                                                    *)
(* Any core API call from a thread other than the owner thread        *)
(* returns WRONG_THREAD.                                              *)
(*--------------------------------------------------------------------*)
WrongThreadSafe ==
    /\ instance = "CREATED"
    /\ currentThread # ownerThread
    /\ ownerThread # "None"
    => lastError \in {"WRONG_THREAD", "OK"}  \* OK only before the call

(*--------------------------------------------------------------------*)
(* ConfigValidated                                                    *)
(*                                                                    *)
(* A create with an invalid config never produces a CREATED instance. *)
(*--------------------------------------------------------------------*)
ConfigValidated ==
    lastError = "INVALID_CONFIG" => instance = "NONE"

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ instance = "NONE"
    /\ handle = "NULL"
    /\ opCount = 0
    /\ lastError = "OK"
    /\ lastOp = "NONE"
    /\ ownerThread = "None"
    /\ currentThread = "Main"
    /\ inStep = FALSE
    /\ trace = <<>>

(**************************************************************************)
(* ACTIONS -- API OPERATIONS                                              *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* legends_create(config, &handle)                                    *)
(*                                                                    *)
(* Creates a new emulator instance.                                   *)
(*   - Returns ALREADY_CREATED if instance exists                     *)
(*   - Returns INVALID_CONFIG if config is invalid                    *)
(*   - Returns VERSION_MISMATCH if API version wrong                  *)
(*   - Returns WRONG_THREAD -- N/A, no instance yet to own           *)
(*   - Returns OK and sets handle on success                          *)
(*--------------------------------------------------------------------*)
Create(cfgKind) ==
    /\ opCount < MaxOperations
    /\ IF instance = "CREATED"
       THEN \* Already have an instance
            /\ lastError' = "ALREADY_CREATED"
            /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
       ELSE IF cfgKind = "INVALID_CFG"
            THEN /\ lastError' = "INVALID_CONFIG"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
            ELSE IF cfgKind = "WRONG_VERSION"
                 THEN /\ lastError' = "VERSION_MISMATCH"
                      /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
                 ELSE \* Success
                      /\ instance' = "CREATED"
                      /\ handle' = "VALID"
                      /\ ownerThread' = currentThread
                      /\ lastError' = "OK"
                      /\ UNCHANGED inStep
    /\ lastOp' = "CREATE"
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "CREATE")
    /\ UNCHANGED currentThread

(*--------------------------------------------------------------------*)
(* legends_destroy(handle)                                            *)
(*                                                                    *)
(* Destroys an emulator instance.                                     *)
(*   - NULL handle is a no-op returning OK                            *)
(*   - Double-destroy is safe (second is no-op)                       *)
(*   - Wrong thread returns WRONG_THREAD                              *)
(*--------------------------------------------------------------------*)
Destroy ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN \* NULL handle -- no-op
            /\ lastError' = "OK"
            /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
       ELSE IF currentThread # ownerThread /\ ownerThread # "None"
            THEN \* Wrong thread
                 /\ lastError' = "WRONG_THREAD"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
            ELSE \* Destroy the instance
                 /\ instance' = "NONE"
                 /\ handle' = "NULL"
                 /\ ownerThread' = "None"
                 /\ inStep' = FALSE
                 /\ lastError' = "OK"
    /\ lastOp' = "DESTROY"
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "DESTROY")
    /\ UNCHANGED currentThread

(*--------------------------------------------------------------------*)
(* legends_step_ms / legends_step_cycles                              *)
(*                                                                    *)
(*   - Returns NULL_HANDLE if handle is NULL                          *)
(*   - Returns WRONG_THREAD from non-owner thread                     *)
(*   - Returns REENTRANT_CALL if already in step                      *)
(*   - Returns OK on success                                          *)
(*--------------------------------------------------------------------*)
Step ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN /\ lastError' = "NULL_HANDLE"
            /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
       ELSE IF currentThread # ownerThread /\ ownerThread # "None"
            THEN /\ lastError' = "WRONG_THREAD"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
            ELSE IF inStep
                 THEN /\ lastError' = "REENTRANT_CALL"
                      /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
                 ELSE /\ lastError' = "OK"
                      /\ inStep' = TRUE
                      /\ UNCHANGED <<instance, handle, ownerThread>>
    /\ lastOp' = "STEP"
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "STEP")
    /\ UNCHANGED currentThread

(*--------------------------------------------------------------------*)
(* Step completes (returns from step call)                            *)
(*                                                                    *)
(* Models the completion of a step -- clears the reentrancy guard.    *)
(*--------------------------------------------------------------------*)
StepComplete ==
    /\ inStep
    /\ inStep' = FALSE
    /\ UNCHANGED <<instance, handle, opCount, lastError, lastOp,
                   ownerThread, currentThread, trace>>

(*--------------------------------------------------------------------*)
(* legends_reset(handle)                                              *)
(*                                                                    *)
(*   - Returns NULL_HANDLE if handle is NULL                          *)
(*   - Returns WRONG_THREAD from non-owner thread                     *)
(*   - Returns OK on success (re-initialises emulator state)          *)
(*--------------------------------------------------------------------*)
Reset ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN /\ lastError' = "NULL_HANDLE"
            /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
       ELSE IF currentThread # ownerThread /\ ownerThread # "None"
            THEN /\ lastError' = "WRONG_THREAD"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
            ELSE /\ lastError' = "OK"
                 /\ inStep' = FALSE  \* Reset clears reentrancy guard
                 /\ UNCHANGED <<instance, handle, ownerThread>>
    /\ lastOp' = "RESET"
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "RESET")
    /\ UNCHANGED currentThread

(*--------------------------------------------------------------------*)
(* Generic core API call (CAPTURE, INPUT, SAVE, LOAD)                 *)
(*                                                                    *)
(* These share the same precondition checks:                          *)
(*   - NULL_HANDLE if no instance                                     *)
(*   - WRONG_THREAD from non-owner thread                             *)
(*   - OK on success                                                  *)
(*--------------------------------------------------------------------*)
CoreAPI(op) ==
    /\ op \in {"CAPTURE", "INPUT", "SAVE", "LOAD"}
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN /\ lastError' = "NULL_HANDLE"
            /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
       ELSE IF currentThread # ownerThread /\ ownerThread # "None"
            THEN /\ lastError' = "WRONG_THREAD"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
            ELSE /\ lastError' = "OK"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
    /\ lastOp' = op
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, op)
    /\ UNCHANGED currentThread

(*--------------------------------------------------------------------*)
(* Thread switch -- model the possibility of calls from wrong thread  *)
(*--------------------------------------------------------------------*)
SwitchThread(t) ==
    /\ t \in ThreadId
    /\ t # currentThread
    /\ currentThread' = t
    /\ UNCHANGED <<instance, handle, opCount, lastError, lastOp,
                   ownerThread, inStep, trace>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E cfg \in ConfigKind : Create(cfg)
    \/ Destroy
    \/ Step
    \/ StepComplete
    \/ Reset
    \/ \E op \in {"CAPTURE", "INPUT", "SAVE", "LOAD"} : CoreAPI(op)
    \/ \E t \in ThreadId : SwitchThread(t)
    \/ UNCHANGED vars  \* Stuttering

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Destroy) /\ WF_vars(StepComplete)

(**************************************************************************)
(* LIVENESS PROPERTIES                                                    *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* EventualTermination                                                *)
(*                                                                    *)
(* With weak fairness on Destroy, every created instance eventually   *)
(* gets destroyed.                                                    *)
(*--------------------------------------------------------------------*)
EventualTermination ==
    instance = "CREATED" ~> instance = "NONE"

(*--------------------------------------------------------------------*)
(* CreateDestroyLoop                                                  *)
(*                                                                    *)
(* After destruction, a new instance can be created.                  *)
(*--------------------------------------------------------------------*)
CreateDestroyLoop ==
    [](instance = "NONE" => <>(instance = "CREATED"))

(*--------------------------------------------------------------------*)
(* NoOrphanedHandles                                                  *)
(*--------------------------------------------------------------------*)
NoOrphanedHandles ==
    [](instance = "NONE" => handle = "NULL")

=======================================================================
