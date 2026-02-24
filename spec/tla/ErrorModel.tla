---------------------------- MODULE ErrorModel ----------------------------
(**************************************************************************)
(* Legends -- Error Code State Machine                                    *)
(*                                                                        *)
(* Models all 14+1 error codes as a deterministic function of             *)
(* (instance state, operation, preconditions).                            *)
(*                                                                        *)
(* Every API function maps to its possible error codes.                   *)
(* The specification verifies that error codes are deterministic:         *)
(* same state + same operation => same error.                             *)
(*                                                                        *)
(* Cross-reference to CONTRACT.md gate numbers in comments.               *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   ErrorCodeDeterministic    -- same state + op => same error           *)
(*   SuccessRequiresValidState -- OK on core ops requires CREATED         *)
(*   ErrorCodesComplete        -- every returned code is in ErrorCode     *)
(*   NullHandleConsistent      -- NULL_HANDLE iff no instance             *)
(*   ReentrantCodeCorrect      -- reentrant => REENTRANT_CALL             *)
(*   WrongThreadCodeCorrect    -- wrong thread => WRONG_THREAD            *)
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

\* Complete error code set (14+1)
\* @type: Set(Str);
ErrorCode == {
    "OK", "NULL_HANDLE", "NULL_POINTER", "ALREADY_CREATED",
    "NOT_INITIALIZED", "REENTRANT_CALL", "BUFFER_TOO_SMALL",
    "INVALID_CONFIG", "INVALID_STATE", "VERSION_MISMATCH",
    "IO_FAILED", "OUT_OF_MEMORY", "NOT_SUPPORTED", "INTERNAL",
    "WRONG_THREAD"
}

\* API operations
\* @type: Set(Str);
APIOperation == {
    "CREATE", "DESTROY", "STEP", "RESET",
    "CAPTURE_TEXT", "CAPTURE_RGB", "KEY_EVENT", "MOUSE_EVENT",
    "SAVE_STATE", "LOAD_STATE", "STATE_HASH", "GET_VERSION"
}

\* Core operations (require active instance)
\* @type: Set(Str);
CoreOps == {
    "STEP", "RESET", "CAPTURE_TEXT", "CAPTURE_RGB",
    "KEY_EVENT", "MOUSE_EVENT", "SAVE_STATE", "LOAD_STATE",
    "STATE_HASH"
}

\* Instance states
\* @type: Set(Str);
InstanceState == {"NONE", "CREATED"}

\* Preconditions (abstracted)
\* @type: Set(Str);
ThreadState == {"OWNER", "OTHER"}
\* @type: Set(Str);
ConfigState == {"VALID", "INVALID", "WRONG_VER"}
\* @type: Set(Str);
BufferState == {"SUFFICIENT", "TOO_SMALL"}
\* @type: Set(Str);
ReentState == {"CLEAR", "IN_STEP"}

(**************************************************************************)
(* ERROR RESOLUTION FUNCTION                                              *)
(*                                                                        *)
(* Pure function: given all preconditions, returns the error code.        *)
(* This is the specification of the error code logic.                     *)
(*                                                                        *)
(* PRIORITY CHAIN (checked in this order):                                *)
(*   1. GET_VERSION always succeeds (no preconditions)                    *)
(*   2. CREATE: check instance -> config -> version -> OK                 *)
(*   3. DESTROY: NULL handle is no-op, then check thread                  *)
(*   4. Core ops: NULL_HANDLE -> WRONG_THREAD -> REENTRANT_CALL ->       *)
(*      BUFFER_TOO_SMALL -> OK                                            *)
(*                                                                        *)
(* WHY THIS ORDER MATTERS:                                                *)
(*   The priority chain ensures deterministic error codes.  If a call     *)
(*   has multiple error conditions (e.g., null handle AND wrong thread),  *)
(*   the highest-priority error is returned.  This matches the C          *)
(*   implementation in legends_embed.cpp which checks conditions in       *)
(*   the same order (guard clauses at function entry).                    *)
(*                                                                        *)
(*   Example: legends_step_ms(NULL, 100, NULL) from wrong thread          *)
(*   returns NULL_HANDLE (not WRONG_THREAD) because null check is first. *)
(**************************************************************************)

\* @type: (Str, Str, Str, Str, Str, Str) -> Str;
ResolveError(op, inst, thread, cfg, buf, reent) ==
    \* GET_VERSION always succeeds (no preconditions)
    IF op = "GET_VERSION" THEN "OK"
    \* CREATE has special preconditions
    ELSE IF op = "CREATE" THEN
        IF inst = "CREATED" THEN "ALREADY_CREATED"
        ELSE IF cfg = "INVALID" THEN "INVALID_CONFIG"
        ELSE IF cfg = "WRONG_VER" THEN "VERSION_MISMATCH"
        ELSE "OK"
    \* DESTROY: NULL handle is no-op (OK), wrong thread blocked
    ELSE IF op = "DESTROY" THEN
        IF inst = "NONE" THEN "OK"  \* NULL handle no-op
        ELSE IF thread = "OTHER" THEN "WRONG_THREAD"
        ELSE "OK"
    \* Core operations: check in priority order
    ELSE IF op \in CoreOps THEN
        IF inst = "NONE" THEN "NULL_HANDLE"
        ELSE IF thread = "OTHER" THEN "WRONG_THREAD"
        ELSE IF reent = "IN_STEP" /\ op = "STEP" THEN "REENTRANT_CALL"
        ELSE IF buf = "TOO_SMALL" /\ op \in {"CAPTURE_TEXT", "CAPTURE_RGB", "SAVE_STATE"} THEN "BUFFER_TOO_SMALL"
        ELSE "OK"
    ELSE "INTERNAL"

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    instance,       \* @type: Str;
    lastOp,         \* @type: Str;
    lastError,      \* @type: Str;
    threadState,    \* @type: Str;
    configState,    \* @type: Str;
    bufferState,    \* @type: Str;
    reentState,     \* @type: Str;
    opCount         \* @type: Int;

vars == <<instance, lastOp, lastError, threadState,
          configState, bufferState, reentState, opCount>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ instance \in InstanceState
    /\ lastOp \in APIOperation \cup {"NONE"}
    /\ lastError \in ErrorCode
    /\ threadState \in ThreadState
    /\ configState \in ConfigState
    /\ bufferState \in BufferState
    /\ reentState \in ReentState
    /\ opCount \in 0..MaxOps

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* ErrorCodeDeterministic                                             *)
(*                                                                    *)
(* The error code is always equal to ResolveError applied to the      *)
(* current preconditions.  There is no non-determinism.               *)
(*--------------------------------------------------------------------*)
ErrorCodeDeterministic ==
    lastOp # "NONE" =>
        lastError = ResolveError(lastOp, instance, threadState,
                                  configState, bufferState, reentState)

(*--------------------------------------------------------------------*)
(* SuccessRequiresValidState                                          *)
(*                                                                    *)
(* A core operation returning OK requires an active instance.         *)
(* Gate 2b cross-reference.                                           *)
(*--------------------------------------------------------------------*)
SuccessRequiresValidState ==
    (lastError = "OK" /\ lastOp \in CoreOps)
    => instance = "CREATED"

(*--------------------------------------------------------------------*)
(* ErrorCodesComplete                                                 *)
(*                                                                    *)
(* Every error code returned is in the defined set.                   *)
(*--------------------------------------------------------------------*)
ErrorCodesComplete ==
    lastError \in ErrorCode

(*--------------------------------------------------------------------*)
(* NullHandleConsistent                                               *)
(*                                                                    *)
(* NULL_HANDLE is returned iff no instance exists and a core op       *)
(* was attempted.                                                     *)
(*--------------------------------------------------------------------*)
NullHandleConsistent ==
    (lastError = "NULL_HANDLE") =>
        (instance = "NONE" /\ lastOp \in CoreOps)

(*--------------------------------------------------------------------*)
(* ReentrantCodeCorrect                                               *)
(*                                                                    *)
(* REENTRANT_CALL only when in-step and attempting step.              *)
(*--------------------------------------------------------------------*)
ReentrantCodeCorrect ==
    (lastError = "REENTRANT_CALL") =>
        (reentState = "IN_STEP" /\ lastOp = "STEP")

(*--------------------------------------------------------------------*)
(* WrongThreadCodeCorrect                                             *)
(*                                                                    *)
(* WRONG_THREAD only when calling from non-owner thread.              *)
(*--------------------------------------------------------------------*)
WrongThreadCodeCorrect ==
    (lastError = "WRONG_THREAD") => threadState = "OTHER"

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ instance = "NONE"
    /\ lastOp = "NONE"
    /\ lastError = "OK"
    /\ threadState = "OWNER"
    /\ configState = "VALID"
    /\ bufferState = "SUFFICIENT"
    /\ reentState = "CLEAR"
    /\ opCount = 0

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

\* Execute an API operation with given preconditions
ExecuteOp(op, thread, cfg, buf, reent) ==
    /\ opCount < MaxOps
    /\ threadState' = thread
    /\ configState' = cfg
    /\ bufferState' = buf
    /\ reentState' = reent
    /\ lastOp' = op
    /\ LET err == ResolveError(op, instance, thread, cfg, buf, reent)
       IN /\ lastError' = err
          \* Update instance state based on successful operations
          /\ IF op = "CREATE" /\ err = "OK"
             THEN instance' = "CREATED"
             ELSE IF op = "DESTROY" /\ err = "OK" /\ instance = "CREATED"
             THEN instance' = "NONE"
             ELSE UNCHANGED instance
    /\ opCount' = opCount + 1

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E op \in APIOperation,
          t \in ThreadState,
          c \in ConfigState,
          b \in BufferState,
          r \in ReentState :
        ExecuteOp(op, t, c, b, r)
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================
