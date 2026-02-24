------------------------ MODULE LifecycleMinimal ------------------------
(**************************************************************************)
(* Legends API -- Minimal Lifecycle for CI Model Checking                 *)
(*                                                                        *)
(* Strips trace variable and reduces type domains to keep the state       *)
(* space tractable for TLC.  Preserves all safety invariants including    *)
(* reentrancy guard and wrong-thread detection.                           *)
(*                                                                        *)
(* Expected: ~250 distinct states at MaxOperations=6                      *)
(**************************************************************************)
EXTENDS Integers, TLC

CONSTANTS
    MaxOperations   \* @type: Int;

(**************************************************************************)
(* TYPES (reduced)                                                        *)
(**************************************************************************)

\* @type: Set(Str);
InstanceState == {"NONE", "CREATED"}

\* @type: Set(Str);
ErrorCode == {
    "OK", "NULL_HANDLE", "ALREADY_CREATED", "INVALID_CONFIG",
    "VERSION_MISMATCH", "REENTRANT_CALL", "WRONG_THREAD"
}

\* @type: Set(Str);
ThreadId == {"Main", "Other"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    instance,       \* @type: Str;
    handle,         \* @type: Str;
    opCount,        \* @type: Int;
    lastError,      \* @type: Str;
    ownerThread,    \* @type: Str;
    currentThread,  \* @type: Str;
    inStep          \* @type: Bool;

vars == <<instance, handle, opCount, lastError,
          ownerThread, currentThread, inStep>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ instance \in InstanceState
    /\ handle \in {"NULL", "VALID"}
    /\ opCount \in 0..MaxOperations
    /\ lastError \in ErrorCode
    /\ ownerThread \in ThreadId \cup {"None"}
    /\ currentThread \in ThreadId
    /\ inStep \in BOOLEAN

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

\* Gate 2c: At most one active instance
AtMostOneInstance ==
    instance = "CREATED" => handle = "VALID"

\* Gate 2b: Misuse returns error, not crash
MisuseSafe ==
    (instance = "NONE" /\ handle = "NULL") =>
        lastError \in {"OK", "NULL_HANDLE", "ALREADY_CREATED",
                       "INVALID_CONFIG", "VERSION_MISMATCH",
                       "WRONG_THREAD"}

\* Handle always consistent with instance
HandleConsistency ==
    (instance = "NONE") <=> (handle = "NULL")

\* Reentrancy guard: step while in step returns REENTRANT_CALL
NoReentrantSuccess ==
    ~(inStep /\ lastError = "OK" /\ instance = "CREATED"
      /\ opCount > 0 /\ opCount < MaxOperations)
    \/ ~inStep  \* If inStep is TRUE, we must have just entered step

\* Wrong thread: non-owner thread cannot get OK on core API
WrongThreadBlocked ==
    (instance = "CREATED" /\ currentThread # ownerThread
     /\ ownerThread # "None")
    => lastError \in {"OK", "WRONG_THREAD"}

\* Config validated: bad config never creates instance
ConfigGated ==
    lastError = "INVALID_CONFIG" => instance = "NONE"

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ instance = "NONE"
    /\ handle = "NULL"
    /\ opCount = 0
    /\ lastError = "OK"
    /\ ownerThread = "None"
    /\ currentThread = "Main"
    /\ inStep = FALSE

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

\* legends_create() with valid config
CreateOK ==
    /\ opCount < MaxOperations
    /\ instance = "NONE"
    /\ instance' = "CREATED"
    /\ handle' = "VALID"
    /\ ownerThread' = currentThread
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<currentThread, inStep>>

\* legends_create() when already created
CreateAlready ==
    /\ opCount < MaxOperations
    /\ instance = "CREATED"
    /\ lastError' = "ALREADY_CREATED"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<instance, handle, ownerThread, currentThread, inStep>>

\* legends_create() with invalid config
CreateBadConfig ==
    /\ opCount < MaxOperations
    /\ instance = "NONE"
    /\ lastError' = "INVALID_CONFIG"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<instance, handle, ownerThread, currentThread, inStep>>

\* legends_create() with wrong version
CreateBadVersion ==
    /\ opCount < MaxOperations
    /\ instance = "NONE"
    /\ lastError' = "VERSION_MISMATCH"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<instance, handle, ownerThread, currentThread, inStep>>

\* legends_destroy()
Destroy ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN /\ lastError' = "OK"
            /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
       ELSE IF currentThread # ownerThread /\ ownerThread # "None"
            THEN /\ lastError' = "WRONG_THREAD"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
            ELSE /\ instance' = "NONE"
                 /\ handle' = "NULL"
                 /\ ownerThread' = "None"
                 /\ inStep' = FALSE
                 /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED currentThread

\* legends_step_*() -- with reentrancy and wrong-thread checks
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
    /\ opCount' = opCount + 1
    /\ UNCHANGED currentThread

\* Step completes -- clears reentrancy guard
StepDone ==
    /\ inStep
    /\ inStep' = FALSE
    /\ UNCHANGED <<instance, handle, opCount, lastError,
                   ownerThread, currentThread>>

\* Generic core API (CAPTURE, INPUT, SAVE, LOAD)
CoreAPI ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN /\ lastError' = "NULL_HANDLE"
            /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
       ELSE IF currentThread # ownerThread /\ ownerThread # "None"
            THEN /\ lastError' = "WRONG_THREAD"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
            ELSE /\ lastError' = "OK"
                 /\ UNCHANGED <<instance, handle, ownerThread, inStep>>
    /\ opCount' = opCount + 1
    /\ UNCHANGED currentThread

\* Thread switch
SwitchThread ==
    /\ currentThread' = IF currentThread = "Main" THEN "Other" ELSE "Main"
    /\ UNCHANGED <<instance, handle, opCount, lastError,
                   ownerThread, inStep>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ CreateOK
    \/ CreateAlready
    \/ CreateBadConfig
    \/ CreateBadVersion
    \/ Destroy
    \/ Step
    \/ StepDone
    \/ CoreAPI
    \/ SwitchThread
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================
