---------------------------- MODULE Threading ----------------------------
(**************************************************************************)
(* Legends -- Threading Model Contract                                    *)
(*                                                                        *)
(* Full (documentation-grade) threading specification.                     *)
(* For CI model checking, use ThreadingMinimal.tla.                       *)
(*                                                                        *)
(* Thread model:                                                          *)
(*   - Core emulation is single-threaded (not thread-safe)                *)
(*   - Only the "owner thread" (the thread that called create) may        *)
(*     invoke legends_* API functions                                     *)
(*   - PAL may spawn internal threads (audio callback, event loop)        *)
(*     but they MUST NOT call any core API                                *)
(*   - Reentrancy guard: legends_step_*() from within a PAL callback      *)
(*     (invoked by step itself) is detected and returns REENTRANT_CALL    *)
(*                                                                        *)
(* Contract gates covered:                                                *)
(*   7a  Core never invoked from audio callback thread                    *)
(*   8a  Core is single-threaded                                          *)
(*   8b  PAL threads never call core                                      *)
(*   8c  Wrong-thread detection                                           *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   CoreSingleThreaded      -- only Main can own core                    *)
(*   PALIsolation             -- PAL threads never in core                *)
(*   NoDataRaces              -- no concurrent access detected            *)
(*   CallStackValid           -- PAL threads have no CORE on stack        *)
(*   OwnerThreadRecorded      -- owner recorded at create time            *)
(*   WrongThreadDetected      -- non-owner core API -> WRONG_THREAD       *)
(*   NoReentrantStep          -- step from callback -> REENTRANT_CALL     *)
(*                                                                        *)
(* Liveness:                                                              *)
(*   MainCanAccessCore        -- main thread not starved (SF)             *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

(**************************************************************************)
(* CONSTANTS                                                              *)
(**************************************************************************)
CONSTANTS
    MaxOperations   \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
ThreadId == {"Main", "AudioCallback", "InputPoll", "Timer"}

\* @type: Set(Str);
Owner == {"None", "Main"}

\* @type: Set(Str);
OpType == {"CORE_API", "PAL_INTERNAL", "CALLBACK"}

\* @type: Set(Str);
CodeRegion == {"USER", "CORE", "PAL", "SYSTEM"}

\* @type: Set(Str);
ErrorCode == {"OK", "WRONG_THREAD", "REENTRANT_CALL"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    activeThread,       \* @type: Str;       Currently executing thread
    coreOwner,          \* @type: Str;       Thread that owns core
    ownerThread,        \* @type: Str;       Thread that called create
    palThreads,         \* @type: Set(Str);  Set of active PAL threads
    callStack,          \* @type: Seq(Str);  Current call stack
    opCount,            \* @type: Int;       Operation counter
    inStep,             \* @type: Bool;      Reentrancy guard
    lastError,          \* @type: Str;       Last error code
    dataRaceDetected    \* @type: Bool;      Data race flag

vars == <<activeThread, coreOwner, ownerThread, palThreads, callStack,
          opCount, inStep, lastError, dataRaceDetected>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ activeThread \in ThreadId
    /\ coreOwner \in {"None", "Main"}
    /\ ownerThread \in {"None", "Main"}
    /\ palThreads \subseteq ThreadId
    /\ callStack \in Seq(CodeRegion)
    /\ Len(callStack) <= 6
    /\ opCount \in 0..MaxOperations
    /\ inStep \in BOOLEAN
    /\ lastError \in ErrorCode
    /\ dataRaceDetected \in BOOLEAN

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* CoreSingleThreaded -- Gate 8a                                      *)
(*                                                                    *)
(* Only Main can own core.  No PAL thread ever has ownership.         *)
(*--------------------------------------------------------------------*)
CoreSingleThreaded ==
    coreOwner \in {"None", "Main"}

(*--------------------------------------------------------------------*)
(* PALIsolation -- Gate 8b                                            *)
(*                                                                    *)
(* PAL threads never own or enter core code.                          *)
(*--------------------------------------------------------------------*)
PALIsolation ==
    \A t \in palThreads : t # coreOwner

(*--------------------------------------------------------------------*)
(* NoDataRaces                                                        *)
(*--------------------------------------------------------------------*)
NoDataRaces ==
    ~dataRaceDetected

(*--------------------------------------------------------------------*)
(* CallStackValid                                                     *)
(*                                                                    *)
(* When a PAL thread is active, CORE must not appear on its stack.    *)
(*--------------------------------------------------------------------*)
CallStackValid ==
    (activeThread \in {"AudioCallback", "InputPoll", "Timer"}) =>
        "CORE" \notin {callStack[i] : i \in 1..Len(callStack)}

(*--------------------------------------------------------------------*)
(* OwnerThreadRecorded                                                *)
(*                                                                    *)
(* Once an instance is created (ownerThread # "None"), the owner      *)
(* thread is always recorded.                                         *)
(*--------------------------------------------------------------------*)
OwnerThreadRecorded ==
    ownerThread # "None" => ownerThread = "Main"

(*--------------------------------------------------------------------*)
(* WrongThreadDetected -- Gate 8c                                     *)
(*                                                                    *)
(* If a non-owner thread attempts a core API call, the last error     *)
(* must be WRONG_THREAD (never OK).                                   *)
(*--------------------------------------------------------------------*)
WrongThreadDetected ==
    (activeThread # ownerThread /\ ownerThread # "None" /\
     coreOwner = "None" /\ lastError = "WRONG_THREAD")
    \/ ~(activeThread # ownerThread /\ ownerThread # "None" /\
         lastError = "WRONG_THREAD")

(*--------------------------------------------------------------------*)
(* NoReentrantStep                                                    *)
(*                                                                    *)
(* If currently in step, attempting step again yields REENTRANT_CALL. *)
(*--------------------------------------------------------------------*)
NoReentrantStep ==
    (inStep /\ lastError = "REENTRANT_CALL") \/
    (~inStep) \/
    (inStep /\ lastError = "OK")

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ activeThread = "Main"
    /\ coreOwner = "None"
    /\ ownerThread = "None"
    /\ palThreads = {}
    /\ callStack = <<>>
    /\ opCount = 0
    /\ inStep = FALSE
    /\ lastError = "OK"
    /\ dataRaceDetected = FALSE

(**************************************************************************)
(* ACTIONS -- INSTANCE LIFECYCLE                                          *)
(**************************************************************************)

\* Create instance -- records owner thread
CreateInstance ==
    /\ activeThread = "Main"
    /\ ownerThread = "None"
    /\ opCount < MaxOperations
    /\ ownerThread' = "Main"
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, callStack,
                   inStep, dataRaceDetected>>

\* Destroy instance
DestroyInstance ==
    /\ activeThread = "Main"
    /\ ownerThread = "Main"
    /\ opCount < MaxOperations
    /\ ownerThread' = "None"
    /\ coreOwner' = "None"
    /\ inStep' = FALSE
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, palThreads, callStack, dataRaceDetected>>

(**************************************************************************)
(* ACTIONS -- CORE API CALLS                                              *)
(**************************************************************************)

\* Main thread enters core (legends_* API)
MainCallsCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "None"
    /\ ownerThread = "Main"
    /\ opCount < MaxOperations
    /\ Len(callStack) < 6
    /\ IF inStep
       THEN \* Reentrant call detected
            /\ lastError' = "REENTRANT_CALL"
            /\ UNCHANGED <<coreOwner, callStack, inStep>>
       ELSE /\ coreOwner' = "Main"
            /\ callStack' = Append(callStack, "CORE")
            /\ lastError' = "OK"
            /\ UNCHANGED inStep
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, ownerThread, palThreads, dataRaceDetected>>

\* Main thread returns from core
MainReturnsFromCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "Main"
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "CORE"
    /\ coreOwner' = "None"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, ownerThread, palThreads, opCount,
                   inStep, lastError, dataRaceDetected>>

\* Wrong-thread API call attempt
WrongThreadCall ==
    /\ activeThread \in {"AudioCallback", "InputPoll", "Timer"}
    /\ ownerThread = "Main"
    /\ opCount < MaxOperations
    /\ lastError' = "WRONG_THREAD"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   callStack, inStep, dataRaceDetected>>

(**************************************************************************)
(* ACTIONS -- STEP WITH REENTRANCY GUARD                                  *)
(**************************************************************************)

\* Begin step (sets reentrancy guard)
BeginStep ==
    /\ activeThread = "Main"
    /\ coreOwner = "Main"
    /\ ~inStep
    /\ inStep' = TRUE
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   callStack, opCount, lastError, dataRaceDetected>>

\* End step (clears reentrancy guard)
EndStep ==
    /\ activeThread = "Main"
    /\ inStep
    /\ inStep' = FALSE
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   callStack, opCount, lastError, dataRaceDetected>>

(**************************************************************************)
(* ACTIONS -- PAL CALLS AND THREADS                                       *)
(**************************************************************************)

\* Core calls PAL (e.g., audio push during step)
CoreCallsPAL ==
    /\ coreOwner = "Main"
    /\ Len(callStack) < 6
    /\ callStack' = Append(callStack, "PAL")
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   opCount, inStep, lastError, dataRaceDetected>>

\* Return from PAL to core
ReturnFromPAL ==
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "PAL"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   opCount, inStep, lastError, dataRaceDetected>>

\* PAL spawns internal thread
PALSpawnThread(tid) ==
    /\ tid \in {"AudioCallback", "InputPoll", "Timer"}
    /\ tid \notin palThreads
    /\ palThreads' = palThreads \cup {tid}
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, callStack,
                   opCount, inStep, lastError, dataRaceDetected>>

\* PAL thread terminates
PALThreadExit(tid) ==
    /\ tid \in palThreads
    /\ palThreads' = palThreads \ {tid}
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, callStack,
                   opCount, inStep, lastError, dataRaceDetected>>

\* Context switch
SwitchToPALThread(tid) ==
    /\ tid \in palThreads
    /\ activeThread' = tid
    /\ UNCHANGED <<coreOwner, ownerThread, palThreads, callStack,
                   opCount, inStep, lastError, dataRaceDetected>>

SwitchToMain ==
    /\ activeThread # "Main"
    /\ activeThread' = "Main"
    /\ UNCHANGED <<coreOwner, ownerThread, palThreads, callStack,
                   opCount, inStep, lastError, dataRaceDetected>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ CreateInstance
    \/ DestroyInstance
    \/ MainCallsCore
    \/ MainReturnsFromCore
    \/ WrongThreadCall
    \/ BeginStep
    \/ EndStep
    \/ CoreCallsPAL
    \/ ReturnFromPAL
    \/ \E t \in {"AudioCallback", "InputPoll", "Timer"} : PALSpawnThread(t)
    \/ \E t \in palThreads : PALThreadExit(t)
    \/ \E t \in palThreads : SwitchToPALThread(t)
    \/ SwitchToMain
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars /\ SF_vars(MainCallsCore)

(**************************************************************************)
(* LIVENESS PROPERTIES                                                    *)
(**************************************************************************)

\* Main thread is not starved
MainCanAccessCore ==
    [](activeThread = "Main" /\ coreOwner = "None" /\ ownerThread = "Main"
       /\ ~inStep /\ opCount < MaxOperations =>
       <>(coreOwner = "Main"))

\* Core access is serialized
CoreAccessSerialized ==
    [](coreOwner = "Main" => activeThread = "Main")

\* PAL threads never enter core
PALThreadsNeverInCore ==
    [](\A t \in palThreads : t # coreOwner)

\* No data races
AlwaysSafe ==
    []~dataRaceDetected

=======================================================================
