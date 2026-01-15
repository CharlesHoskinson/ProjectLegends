---------------------------- MODULE Threading ----------------------------
(*
 * Legends - Threading Model Contract
 *
 * This module specifies the threading guarantees:
 * - Core is single-threaded
 * - PAL may have threads but they never call core
 * - All legends_* API calls from same thread
 *
 * Key invariants:
 * - CoreSingleThreaded: Only one thread in core at a time
 * - PALIsolation: PAL threads never invoke core
 * - NoDataRaces: No concurrent access to shared state
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    MaxOperations   \* Maximum operations to model-check

\* =====================================================================
\* TYPES
\* =====================================================================

\* Thread identifiers
ThreadId == {"Main", "AudioCallback", "InputPoll", "Timer"}

\* Thread ownership
Owner == {"None", "Main", "PAL"}

\* Operation types
OpType == {"CORE_API", "PAL_INTERNAL", "CALLBACK"}

\* Code regions
CodeRegion == {"USER", "CORE", "PAL", "SYSTEM"}

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    activeThread,       \* Currently executing thread
    coreOwner,          \* Thread that owns core (or None)
    palThreads,         \* Set of active PAL threads
    callStack,          \* Current call stack (for invariant checking)
    opCount,            \* Operation counter
    dataRaceDetected    \* Flag for data race detection

vars == <<activeThread, coreOwner, palThreads, callStack,
          opCount, dataRaceDetected>>

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

TypeOK ==
    /\ activeThread \in ThreadId
    /\ coreOwner \in {"None", "Main"}  \* Only Main can own core
    /\ palThreads \subseteq ThreadId
    /\ callStack \in Seq(CodeRegion)
    /\ opCount \in 0..MaxOperations
    /\ dataRaceDetected \in BOOLEAN

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

(*
 * CoreSingleThreaded - At most one thread in core
 *
 * The core emulation is not thread-safe.
 * Only the main thread may call legends_* functions.
 *)
CoreSingleThreaded ==
    coreOwner \in {"None", "Main"}

(*
 * PALIsolation - PAL threads never enter core
 *
 * Threads spawned by PAL (audio callback, etc.) must never
 * invoke any legends_* API functions.
 *)
PALIsolation ==
    \A t \in palThreads :
        t # "Main" => coreOwner # t

(*
 * NoDataRaces - Concurrent access properly synchronized
 *)
NoDataRaces ==
    ~dataRaceDetected

(*
 * CallStackValid - Call stack respects boundaries
 *
 * PAL code can call system, but not core.
 * Core code can call PAL.
 *)
CallStackValid ==
    \* If in PAL internal thread, CORE should not be on stack
    (activeThread \in {"AudioCallback", "InputPoll", "Timer"}) =>
        "CORE" \notin {callStack[i] : i \in 1..Len(callStack)}

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

Init ==
    /\ activeThread = "Main"
    /\ coreOwner = "None"
    /\ palThreads = {}
    /\ callStack = <<>>
    /\ opCount = 0
    /\ dataRaceDetected = FALSE

\* =====================================================================
\* ACTIONS - THREAD MANAGEMENT
\* =====================================================================

(*
 * Main thread calls legends_* API
 *
 * This is the only valid way to enter core code.
 *)
MainCallsCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "None"
    /\ opCount < MaxOperations
    /\ coreOwner' = "Main"
    /\ callStack' = Append(callStack, "CORE")
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, palThreads, dataRaceDetected>>

(*
 * Main thread returns from core
 *)
MainReturnsFromCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "Main"
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "CORE"
    /\ coreOwner' = "None"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, palThreads, opCount, dataRaceDetected>>

(*
 * Core calls PAL (e.g., for audio push)
 *)
CoreCallsPAL ==
    /\ coreOwner = "Main"
    /\ callStack' = Append(callStack, "PAL")
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, opCount, dataRaceDetected>>

(*
 * Return from PAL to core
 *)
ReturnFromPAL ==
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "PAL"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, opCount, dataRaceDetected>>

\* =====================================================================
\* ACTIONS - PAL THREADS
\* =====================================================================

(*
 * PAL spawns internal thread (e.g., SDL audio callback)
 *)
PALSpawnThread(tid) ==
    /\ tid \in {"AudioCallback", "InputPoll", "Timer"}
    /\ tid \notin palThreads
    /\ palThreads' = palThreads \cup {tid}
    /\ UNCHANGED <<activeThread, coreOwner, callStack, opCount, dataRaceDetected>>

(*
 * PAL thread terminates
 *)
PALThreadExit(tid) ==
    /\ tid \in palThreads
    /\ palThreads' = palThreads \ {tid}
    /\ UNCHANGED <<activeThread, coreOwner, callStack, opCount, dataRaceDetected>>

(*
 * Context switch to PAL thread
 *)
SwitchToPALThread(tid) ==
    /\ tid \in palThreads
    /\ activeThread' = tid
    /\ UNCHANGED <<coreOwner, palThreads, callStack, opCount, dataRaceDetected>>

(*
 * Return to main thread
 *)
SwitchToMain ==
    /\ activeThread # "Main"
    /\ activeThread' = "Main"
    /\ UNCHANGED <<coreOwner, palThreads, callStack, opCount, dataRaceDetected>>

\* =====================================================================
\* ACTIONS - DATA RACE DETECTION
\* =====================================================================

(*
 * ILLEGAL: PAL thread attempts to call core
 *
 * This action models the forbidden behavior.
 * If it happens, we set dataRaceDetected.
 *)
PALThreadCallsCore_ILLEGAL ==
    /\ activeThread \in {"AudioCallback", "InputPoll", "Timer"}
    /\ activeThread \in palThreads
    /\ coreOwner = "None"  \* Core appears available
    \* This would be a bug - PAL thread must not call core
    /\ dataRaceDetected' = TRUE
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, callStack, opCount>>

(*
 * ILLEGAL: Two threads try to enter core
 *
 * This action models concurrent core access.
 *)
ConcurrentCoreAccess_ILLEGAL ==
    /\ coreOwner = "Main"
    /\ activeThread # "Main"
    \* Another thread tries to enter core while Main is in it
    /\ dataRaceDetected' = TRUE
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, callStack, opCount>>

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================

\* Legal transitions
LegalNext ==
    \/ MainCallsCore
    \/ MainReturnsFromCore
    \/ CoreCallsPAL
    \/ ReturnFromPAL
    \/ \E t \in {"AudioCallback", "InputPoll", "Timer"} : PALSpawnThread(t)
    \/ \E t \in palThreads : PALThreadExit(t)
    \/ \E t \in palThreads : SwitchToPALThread(t)
    \/ SwitchToMain

\* All transitions (including illegal for testing)
Next ==
    \/ LegalNext
    \* Uncomment to test that illegal actions are caught:
    \* \/ PALThreadCallsCore_ILLEGAL
    \* \/ ConcurrentCoreAccess_ILLEGAL
    \/ UNCHANGED vars

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars

\* =====================================================================
\* PROPERTIES
\* =====================================================================

(*
 * AlwaysSafe - No data races ever detected
 *)
AlwaysSafe ==
    []~dataRaceDetected

(*
 * CoreAccessSerialized - Core access is sequential
 *)
CoreAccessSerialized ==
    [](coreOwner = "Main" => activeThread = "Main")

(*
 * PALThreadsNeverInCore - Structural guarantee
 *)
PALThreadsNeverInCore ==
    [](\A t \in palThreads : t # coreOwner)

(*
 * MainCanAlwaysAccessCore - Main thread is not starved
 *)
MainCanAccessCore ==
    [](activeThread = "Main" /\ coreOwner = "None" =>
       <>coreOwner = "Main")

=======================================================================
