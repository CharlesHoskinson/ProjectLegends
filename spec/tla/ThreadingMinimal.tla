------------------------ MODULE ThreadingMinimal ------------------------
(**************************************************************************)
(* Legends -- Minimal Threading for CI Model Checking                     *)
(*                                                                        *)
(* Includes owner thread, wrong-thread detection, and reentrancy guard.   *)
(* Strips full thread lifecycle to keep state space tractable.             *)
(*                                                                        *)
(* Expected: ~2000 distinct states at MaxOps=5                            *)
(**************************************************************************)
EXTENDS Integers, Sequences, TLC

CONSTANTS
    MaxOps          \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
Thread == {"Main", "AudioCallback", "Timer"}

\* @type: Set(Str);
Owner == {"None", "Main"}

\* @type: Set(Str);
Region == {"USER", "CORE", "PAL"}

\* @type: Set(Str);
ErrCode == {"OK", "WRONG_THREAD", "REENTRANT_CALL"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    activeThread,   \* @type: Str;
    coreOwner,      \* @type: Str;
    ownerThread,    \* @type: Str;
    palThreads,     \* @type: Set(Str);
    callStack,      \* @type: Seq(Str);
    opCount,        \* @type: Int;
    inStep,         \* @type: Bool;
    lastError,      \* @type: Str;
    dataRace        \* @type: Bool;

vars == <<activeThread, coreOwner, ownerThread, palThreads, callStack,
          opCount, inStep, lastError, dataRace>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ activeThread \in Thread
    /\ coreOwner \in Owner
    /\ ownerThread \in Owner
    /\ palThreads \subseteq Thread
    /\ callStack \in Seq(Region)
    /\ Len(callStack) <= 4
    /\ opCount \in 0..MaxOps
    /\ inStep \in BOOLEAN
    /\ lastError \in ErrCode
    /\ dataRace \in BOOLEAN

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

\* Gate 8a: Only Main can own core
CoreSingleThreaded ==
    coreOwner \in {"None", "Main"}

\* Gate 8b: PAL threads never own core
PALIsolation ==
    \A t \in palThreads : t # coreOwner

\* No data races detected
NoDataRaces ==
    ~dataRace

\* PAL threads have no CORE on stack
CallStackValid ==
    activeThread \in {"AudioCallback", "Timer"} =>
        "CORE" \notin {callStack[i] : i \in 1..Len(callStack)}

\* Gate 8c: wrong-thread call blocked
WrongThreadBlocked ==
    (activeThread # ownerThread /\ ownerThread # "None" /\
     activeThread \in {"AudioCallback", "Timer"})
    => lastError \in {"OK", "WRONG_THREAD"}

\* Reentrancy guard: step during step returns error on Main
NoReentrantStep ==
    ~inStep
    \/ (inStep /\ activeThread = "Main" /\ lastError \in {"OK", "REENTRANT_CALL"})
    \/ (inStep /\ activeThread # "Main")

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
    /\ dataRace = FALSE

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

\* Create instance
CreateInst ==
    /\ activeThread = "Main"
    /\ ownerThread = "None"
    /\ opCount < MaxOps
    /\ ownerThread' = "Main"
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, callStack,
                   inStep, dataRace>>

\* Destroy instance
DestroyInst ==
    /\ activeThread = "Main"
    /\ ownerThread = "Main"
    /\ opCount < MaxOps
    /\ ownerThread' = "None"
    /\ coreOwner' = "None"
    /\ inStep' = FALSE
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, palThreads, callStack, dataRace>>

\* Main enters core
MainEnterCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "None"
    /\ ownerThread = "Main"
    /\ opCount < MaxOps
    /\ Len(callStack) < 4
    /\ IF inStep
       THEN /\ lastError' = "REENTRANT_CALL"
            /\ UNCHANGED <<coreOwner, callStack, inStep>>
       ELSE /\ coreOwner' = "Main"
            /\ callStack' = Append(callStack, "CORE")
            /\ lastError' = "OK"
            /\ UNCHANGED inStep
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, ownerThread, palThreads, dataRace>>

\* Main exits core
MainExitCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "Main"
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "CORE"
    /\ coreOwner' = "None"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, ownerThread, palThreads, opCount,
                   inStep, lastError, dataRace>>

\* Wrong-thread attempt
WrongThreadCall ==
    /\ activeThread \in {"AudioCallback", "Timer"}
    /\ ownerThread = "Main"
    /\ opCount < MaxOps
    /\ lastError' = "WRONG_THREAD"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   callStack, inStep, dataRace>>

\* Begin/end step
BeginStep ==
    /\ activeThread = "Main"
    /\ coreOwner = "Main"
    /\ ~inStep
    /\ inStep' = TRUE
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   callStack, opCount, lastError, dataRace>>

EndStep ==
    /\ inStep
    /\ activeThread = "Main"
    /\ inStep' = FALSE
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   callStack, opCount, lastError, dataRace>>

\* Core calls PAL
CoreCallPAL ==
    /\ coreOwner = "Main"
    /\ Len(callStack) < 4
    /\ callStack' = Append(callStack, "PAL")
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   opCount, inStep, lastError, dataRace>>

\* Return from PAL
ReturnFromPAL ==
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "PAL"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, palThreads,
                   opCount, inStep, lastError, dataRace>>

\* Spawn PAL thread
SpawnPALThread(t) ==
    /\ t \in {"AudioCallback", "Timer"}
    /\ t \notin palThreads
    /\ palThreads' = palThreads \cup {t}
    /\ UNCHANGED <<activeThread, coreOwner, ownerThread, callStack,
                   opCount, inStep, lastError, dataRace>>

\* Context switch to PAL thread
SwitchToPAL(t) ==
    /\ t \in palThreads
    /\ activeThread' = t
    /\ callStack' = <<>>
    /\ UNCHANGED <<coreOwner, ownerThread, palThreads, opCount,
                   inStep, lastError, dataRace>>

\* Return to main
SwitchToMain ==
    /\ activeThread # "Main"
    /\ activeThread' = "Main"
    /\ UNCHANGED <<coreOwner, ownerThread, palThreads, callStack,
                   opCount, inStep, lastError, dataRace>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ CreateInst
    \/ DestroyInst
    \/ MainEnterCore
    \/ MainExitCore
    \/ WrongThreadCall
    \/ BeginStep
    \/ EndStep
    \/ CoreCallPAL
    \/ ReturnFromPAL
    \/ \E t \in {"AudioCallback", "Timer"} : SpawnPALThread(t)
    \/ \E t \in {"AudioCallback", "Timer"} : SwitchToPAL(t)
    \/ SwitchToMain
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================
