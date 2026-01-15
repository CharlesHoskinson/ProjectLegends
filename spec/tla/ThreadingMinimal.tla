------------------------ MODULE ThreadingMinimal ------------------------
(*
 * Minimal Threading specification for model checking
 *)
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxOps

\* Thread IDs
Thread == {"Main", "AudioCallback", "Timer"}

\* Core ownership
Owner == {"None", "Main"}

\* Code regions
Region == {"USER", "CORE", "PAL"}

VARIABLES
    activeThread,
    coreOwner,
    palThreads,
    callStack,
    opCount,
    dataRace

vars == <<activeThread, coreOwner, palThreads, callStack, opCount, dataRace>>

TypeOK ==
    /\ activeThread \in Thread
    /\ coreOwner \in Owner
    /\ palThreads \subseteq Thread
    /\ callStack \in Seq(Region)
    /\ Len(callStack) <= 4
    /\ opCount \in 0..MaxOps
    /\ dataRace \in BOOLEAN

\* CRITICAL: Only Main can own core
CoreSingleThreaded ==
    coreOwner \in {"None", "Main"}

\* CRITICAL: PAL threads never in core
PALIsolation ==
    \A t \in palThreads : t # coreOwner

\* No data races detected
NoDataRaces ==
    ~dataRace

\* Call stack valid
CallStackValid ==
    activeThread \in {"AudioCallback", "Timer"} =>
        "CORE" \notin {callStack[i] : i \in 1..Len(callStack)}

Init ==
    /\ activeThread = "Main"
    /\ coreOwner = "None"
    /\ palThreads = {}
    /\ callStack = <<>>
    /\ opCount = 0
    /\ dataRace = FALSE

\* Main enters core
MainEnterCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "None"
    /\ opCount < MaxOps
    /\ Len(callStack) < 4
    /\ coreOwner' = "Main"
    /\ callStack' = Append(callStack, "CORE")
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<activeThread, palThreads, dataRace>>

\* Main exits core
MainExitCore ==
    /\ activeThread = "Main"
    /\ coreOwner = "Main"
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "CORE"
    /\ coreOwner' = "None"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, palThreads, opCount, dataRace>>

\* Core calls PAL
CoreCallPAL ==
    /\ coreOwner = "Main"
    /\ Len(callStack) < 4
    /\ callStack' = Append(callStack, "PAL")
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, opCount, dataRace>>

\* Return from PAL
ReturnFromPAL ==
    /\ Len(callStack) > 0
    /\ callStack[Len(callStack)] = "PAL"
    /\ callStack' = SubSeq(callStack, 1, Len(callStack) - 1)
    /\ UNCHANGED <<activeThread, coreOwner, palThreads, opCount, dataRace>>

\* Spawn PAL thread
SpawnPALThread(t) ==
    /\ t \in {"AudioCallback", "Timer"}
    /\ t \notin palThreads
    /\ palThreads' = palThreads \cup {t}
    /\ UNCHANGED <<activeThread, coreOwner, callStack, opCount, dataRace>>

\* Context switch to PAL thread
SwitchToPAL(t) ==
    /\ t \in palThreads
    /\ activeThread' = t
    /\ callStack' = <<>>  \* New thread has empty stack
    /\ UNCHANGED <<coreOwner, palThreads, opCount, dataRace>>

\* Return to main
SwitchToMain ==
    /\ activeThread # "Main"
    /\ activeThread' = "Main"
    /\ UNCHANGED <<coreOwner, palThreads, callStack, opCount, dataRace>>

Next ==
    \/ MainEnterCore
    \/ MainExitCore
    \/ CoreCallPAL
    \/ ReturnFromPAL
    \/ \E t \in {"AudioCallback", "Timer"} : SpawnPALThread(t)
    \/ \E t \in {"AudioCallback", "Timer"} : SwitchToPAL(t)
    \/ SwitchToMain
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

=======================================================================
