-------------------------- MODULE PALMinimal --------------------------
(*
 * Minimal PAL specification for model checking
 * Focuses on threading invariants
 *)
EXTENDS Integers, TLC

CONSTANTS MaxAudioFrames

\* Backends
Backend == {"Headless", "SDL2", "SDL3", "None"}

\* Threads
Thread == {"Main", "AudioCallback"}

\* Caller types
Caller == {"None", "Core", "PAL"}

VARIABLES
    backend,
    audioQueue,
    currentThread,
    lastCaller

vars == <<backend, audioQueue, currentThread, lastCaller>>

TypeOK ==
    /\ backend \in Backend
    /\ audioQueue \in 0..MaxAudioFrames
    /\ currentThread \in Thread
    /\ lastCaller \in Caller

\* CRITICAL INVARIANT: Audio callback never calls core
AudioPushModel ==
    currentThread = "AudioCallback" => lastCaller # "Core"

\* PAL threads never call core
ThreadSafety ==
    lastCaller = "Core" => currentThread = "Main"

\* Queue bounded
AudioQueueBounded ==
    audioQueue <= MaxAudioFrames

Init ==
    /\ backend = "None"
    /\ audioQueue = 0
    /\ currentThread = "Main"
    /\ lastCaller = "None"

InitBackend(b) ==
    /\ backend = "None"
    /\ backend' = b
    /\ UNCHANGED <<audioQueue, currentThread, lastCaller>>

\* Core pushes audio (Main thread only)
PushAudio(frames) ==
    /\ currentThread = "Main"
    /\ backend # "None"
    /\ audioQueue + frames <= MaxAudioFrames
    /\ audioQueue' = audioQueue + frames
    /\ lastCaller' = "Core"
    /\ UNCHANGED <<backend, currentThread>>

\* Audio callback drains queue (SDL2 only)
AudioCallback ==
    /\ backend = "SDL2"
    /\ audioQueue > 0
    /\ currentThread' = "AudioCallback"
    /\ audioQueue' = audioQueue - 1
    /\ lastCaller' = "PAL"
    /\ UNCHANGED backend

\* Return to main thread
ReturnToMain ==
    /\ currentThread = "AudioCallback"
    /\ currentThread' = "Main"
    /\ UNCHANGED <<backend, audioQueue, lastCaller>>

Next ==
    \/ \E b \in {"Headless", "SDL2", "SDL3"} : InitBackend(b)
    \/ \E f \in 1..3 : PushAudio(f)
    \/ AudioCallback
    \/ ReturnToMain
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

=======================================================================
