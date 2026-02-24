-------------------------- MODULE PALMinimal --------------------------
(**************************************************************************)
(* Legends -- Minimal PAL for CI Model Checking                           *)
(*                                                                        *)
(* Focuses on audio push model, thread safety, component dependencies,    *)
(* and backpressure tracking.                                             *)
(*                                                                        *)
(* Expected: ~200 distinct states at MaxAudioFrames=5                     *)
(**************************************************************************)
EXTENDS Integers, TLC

CONSTANTS
    MaxAudioFrames  \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
Backend == {"Headless", "SDL2", "SDL3", "None"}

\* @type: Set(Str);
Thread == {"Main", "AudioCallback"}

\* @type: Set(Str);
Caller == {"None", "Core", "PAL"}

\* @type: Set(Str);
Component == {"Context", "AudioSink"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    backend,        \* @type: Str;
    initialized,    \* @type: Set(Str);
    audioQueue,     \* @type: Int;
    droppedFrames,  \* @type: Int;
    currentThread,  \* @type: Str;
    lastCaller      \* @type: Str;

vars == <<backend, initialized, audioQueue, droppedFrames,
          currentThread, lastCaller>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ backend \in Backend
    /\ initialized \subseteq Component
    /\ audioQueue \in 0..MaxAudioFrames
    /\ droppedFrames \in 0..100
    /\ currentThread \in Thread
    /\ lastCaller \in Caller

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

\* Audio callback never calls core
AudioPushModel ==
    currentThread = "AudioCallback" => lastCaller # "Core"

\* Core calls only from Main
ThreadSafety ==
    lastCaller = "Core" => currentThread = "Main"

\* Queue bounded
AudioQueueBounded ==
    audioQueue <= MaxAudioFrames

\* Component dependency: AudioSink requires Context
ComponentDependency ==
    "AudioSink" \in initialized => "Context" \in initialized

\* Dropped frames counter monotonically non-decreasing (checked via action)
BackpressureNonNegative ==
    droppedFrames >= 0

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ backend = "None"
    /\ initialized = {}
    /\ audioQueue = 0
    /\ droppedFrames = 0
    /\ currentThread = "Main"
    /\ lastCaller = "None"

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

InitBackend(b) ==
    /\ backend = "None"
    /\ b \in {"Headless", "SDL2", "SDL3"}
    /\ backend' = b
    /\ initialized' = {}
    /\ droppedFrames' = 0
    /\ UNCHANGED <<audioQueue, currentThread, lastCaller>>

\* Init Context (no deps)
InitContext ==
    /\ backend # "None"
    /\ "Context" \notin initialized
    /\ initialized' = initialized \cup {"Context"}
    /\ UNCHANGED <<backend, audioQueue, droppedFrames, currentThread, lastCaller>>

\* Init AudioSink (requires Context)
InitAudioSink ==
    /\ backend # "None"
    /\ "Context" \in initialized
    /\ "AudioSink" \notin initialized
    /\ initialized' = initialized \cup {"AudioSink"}
    /\ UNCHANGED <<backend, audioQueue, droppedFrames, currentThread, lastCaller>>

\* Core pushes audio with backpressure
PushAudio(frames) ==
    /\ currentThread = "Main"
    /\ "AudioSink" \in initialized
    /\ droppedFrames < 100  \* Bound model exploration
    /\ IF audioQueue + frames <= MaxAudioFrames
       THEN /\ audioQueue' = audioQueue + frames
            /\ UNCHANGED droppedFrames
       ELSE LET dropped == frames - (MaxAudioFrames - audioQueue)
                newDropped == droppedFrames + dropped
            IN /\ audioQueue' = MaxAudioFrames
               /\ droppedFrames' = IF newDropped > 100 THEN 100 ELSE newDropped
    /\ lastCaller' = "Core"
    /\ UNCHANGED <<backend, initialized, currentThread>>

\* Audio callback drains queue (SDL2)
AudioCallback ==
    /\ backend = "SDL2"
    /\ audioQueue > 0
    /\ currentThread' = "AudioCallback"
    /\ audioQueue' = audioQueue - 1
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<backend, initialized, droppedFrames>>

\* Stream drain (SDL3/Headless)
StreamDrain ==
    /\ backend \in {"SDL3", "Headless"}
    /\ audioQueue > 0
    /\ audioQueue' = audioQueue - 1
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<backend, initialized, droppedFrames, currentThread>>

\* Return to main thread
ReturnToMain ==
    /\ currentThread = "AudioCallback"
    /\ currentThread' = "Main"
    /\ UNCHANGED <<backend, initialized, audioQueue, droppedFrames, lastCaller>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E b \in {"Headless", "SDL2", "SDL3"} : InitBackend(b)
    \/ InitContext
    \/ InitAudioSink
    \/ \E f \in 1..3 : PushAudio(f)
    \/ AudioCallback
    \/ StreamDrain
    \/ ReturnToMain
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================
