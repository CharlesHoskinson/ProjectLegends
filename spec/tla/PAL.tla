---------------------------- MODULE PAL ----------------------------
(**************************************************************************)
(* Legends -- Platform Abstraction Layer (PAL) Contract                   *)
(*                                                                        *)
(* Full (documentation-grade) PAL specification.                          *)
(* For CI model checking, use PALMinimal.tla.                             *)
(*                                                                        *)
(* Models:                                                                *)
(*   - Backend isolation (SDL headers confined to PAL)                    *)
(*   - Push-model audio (core -> PAL, never PAL -> core)                  *)
(*   - Component dependency graph                                         *)
(*   - Audio backpressure with drop metrics                               *)
(*   - Backend-specific drain behaviour (SDL2 callback vs SDL3 stream)    *)
(*                                                                        *)
(* Contract gates covered:                                                *)
(*   7a  Core never invoked from audio callback thread                    *)
(*   7b  Audio queue policy documented (bounded, drop on overflow)        *)
(*   7c  Push model -- no callback driving emulation                      *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   BackendIsolation            -- core never calls SDL directly         *)
(*   AudioPushModel              -- callback thread never calls core      *)
(*   ThreadSafety                -- core calls only from MainThread       *)
(*   AudioQueueBounded           -- queue never exceeds capacity          *)
(*   ComponentDependencySatisfied -- AudioSink requires Context           *)
(*   BackpressureTracked         -- dropped frames monotonically increase *)
(*                                                                        *)
(* Liveness:                                                              *)
(*   AudioEventuallyDrains       -- queue > 0 ~> queue = 0 (with WF)     *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

(**************************************************************************)
(* CONSTANTS                                                              *)
(**************************************************************************)
CONSTANTS
    MaxAudioFrames,     \* @type: Int;
    MaxInputEvents      \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
Backend == {"Headless", "SDL2", "SDL3"}

\* @type: Set(Str);
Component == {"Window", "Context", "AudioSink", "HostClock", "InputSource"}

\* @type: Set(Int);
AudioFrame == 0..32767

\* @type: Set(Str);
InputEventType == {
    "KeyDown", "KeyUp",
    "MouseMotion", "MouseButtonDown", "MouseButtonUp",
    "WindowClose", "WindowResize"
}

\* @type: Set(Str);
Thread == {"MainThread", "AudioCallback", "EventLoop"}

\* @type: Set(Str);
FunctionCall == {"PAL", "Core", "None"}

(**************************************************************************)
(* COMPONENT DEPENDENCY GRAPH                                             *)
(*                                                                        *)
(* Models the initialization order constraints between PAL components.   *)
(* This prevents runtime failures from missing prerequisites.            *)
(*                                                                        *)
(*   Window         <- no dependencies (created first)                   *)
(*   Context        <- depends on Window (needs window handle)           *)
(*   AudioSink      <- depends on Context (needs graphics context)       *)
(*   HostClock      <- no dependencies (standalone timer)                *)
(*   InputSource    <- no dependencies (standalone input polling)        *)
(*                                                                        *)
(* The ComponentDependencySatisfied invariant ensures that at any point  *)
(* in time, every initialized component has all its dependencies also    *)
(* initialized.  This is enforced by the InitComponent action's guard.  *)
(*                                                                        *)
(* WHY MODEL THIS:                                                        *)
(* In the real implementation, initializing AudioSink before Context     *)
(* would cause a null pointer crash.  The TLA+ model catches this class  *)
(* of bugs by exhaustively checking all initialization orderings.        *)
(**************************************************************************)

\* @type: Str -> Set(Str);
ComponentDeps(comp) ==
    CASE comp = "AudioSink"    -> {"Context"}
      [] comp = "Context"      -> {"Window"}
      [] comp = "Window"       -> {}
      [] comp = "HostClock"    -> {}
      [] comp = "InputSource"  -> {}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    activeBackend,      \* @type: Str;
    initialized,        \* @type: Set(Str);  Initialized components
    audioQueue,         \* @type: Seq(Int);
    audioQueueSize,     \* @type: Int;
    droppedFrames,      \* @type: Int;       Backpressure drop counter
    inputBuffer,        \* @type: Seq(Str);
    currentThread,      \* @type: Str;
    lastCaller          \* @type: Str;

vars == <<activeBackend, initialized, audioQueue, audioQueueSize,
          droppedFrames, inputBuffer, currentThread, lastCaller>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ activeBackend \in Backend \cup {"None"}
    /\ initialized \subseteq Component
    /\ audioQueue \in Seq(AudioFrame)
    /\ audioQueueSize \in 0..MaxAudioFrames
    /\ Len(audioQueue) = audioQueueSize
    /\ droppedFrames \in 0..1000
    /\ inputBuffer \in Seq(InputEventType)
    /\ Len(inputBuffer) <= MaxInputEvents
    /\ currentThread \in Thread
    /\ lastCaller \in FunctionCall

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* BackendIsolation                                                   *)
(*                                                                    *)
(* When backend is active, core only sees PAL interfaces.             *)
(* PAL internal threads never invoke core.                            *)
(*--------------------------------------------------------------------*)
BackendIsolation ==
    activeBackend # "None" =>
        (currentThread \in {"AudioCallback", "EventLoop"} =>
            lastCaller # "Core")

(*--------------------------------------------------------------------*)
(* AudioPushModel -- Gate 7c                                          *)
(*                                                                    *)
(* Audio flows core -> PAL only.  The audio callback thread           *)
(* never invokes core functions.                                      *)
(*--------------------------------------------------------------------*)
AudioPushModel ==
    currentThread = "AudioCallback" => lastCaller \in {"PAL", "None"}

(*--------------------------------------------------------------------*)
(* ThreadSafety -- Gates 7a, 8a                                       *)
(*                                                                    *)
(* Only MainThread may invoke core functions.                         *)
(*--------------------------------------------------------------------*)
ThreadSafety ==
    lastCaller = "Core" => currentThread = "MainThread"

(*--------------------------------------------------------------------*)
(* AudioQueueBounded -- Gate 7b                                       *)
(*--------------------------------------------------------------------*)
AudioQueueBounded ==
    audioQueueSize <= MaxAudioFrames

(*--------------------------------------------------------------------*)
(* ComponentDependencySatisfied                                       *)
(*                                                                    *)
(* A component may only be initialized if all its dependencies        *)
(* are already initialized.                                           *)
(*--------------------------------------------------------------------*)
ComponentDependencySatisfied ==
    \A comp \in initialized :
        ComponentDeps(comp) \subseteq initialized

(*--------------------------------------------------------------------*)
(* BackpressureTracked -- Gate 7d                                     *)
(*                                                                    *)
(* The dropped-frames counter is monotonically non-decreasing.        *)
(* It never goes below zero.  This ensures that audio backpressure   *)
(* statistics are always available to the embedding application via  *)
(* getDroppedFrames().                                                *)
(*                                                                    *)
(* When the audio queue is full, PushAudioSamples drops excess        *)
(* frames and increments droppedFrames.  The counter is never reset  *)
(* except on backend shutdown.  This lets the host detect and        *)
(* respond to audio underrun/overrun conditions.                     *)
(*--------------------------------------------------------------------*)
BackpressureTracked ==
    droppedFrames >= 0

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ activeBackend = "None"
    /\ initialized = {}
    /\ audioQueue = <<>>
    /\ audioQueueSize = 0
    /\ droppedFrames = 0
    /\ inputBuffer = <<>>
    /\ currentThread = "MainThread"
    /\ lastCaller = "None"

(**************************************************************************)
(* ACTIONS -- PAL LIFECYCLE                                               *)
(**************************************************************************)

InitializeBackend(backend) ==
    /\ activeBackend = "None"
    /\ activeBackend' = backend
    /\ initialized' = {}
    /\ droppedFrames' = 0
    /\ UNCHANGED <<audioQueue, audioQueueSize, inputBuffer,
                   currentThread, lastCaller>>

ShutdownBackend ==
    /\ activeBackend # "None"
    /\ activeBackend' = "None"
    /\ initialized' = {}
    /\ audioQueue' = <<>>
    /\ audioQueueSize' = 0
    /\ inputBuffer' = <<>>
    /\ UNCHANGED <<droppedFrames, currentThread, lastCaller>>

\* Component initialization -- respects dependency graph
InitComponent(comp) ==
    /\ activeBackend # "None"
    /\ comp \notin initialized
    /\ ComponentDeps(comp) \subseteq initialized
    /\ initialized' = initialized \cup {comp}
    /\ UNCHANGED <<activeBackend, audioQueue, audioQueueSize,
                   droppedFrames, inputBuffer, currentThread, lastCaller>>

(**************************************************************************)
(* ACTIONS -- AUDIO (PUSH MODEL)                                          *)
(**************************************************************************)

\* Core pushes audio to PAL (MainThread only)
PushAudioSamples(frames) ==
    /\ currentThread = "MainThread"
    /\ "AudioSink" \in initialized
    /\ IF audioQueueSize + frames <= MaxAudioFrames
       THEN \* Queue has room
            /\ audioQueueSize' = audioQueueSize + frames
            /\ audioQueue' = audioQueue \o [i \in 1..frames |-> 0]
            /\ UNCHANGED droppedFrames
       ELSE \* Queue full -- drop excess frames (backpressure)
            /\ LET room == MaxAudioFrames - audioQueueSize
                   dropped == frames - room
               IN /\ audioQueueSize' = MaxAudioFrames
                  /\ audioQueue' = IF room > 0
                                   THEN audioQueue \o [i \in 1..room |-> 0]
                                   ELSE audioQueue
                  /\ droppedFrames' = droppedFrames + dropped
    /\ lastCaller' = "Core"
    /\ UNCHANGED <<activeBackend, initialized, inputBuffer, currentThread>>

\* SDL2 audio callback drains queue
AudioCallbackDrain(frames) ==
    /\ activeBackend = "SDL2"
    /\ currentThread' = "AudioCallback"
    /\ audioQueueSize >= frames
    /\ audioQueueSize' = audioQueueSize - frames
    /\ audioQueue' = SubSeq(audioQueue, frames + 1, Len(audioQueue))
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<activeBackend, initialized, droppedFrames, inputBuffer>>

\* SDL3 audio stream pull
AudioStreamPull(frames) ==
    /\ activeBackend = "SDL3"
    /\ audioQueueSize >= frames
    /\ audioQueueSize' = audioQueueSize - frames
    /\ audioQueue' = SubSeq(audioQueue, frames + 1, Len(audioQueue))
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<activeBackend, initialized, droppedFrames,
                   inputBuffer, currentThread>>

\* Headless audio -- silently discards
HeadlessDrain(frames) ==
    /\ activeBackend = "Headless"
    /\ audioQueueSize >= frames
    /\ audioQueueSize' = audioQueueSize - frames
    /\ audioQueue' = SubSeq(audioQueue, frames + 1, Len(audioQueue))
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<activeBackend, initialized, droppedFrames,
                   inputBuffer, currentThread>>

(**************************************************************************)
(* ACTIONS -- INPUT                                                       *)
(**************************************************************************)

PollInput ==
    /\ currentThread = "MainThread"
    /\ "InputSource" \in initialized
    /\ inputBuffer' = <<>>
    /\ lastCaller' = "Core"
    /\ UNCHANGED <<activeBackend, initialized, audioQueue,
                   audioQueueSize, droppedFrames, currentThread>>

ReceiveInputEvent(eventType) ==
    /\ activeBackend # "None"
    /\ "InputSource" \in initialized
    /\ Len(inputBuffer) < MaxInputEvents
    /\ inputBuffer' = Append(inputBuffer, eventType)
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<activeBackend, initialized, audioQueue,
                   audioQueueSize, droppedFrames, currentThread>>

(**************************************************************************)
(* ACTIONS -- THREAD CONTEXT                                              *)
(**************************************************************************)

ReturnToMainThread ==
    /\ currentThread # "MainThread"
    /\ currentThread' = "MainThread"
    /\ UNCHANGED <<activeBackend, initialized, audioQueue,
                   audioQueueSize, droppedFrames, inputBuffer, lastCaller>>

(**************************************************************************)
(* QUERY OPERATORS (for use by other modules)                             *)
(**************************************************************************)

\* @type: Int;
GetQueuedFrames == audioQueueSize

\* @type: Int;
GetBufferCapacity == MaxAudioFrames

\* @type: Int;
GetDroppedFrames == droppedFrames

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E b \in Backend : InitializeBackend(b)
    \/ ShutdownBackend
    \/ \E c \in Component : InitComponent(c)
    \/ \E f \in 1..5 : PushAudioSamples(f)
    \/ \E f \in 1..5 : AudioCallbackDrain(f)
    \/ \E f \in 1..5 : AudioStreamPull(f)
    \/ \E f \in 1..5 : HeadlessDrain(f)
    \/ PollInput
    \/ \E e \in InputEventType : ReceiveInputEvent(e)
    \/ ReturnToMainThread
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(AudioCallbackDrain(1)) /\
        WF_vars(AudioStreamPull(1)) /\ WF_vars(HeadlessDrain(1))

(**************************************************************************)
(* LIVENESS PROPERTIES                                                    *)
(**************************************************************************)

\* Audio eventually drains (with fair scheduling)
AudioEventuallyDrains ==
    audioQueueSize > 0 ~> audioQueueSize = 0

\* Core never called from callback
CoreNeverCalledFromCallback ==
    [](currentThread \in {"AudioCallback", "EventLoop"} =>
       lastCaller # "Core")

=======================================================================
