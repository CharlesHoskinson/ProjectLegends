---------------------------- MODULE PAL ----------------------------
(*
 * Legends - Platform Abstraction Layer (PAL) Contract
 *
 * This module specifies the PAL interfaces and invariants:
 * - Backend isolation (SDL headers only in PAL)
 * - Push-model audio (no callbacks into core)
 * - Threading model (PAL threads never call core)
 *
 * Key invariants:
 * - BackendIsolation: Core never directly calls SDL
 * - AudioPushModel: Audio flows core -> PAL, never PAL -> core
 * - ThreadSafety: PAL threads never invoke core functions
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    MaxAudioFrames,     \* Maximum audio frames in queue
    MaxInputEvents      \* Maximum input events buffered

\* =====================================================================
\* TYPES
\* =====================================================================

\* PAL backends
Backend == {"Headless", "SDL2", "SDL3"}

\* PAL components
Component == {"Window", "Context", "AudioSink", "HostClock", "InputSource"}

\* Audio sample (simplified)
AudioFrame == 0..32767  \* 16-bit PCM range

\* Input event types
InputEventType == {
    "KeyDown", "KeyUp",
    "MouseMotion", "MouseButtonDown", "MouseButtonUp",
    "WindowClose", "WindowResize"
}

\* Thread identifiers
Thread == {"MainThread", "AudioCallback", "EventLoop"}

\* Function call types
FunctionCall == {"PAL", "Core", "None"}

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    activeBackend,      \* Currently active backend
    initialized,        \* Set of initialized components
    audioQueue,         \* Audio frame queue (sequence)
    audioQueueSize,     \* Current queue size
    inputBuffer,        \* Input event buffer
    currentThread,      \* Current executing thread
    lastCaller          \* What called core last

vars == <<activeBackend, initialized, audioQueue, audioQueueSize,
          inputBuffer, currentThread, lastCaller>>

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

TypeOK ==
    /\ activeBackend \in Backend \cup {"None"}
    /\ initialized \subseteq Component
    /\ audioQueue \in Seq(AudioFrame)
    /\ audioQueueSize \in 0..MaxAudioFrames
    /\ Len(audioQueue) = audioQueueSize
    /\ inputBuffer \in Seq(InputEventType)
    /\ Len(inputBuffer) <= MaxInputEvents
    /\ currentThread \in Thread
    /\ lastCaller \in FunctionCall

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

(*
 * BackendIsolation - Core code never directly calls SDL
 *
 * All platform interaction goes through PAL interfaces.
 * SDL symbols are not visible to core code.
 *)
BackendIsolation ==
    \* When backend is active, core only sees PAL interfaces
    activeBackend # "None" =>
        \* Core functions never called from PAL internal threads
        (currentThread \in {"AudioCallback", "EventLoop"} =>
            lastCaller # "Core")

(*
 * AudioPushModel - Audio flows from core to PAL only
 *
 * Core pushes samples to IAudioSink.
 * PAL drains samples to device.
 * PAL never calls back into core for audio.
 *)
AudioPushModel ==
    \* Audio callback thread never invokes core
    currentThread = "AudioCallback" => lastCaller \in {"PAL", "None"}

(*
 * ThreadSafety - PAL threads never call core functions
 *
 * Only MainThread may call core functions.
 * AudioCallback and EventLoop are PAL-internal.
 *)
ThreadSafety ==
    lastCaller = "Core" => currentThread = "MainThread"

(*
 * AudioQueueBounded - Queue never exceeds capacity
 *)
AudioQueueBounded ==
    audioQueueSize <= MaxAudioFrames

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

Init ==
    /\ activeBackend = "None"
    /\ initialized = {}
    /\ audioQueue = <<>>
    /\ audioQueueSize = 0
    /\ inputBuffer = <<>>
    /\ currentThread = "MainThread"
    /\ lastCaller = "None"

\* =====================================================================
\* ACTIONS - PAL LIFECYCLE
\* =====================================================================

(*
 * pal::Platform::initialize(backend)
 *
 * Initialize the platform with specified backend.
 *)
InitializeBackend(backend) ==
    /\ activeBackend = "None"
    /\ activeBackend' = backend
    /\ initialized' = {}
    /\ UNCHANGED <<audioQueue, audioQueueSize, inputBuffer,
                   currentThread, lastCaller>>

(*
 * pal::Platform::shutdown()
 *
 * Shutdown the platform and release all resources.
 *)
ShutdownBackend ==
    /\ activeBackend # "None"
    /\ activeBackend' = "None"
    /\ initialized' = {}
    /\ audioQueue' = <<>>
    /\ audioQueueSize' = 0
    /\ inputBuffer' = <<>>
    /\ UNCHANGED <<currentThread, lastCaller>>

(*
 * Component initialization
 *)
InitComponent(comp) ==
    /\ activeBackend # "None"
    /\ comp \notin initialized
    /\ initialized' = initialized \cup {comp}
    /\ UNCHANGED <<activeBackend, audioQueue, audioQueueSize,
                   inputBuffer, currentThread, lastCaller>>

\* =====================================================================
\* ACTIONS - AUDIO (PUSH MODEL)
\* =====================================================================

(*
 * IAudioSink::pushSamples() - Core pushes audio to PAL
 *
 * Called from MainThread only.
 * Adds samples to queue for playback.
 *)
PushAudioSamples(frames) ==
    /\ currentThread = "MainThread"
    /\ "AudioSink" \in initialized
    /\ audioQueueSize + frames <= MaxAudioFrames
    /\ audioQueueSize' = audioQueueSize + frames
    \* Simplified: just track count, not actual samples
    /\ audioQueue' = audioQueue \o [i \in 1..frames |-> 0]
    /\ lastCaller' = "Core"
    /\ UNCHANGED <<activeBackend, initialized, inputBuffer, currentThread>>

(*
 * Audio callback drains queue - SDL2 backend only
 *
 * This is PAL-internal. Never calls core.
 *)
AudioCallbackDrain(frames) ==
    /\ activeBackend = "SDL2"
    /\ currentThread' = "AudioCallback"
    /\ audioQueueSize >= frames
    /\ audioQueueSize' = audioQueueSize - frames
    /\ audioQueue' = SubSeq(audioQueue, frames + 1, Len(audioQueue))
    /\ lastCaller' = "PAL"  \* PAL internal, never "Core"
    /\ UNCHANGED <<activeBackend, initialized, inputBuffer>>

(*
 * Audio stream pull - SDL3 backend
 *
 * SDL3 uses push model internally, no callbacks.
 *)
AudioStreamPull(frames) ==
    /\ activeBackend = "SDL3"
    /\ audioQueueSize >= frames
    /\ audioQueueSize' = audioQueueSize - frames
    /\ audioQueue' = SubSeq(audioQueue, frames + 1, Len(audioQueue))
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<activeBackend, initialized, inputBuffer, currentThread>>

\* =====================================================================
\* ACTIONS - INPUT
\* =====================================================================

(*
 * IInputSource::poll() - Core polls input from PAL
 *
 * Called from MainThread only.
 * Returns buffered events.
 *)
PollInput ==
    /\ currentThread = "MainThread"
    /\ "InputSource" \in initialized
    /\ inputBuffer' = <<>>  \* Clear buffer after poll
    /\ lastCaller' = "Core"
    /\ UNCHANGED <<activeBackend, initialized, audioQueue,
                   audioQueueSize, currentThread>>

(*
 * Input event arrives from OS (PAL internal)
 *)
ReceiveInputEvent(eventType) ==
    /\ activeBackend # "None"
    /\ "InputSource" \in initialized
    /\ Len(inputBuffer) < MaxInputEvents
    /\ inputBuffer' = Append(inputBuffer, eventType)
    /\ lastCaller' = "PAL"
    /\ UNCHANGED <<activeBackend, initialized, audioQueue,
                   audioQueueSize, currentThread>>

\* =====================================================================
\* ACTIONS - THREAD CONTEXT
\* =====================================================================

(*
 * Return to main thread after callback
 *)
ReturnToMainThread ==
    /\ currentThread # "MainThread"
    /\ currentThread' = "MainThread"
    /\ UNCHANGED <<activeBackend, initialized, audioQueue,
                   audioQueueSize, inputBuffer, lastCaller>>

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================

Next ==
    \/ \E b \in Backend : InitializeBackend(b)
    \/ ShutdownBackend
    \/ \E c \in Component : InitComponent(c)
    \/ \E f \in 1..10 : PushAudioSamples(f)
    \/ \E f \in 1..10 : AudioCallbackDrain(f)
    \/ \E f \in 1..10 : AudioStreamPull(f)
    \/ PollInput
    \/ \E e \in InputEventType : ReceiveInputEvent(e)
    \/ ReturnToMainThread
    \/ UNCHANGED vars

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars

\* =====================================================================
\* PROPERTIES
\* =====================================================================

(*
 * CoreNeverCalledFromCallback - Core isolation guarantee
 *)
CoreNeverCalledFromCallback ==
    [](currentThread \in {"AudioCallback", "EventLoop"} =>
       lastCaller # "Core")

(*
 * AudioNeverStarves - With fair scheduling, audio eventually drains
 *)
AudioDrains ==
    audioQueueSize > 0 ~> audioQueueSize = 0

=======================================================================
