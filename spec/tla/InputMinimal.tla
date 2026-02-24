-------------------------- MODULE InputMinimal --------------------------
(**************************************************************************)
(* Legends -- Minimal Input for CI Model Checking                         *)
(*                                                                        *)
(* Reduces scancode sets and buffer size for tractable state space.        *)
(* Verifies E0 prefix correctness, input determinism (parallel state),    *)
(* and buffer overflow safety.                                            *)
(*                                                                        *)
(* Expected: ~300 distinct states with 1 worker                           *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxInputs,          \* @type: Int;
    MaxKeyboardBuffer   \* @type: Int;

(**************************************************************************)
(* TYPES (reduced)                                                        *)
(**************************************************************************)

\* Reduced scancode sets for tractability
\* @type: Set(Int);
StdScancodes == {30, 31, 57}   \* A, S, Space

\* @type: Set(Int);
ExtScancodes == {72, 80}       \* Up, Down

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    keyboardBuffer,     \* @type: Seq(Int);
    keyState,           \* @type: Set(Int);
    shadowKeyState,     \* @type: Set(Int);  Parallel state
    shadowBuffer,       \* @type: Seq(Int);  Parallel buffer
    opCount             \* @type: Int;

vars == <<keyboardBuffer, keyState, shadowKeyState, shadowBuffer, opCount>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ keyboardBuffer \in Seq(1..255)
    /\ Len(keyboardBuffer) <= MaxKeyboardBuffer
    /\ keyState \subseteq 1..383  \* 1..127 standard + 257..383 extended
    /\ shadowKeyState \subseteq 1..383
    /\ shadowBuffer \in Seq(1..255)
    /\ Len(shadowBuffer) <= MaxKeyboardBuffer
    /\ opCount \in 0..MaxInputs

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

\* All buffer bytes are valid
ScancodeValid ==
    \A i \in 1..Len(keyboardBuffer) :
        keyboardBuffer[i] \in 1..255

\* No orphaned E0 at end of buffer
BufferNotCorrupted ==
    Len(keyboardBuffer) > 0 =>
        keyboardBuffer[Len(keyboardBuffer)] # 224

\* Every E0 byte has a following byte
E0PrefixCorrect ==
    \A i \in 1..Len(keyboardBuffer) :
        keyboardBuffer[i] = 224 => i < Len(keyboardBuffer)

\* Parallel state matches primary (input determinism)
InputDeterminism ==
    /\ keyState = shadowKeyState
    /\ keyboardBuffer = shadowBuffer

\* Buffer never exceeds capacity
BufferBounded ==
    Len(keyboardBuffer) <= MaxKeyboardBuffer

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ keyboardBuffer = <<>>
    /\ keyState = {}
    /\ shadowKeyState = {}
    /\ shadowBuffer = <<>>
    /\ opCount = 0

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

\* Standard key press
StdKeyPress(sc) ==
    /\ sc \in StdScancodes
    /\ Len(keyboardBuffer) < MaxKeyboardBuffer
    /\ opCount < MaxInputs
    /\ keyboardBuffer' = Append(keyboardBuffer, sc)
    /\ keyState' = keyState \cup {sc}
    /\ shadowBuffer' = Append(shadowBuffer, sc)
    /\ shadowKeyState' = shadowKeyState \cup {sc}
    /\ opCount' = opCount + 1

\* Standard key release
StdKeyRelease(sc) ==
    /\ sc \in StdScancodes
    /\ sc \in keyState
    /\ Len(keyboardBuffer) < MaxKeyboardBuffer
    /\ opCount < MaxInputs
    /\ keyboardBuffer' = Append(keyboardBuffer, sc + 128)
    /\ keyState' = keyState \ {sc}
    /\ shadowBuffer' = Append(shadowBuffer, sc + 128)
    /\ shadowKeyState' = shadowKeyState \ {sc}
    /\ opCount' = opCount + 1

\* Extended key press (E0 + scancode)
ExtKeyPress(sc) ==
    /\ sc \in ExtScancodes
    /\ Len(keyboardBuffer) < MaxKeyboardBuffer - 1
    /\ opCount < MaxInputs
    /\ keyboardBuffer' = keyboardBuffer \o <<224, sc>>
    /\ keyState' = keyState \cup {sc + 256}
    /\ shadowBuffer' = shadowBuffer \o <<224, sc>>
    /\ shadowKeyState' = shadowKeyState \cup {sc + 256}
    /\ opCount' = opCount + 1

\* Extended key release
ExtKeyRelease(sc) ==
    /\ sc \in ExtScancodes
    /\ (sc + 256) \in keyState
    /\ Len(keyboardBuffer) < MaxKeyboardBuffer - 1
    /\ opCount < MaxInputs
    /\ keyboardBuffer' = keyboardBuffer \o <<224, sc + 128>>
    /\ keyState' = keyState \ {sc + 256}
    /\ shadowBuffer' = shadowBuffer \o <<224, sc + 128>>
    /\ shadowKeyState' = shadowKeyState \ {sc + 256}
    /\ opCount' = opCount + 1

\* Buffer consumption
ConsumeByte ==
    /\ Len(keyboardBuffer) > 0
    /\ keyboardBuffer' = Tail(keyboardBuffer)
    /\ shadowBuffer' = Tail(shadowBuffer)
    /\ UNCHANGED <<keyState, shadowKeyState, opCount>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E sc \in StdScancodes : StdKeyPress(sc)
    \/ \E sc \in StdScancodes : StdKeyRelease(sc)
    \/ \E sc \in ExtScancodes : ExtKeyPress(sc)
    \/ \E sc \in ExtScancodes : ExtKeyRelease(sc)
    \/ ConsumeByte
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================
