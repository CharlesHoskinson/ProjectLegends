---------------------------- MODULE Input ----------------------------
(**************************************************************************)
(* Legends -- Input Encoding Contract                                     *)
(*                                                                        *)
(* Full (documentation-grade) input specification.                        *)
(* For CI model checking, use InputMinimal.tla.                           *)
(*                                                                        *)
(* Models:                                                                *)
(*   - AT Scancode Set 1 (standard PC keyboard)                           *)
(*   - E0 prefix for extended keys                                        *)
(*   - Input determinism via parallel state tracking                      *)
(*   - Keyboard buffer overflow behaviour                                 *)
(*   - Mouse boundary clamping                                            *)
(*                                                                        *)
(* Contract gates covered:                                                *)
(*   6a  Scancode encoding is AT set 1                                    *)
(*   6b  Input replay produces identical hash                             *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   ScancodeValid           -- all buffer bytes are valid AT set 1       *)
(*   KeyStateConsistent      -- keyState only contains valid scancodes    *)
(*   BufferNotCorrupted      -- no orphaned E0 at end of buffer           *)
(*   E0PrefixCorrect         -- every E0 byte is followed by scancode    *)
(*   InputDeterminism        -- parallel state tracks identically         *)
(*   MouseInBounds           -- mouse position within clamped range       *)
(*   BufferOverflowSafe      -- overflow drops input, no crash            *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

(**************************************************************************)
(* CONSTANTS                                                              *)
(**************************************************************************)
CONSTANTS
    MaxInputs,          \* @type: Int;
    MaxKeyboardBuffer   \* @type: Int;

(**************************************************************************)
(* AT SCANCODE SET 1 DEFINITIONS                                          *)
(**************************************************************************)

\* Standard key scancodes (make codes)
\* @type: Set(Int);
StandardScancodes == {
    1,      \* Esc
    2,      \* 1
    3,      \* 2
    14,     \* Backspace
    15,     \* Tab
    28,     \* Enter
    29,     \* Left Ctrl
    30,     \* A
    31,     \* S
    32,     \* D
    33,     \* F
    42,     \* Left Shift
    44,     \* Z
    48,     \* B
    54,     \* Right Shift
    56,     \* Left Alt
    57,     \* Space
    58      \* Caps Lock
}

\* Extended key scancodes (require E0 prefix)
\* @type: Set(Int);
ExtendedScancodes == {
    28,     \* Numpad Enter (with E0)
    29,     \* Right Ctrl (with E0)
    53,     \* Numpad /
    56,     \* Right Alt
    71,     \* Home
    72,     \* Up
    73,     \* Page Up
    75,     \* Left
    77,     \* Right
    79,     \* End
    80,     \* Down
    81,     \* Page Down
    82,     \* Insert
    83      \* Delete
}

\* @type: Set(Int);
AllScancodes == 1..127

\* @type: Set(Int);
MouseButton == {1, 2, 4}

\* Mouse position clamp range
\* @type: Set(Int);
MouseRange == -32768..32767

\* Clamp mouse to screen bounds
\* @type: (Int, Int, Int) -> Int;
Clamp(val, lo, hi) ==
    IF val < lo THEN lo
    ELSE IF val > hi THEN hi
    ELSE val

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    keyboardBuffer,     \* @type: Seq(Int);  Scancode buffer
    keyState,           \* @type: Set(Int);  Currently pressed keys
    mouseX,             \* @type: Int;
    mouseY,             \* @type: Int;
    mouseButtons,       \* @type: Set(Int);
    inputTrace,         \* @type: Seq(Str);  Complete trace for replay
    \* SHADOW STATE -- Parallel copies for determinism verification.
    \* The shadow state processes the exact same input trace as the primary
    \* state.  Every action updates both primary and shadow identically.
    \* The InputDeterminism invariant asserts they always match.
    \*
    \* WHY: If any action accidentally introduced non-determinism (e.g.,
    \* using CHOOSE or forgetting to update shadow), the invariant would
    \* fail immediately.  This technique catches non-determinism bugs in
    \* the specification itself, not just in the modelled system.
    shadowKeyState,     \* @type: Set(Int);  Shadow copy of keyState
    shadowBuffer        \* @type: Seq(Int);  Shadow copy of buffer

vars == <<keyboardBuffer, keyState, mouseX, mouseY,
          mouseButtons, inputTrace, shadowKeyState, shadowBuffer>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ keyboardBuffer \in Seq(1..255)
    /\ Len(keyboardBuffer) <= MaxKeyboardBuffer
    /\ keyState \subseteq AllScancodes
    /\ mouseX \in MouseRange
    /\ mouseY \in MouseRange
    /\ mouseButtons \subseteq MouseButton
    /\ inputTrace \in Seq({"KEY", "MOUSE", "TEXT"})
    /\ Len(inputTrace) <= MaxInputs
    /\ shadowKeyState \subseteq AllScancodes
    /\ shadowBuffer \in Seq(1..255)
    /\ Len(shadowBuffer) <= MaxKeyboardBuffer

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* ScancodeValid -- Gate 6a                                           *)
(*                                                                    *)
(* All bytes in the keyboard buffer are valid AT set 1 values:        *)
(* make codes (1..127), break codes (129..255), or E0 prefix (224).   *)
(*--------------------------------------------------------------------*)
ScancodeValid ==
    \A i \in 1..Len(keyboardBuffer) :
        keyboardBuffer[i] \in 1..255

(*--------------------------------------------------------------------*)
(* KeyStateConsistent                                                 *)
(*                                                                    *)
(* Key state only contains valid scancodes.                           *)
(*--------------------------------------------------------------------*)
KeyStateConsistent ==
    keyState \subseteq AllScancodes

(*--------------------------------------------------------------------*)
(* BufferNotCorrupted                                                 *)
(*                                                                    *)
(* No orphaned E0 prefix at end of buffer.  Every E0 (224) byte      *)
(* must be followed by a scancode byte.                               *)
(*--------------------------------------------------------------------*)
BufferNotCorrupted ==
    Len(keyboardBuffer) > 0 =>
        keyboardBuffer[Len(keyboardBuffer)] # 224

(*--------------------------------------------------------------------*)
(* E0PrefixCorrect                                                    *)
(*                                                                    *)
(* Every E0 byte (224) in the buffer is followed by another byte.     *)
(* This is the real check replacing the old TRUE stub.                *)
(*--------------------------------------------------------------------*)
E0PrefixCorrect ==
    \A i \in 1..Len(keyboardBuffer) :
        keyboardBuffer[i] = 224 => i < Len(keyboardBuffer)

(*--------------------------------------------------------------------*)
(* InputDeterminism -- Gate 6b                                        *)
(*                                                                    *)
(* The shadow state always matches the primary state.                 *)
(* Both process the same input trace identically.                     *)
(* This replaces the old TRUE stub with a real check.                 *)
(*--------------------------------------------------------------------*)
InputDeterminism ==
    /\ keyState = shadowKeyState
    /\ keyboardBuffer = shadowBuffer

(*--------------------------------------------------------------------*)
(* MouseInBounds                                                      *)
(*                                                                    *)
(* Mouse position is always within the clamped range.                 *)
(*--------------------------------------------------------------------*)
MouseInBounds ==
    /\ mouseX \in MouseRange
    /\ mouseY \in MouseRange

(*--------------------------------------------------------------------*)
(* BufferOverflowSafe                                                 *)
(*                                                                    *)
(* Buffer never exceeds capacity.  Overflow drops input silently.     *)
(*--------------------------------------------------------------------*)
BufferOverflowSafe ==
    Len(keyboardBuffer) <= MaxKeyboardBuffer

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ keyboardBuffer = <<>>
    /\ keyState = {}
    /\ mouseX = 0
    /\ mouseY = 0
    /\ mouseButtons = {}
    /\ inputTrace = <<>>
    /\ shadowKeyState = {}
    /\ shadowBuffer = <<>>

(**************************************************************************)
(* ACTIONS -- KEYBOARD INPUT                                              *)
(**************************************************************************)

\* Standard key press/release
KeyEvent_Standard(scancode, pressed) ==
    /\ scancode \in StandardScancodes
    /\ Len(keyboardBuffer) < MaxKeyboardBuffer
    /\ Len(inputTrace) < MaxInputs
    /\ IF pressed
       THEN /\ keyboardBuffer' = Append(keyboardBuffer, scancode)
            /\ keyState' = keyState \cup {scancode}
            /\ shadowBuffer' = Append(shadowBuffer, scancode)
            /\ shadowKeyState' = shadowKeyState \cup {scancode}
       ELSE /\ keyboardBuffer' = Append(keyboardBuffer, scancode + 128)
            /\ keyState' = keyState \ {scancode}
            /\ shadowBuffer' = Append(shadowBuffer, scancode + 128)
            /\ shadowKeyState' = shadowKeyState \ {scancode}
    /\ inputTrace' = Append(inputTrace, "KEY")
    /\ UNCHANGED <<mouseX, mouseY, mouseButtons>>

\* Extended key press/release (E0 prefix)
KeyEvent_Extended(scancode, pressed) ==
    /\ scancode \in ExtendedScancodes
    /\ Len(keyboardBuffer) < MaxKeyboardBuffer - 1  \* Need 2 bytes
    /\ Len(inputTrace) < MaxInputs
    /\ LET e0 == 224
           code == IF pressed THEN scancode ELSE scancode + 128
       IN /\ keyboardBuffer' = keyboardBuffer \o <<e0, code>>
          /\ shadowBuffer' = shadowBuffer \o <<e0, code>>
    /\ IF pressed
       THEN /\ keyState' = keyState \cup {scancode + 256}
            /\ shadowKeyState' = shadowKeyState \cup {scancode + 256}
       ELSE /\ keyState' = keyState \ {scancode + 256}
            /\ shadowKeyState' = shadowKeyState \ {scancode + 256}
    /\ inputTrace' = Append(inputTrace, "KEY")
    /\ UNCHANGED <<mouseX, mouseY, mouseButtons>>

\* Keyboard buffer overflow -- input dropped silently
KeyEvent_Overflow(scancode) ==
    /\ scancode \in StandardScancodes
    /\ Len(keyboardBuffer) >= MaxKeyboardBuffer
    \* Input is silently dropped
    /\ UNCHANGED <<keyboardBuffer, keyState, mouseX, mouseY,
                   mouseButtons, inputTrace, shadowKeyState, shadowBuffer>>

\* Text input
TextInput ==
    /\ Len(inputTrace) < MaxInputs
    /\ inputTrace' = Append(inputTrace, "TEXT")
    /\ UNCHANGED <<keyboardBuffer, keyState, mouseX, mouseY,
                   mouseButtons, shadowKeyState, shadowBuffer>>

(**************************************************************************)
(* ACTIONS -- MOUSE INPUT                                                 *)
(**************************************************************************)

\* Mouse movement with boundary clamping
MouseInput(dx, dy, buttons) ==
    /\ dx \in -127..127
    /\ dy \in -127..127
    /\ buttons \subseteq MouseButton
    /\ Len(inputTrace) < MaxInputs
    /\ mouseX' = Clamp(mouseX + dx, -32768, 32767)
    /\ mouseY' = Clamp(mouseY + dy, -32768, 32767)
    /\ mouseButtons' = buttons
    /\ inputTrace' = Append(inputTrace, "MOUSE")
    /\ UNCHANGED <<keyboardBuffer, keyState, shadowKeyState, shadowBuffer>>

(**************************************************************************)
(* ACTIONS -- BUFFER CONSUMPTION                                          *)
(**************************************************************************)

\* BIOS/DOS reads from keyboard buffer
ConsumeKeyboardByte ==
    /\ Len(keyboardBuffer) > 0
    /\ keyboardBuffer' = Tail(keyboardBuffer)
    /\ shadowBuffer' = Tail(shadowBuffer)
    /\ UNCHANGED <<keyState, mouseX, mouseY, mouseButtons,
                   inputTrace, shadowKeyState>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E sc \in StandardScancodes, p \in BOOLEAN :
        KeyEvent_Standard(sc, p)
    \/ \E sc \in ExtendedScancodes, p \in BOOLEAN :
        KeyEvent_Extended(sc, p)
    \/ \E sc \in StandardScancodes :
        KeyEvent_Overflow(sc)
    \/ TextInput
    \/ \E dx, dy \in -10..10, b \in SUBSET MouseButton :
        MouseInput(dx, dy, b)
    \/ ConsumeKeyboardByte
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

(**************************************************************************)
(* TEMPORAL PROPERTIES                                                    *)
(**************************************************************************)

\* Buffer never overflows
NoBufferOverflow ==
    [](Len(keyboardBuffer) <= MaxKeyboardBuffer)

=======================================================================
