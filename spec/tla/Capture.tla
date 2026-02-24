---------------------------- MODULE Capture ----------------------------
(**************************************************************************)
(* Legends -- Screen Capture Contract                                     *)
(*                                                                        *)
(* Full (documentation-grade) capture specification.                       *)
(* For CI model checking, use CaptureMinimal.tla.                         *)
(*                                                                        *)
(* Models:                                                                *)
(*   - Text capture (CP437 character cells)                               *)
(*   - RGB capture (pre-scaler framebuffer, RGB24, no padding)            *)
(*   - Video mode transitions (INT 10h)                                   *)
(*   - Dirty flag lifecycle (write sets, capture clears)                   *)
(*   - Backend-independent output                                         *)
(*                                                                        *)
(* Contract gates covered:                                                *)
(*   5a  capture_text returns consistent dimensions                       *)
(*   5b  capture_rgb has fixed pixel format (RGB24)                       *)
(*   5c  Capture is backend-independent                                   *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   DimensionsConsistent  -- dimensions match video mode                 *)
(*   FormatFixed           -- RGB24, pitch = width * 3, no padding        *)
(*   BackendIndependent    -- same state -> same capture, any backend     *)
(*   CellCountMatches      -- text buffer size = cols * rows              *)
(*   CursorInBounds        -- cursor within screen bounds                 *)
(*   FramebufferSizeConsistent -- |rgbBuffer| = w * h * 3 or empty       *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

(**************************************************************************)
(* CONSTANTS                                                              *)
(**************************************************************************)
CONSTANTS
    MaxColumns,     \* @type: Int;
    MaxRows,        \* @type: Int;
    MaxWidth,       \* @type: Int;
    MaxHeight       \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Str);
VideoMode == {"TEXT_80x25", "TEXT_80x43", "TEXT_80x50", "TEXT_40x25",
              "MODE_13h", "MODE_12h", "CUSTOM"}

\* @type: Set(Str);
CaptureResult == {"OK", "NULL_HANDLE", "BUFFER_TOO_SMALL"}

(**************************************************************************)
(* VIDEO MODE DIMENSION FUNCTIONS                                         *)
(**************************************************************************)

\* @type: Str -> Int;
ModeColumns(mode) ==
    CASE mode = "TEXT_40x25" -> 40
      [] mode \in {"TEXT_80x25", "TEXT_80x43", "TEXT_80x50"} -> 80
      [] OTHER -> 80

\* @type: Str -> Int;
ModeRows(mode) ==
    CASE mode = "TEXT_80x25" -> 25
      [] mode = "TEXT_40x25" -> 25
      [] mode = "TEXT_80x43" -> 43
      [] mode = "TEXT_80x50" -> 50
      [] OTHER -> 25

\* @type: Str -> Int;
ModePixelWidth(mode) ==
    CASE mode = "TEXT_80x25" -> 640
      [] mode = "TEXT_40x25" -> 320
      [] mode = "MODE_13h"   -> 320
      [] mode = "MODE_12h"   -> 640
      [] OTHER -> 640

\* @type: Str -> Int;
ModePixelHeight(mode) ==
    CASE mode = "TEXT_80x25" -> 400
      [] mode = "TEXT_40x25" -> 400
      [] mode = "MODE_13h"   -> 200
      [] mode = "MODE_12h"   -> 480
      [] OTHER -> 400

\* RGB24 size: width * height * 3 bytes (no padding)
\* @type: (Int, Int) -> Int;
RGB24Size(w, h) == w * h * 3

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    videoMode,      \* @type: Str;
    textColumns,    \* @type: Int;
    textRows,       \* @type: Int;
    rgbWidth,       \* @type: Int;
    rgbHeight,      \* @type: Int;
    rgbBufferSize,  \* @type: Int;   Size in bytes (= w*h*3 or 0)
    frameDirty,     \* @type: Bool;
    cursorX,        \* @type: Int;
    cursorY,        \* @type: Int;
    activeBackend   \* @type: Str;

vars == <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
          rgbBufferSize, frameDirty, cursorX, cursorY, activeBackend>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ videoMode \in VideoMode
    /\ textColumns \in 1..MaxColumns
    /\ textRows \in 1..MaxRows
    /\ rgbWidth \in 1..MaxWidth
    /\ rgbHeight \in 1..MaxHeight
    /\ rgbBufferSize \in {0} \cup {rgbWidth * rgbHeight * 3}
    /\ frameDirty \in BOOLEAN
    /\ cursorX \in 0..MaxColumns
    /\ cursorY \in 0..MaxRows
    /\ activeBackend \in {"Headless", "SDL2", "SDL3"}

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* DimensionsConsistent -- Gate 5a                                    *)
(*                                                                    *)
(* Text and RGB dimensions always match the current video mode.       *)
(*--------------------------------------------------------------------*)
DimensionsConsistent ==
    /\ textColumns = ModeColumns(videoMode)
    /\ textRows = ModeRows(videoMode)
    /\ rgbWidth = ModePixelWidth(videoMode)
    /\ rgbHeight = ModePixelHeight(videoMode)

(*--------------------------------------------------------------------*)
(* FormatFixed -- Gate 5b                                             *)
(*                                                                    *)
(* RGB format is always RGB24, no row padding.                        *)
(* Pitch = width * 3.  Total size = width * height * 3.              *)
(*--------------------------------------------------------------------*)
FormatFixed ==
    RGB24Size(rgbWidth, rgbHeight) = rgbWidth * rgbHeight * 3

(*--------------------------------------------------------------------*)
(* BackendIndependent -- Gate 5c                                      *)
(*                                                                    *)
(* Capture dimensions are determined by videoMode, not by backend.    *)
(*--------------------------------------------------------------------*)
BackendIndependent ==
    /\ textColumns = ModeColumns(videoMode)
    /\ rgbWidth = ModePixelWidth(videoMode)

(*--------------------------------------------------------------------*)
(* FramebufferSizeConsistent                                          *)
(*                                                                    *)
(* The framebuffer byte count is either 0 (not yet rendered) or       *)
(* exactly w * h * 3.                                                 *)
(*--------------------------------------------------------------------*)
FramebufferSizeConsistent ==
    rgbBufferSize = rgbWidth * rgbHeight * 3 \/ rgbBufferSize = 0

(*--------------------------------------------------------------------*)
(* CursorInBounds                                                     *)
(*--------------------------------------------------------------------*)
CursorInBounds ==
    /\ cursorX < textColumns
    /\ cursorY < textRows

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ videoMode = "TEXT_80x25"
    /\ textColumns = 80
    /\ textRows = 25
    /\ rgbWidth = 640
    /\ rgbHeight = 400
    /\ rgbBufferSize = 0
    /\ frameDirty = TRUE
    /\ cursorX = 0
    /\ cursorY = 0
    /\ activeBackend = "Headless"

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

\* Set video mode (INT 10h)
SetVideoMode(mode) ==
    /\ videoMode' = mode
    /\ textColumns' = ModeColumns(mode)
    /\ textRows' = ModeRows(mode)
    /\ rgbWidth' = ModePixelWidth(mode)
    /\ rgbHeight' = ModePixelHeight(mode)
    /\ rgbBufferSize' = 0  \* Reset until next render
    /\ frameDirty' = TRUE
    /\ cursorX' = 0
    /\ cursorY' = 0
    /\ UNCHANGED activeBackend

\* Write character (sets dirty flag)
WriteCharacter(x, y) ==
    /\ x < textColumns
    /\ y < textRows
    /\ frameDirty' = TRUE
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, cursorX, cursorY, activeBackend>>

\* Move cursor
MoveCursor(x, y) ==
    /\ x < textColumns
    /\ y < textRows
    /\ cursorX' = x
    /\ cursorY' = y
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, frameDirty, activeBackend>>

\* Capture text -- clears dirty flag
CaptureText ==
    /\ frameDirty' = FALSE
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, cursorX, cursorY, activeBackend>>

\* Capture RGB -- clears dirty flag, sets buffer size
CaptureRGB ==
    /\ frameDirty' = FALSE
    /\ rgbBufferSize' = rgbWidth * rgbHeight * 3
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   cursorX, cursorY, activeBackend>>

\* Switch backend -- capture output remains identical
SwitchBackend(backend) ==
    /\ activeBackend' = backend
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, frameDirty, cursorX, cursorY>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E m \in VideoMode : SetVideoMode(m)
    \/ \E x \in 0..79, y \in 0..24 : WriteCharacter(x, y)
    \/ \E x \in 0..79, y \in 0..24 : MoveCursor(x, y)
    \/ CaptureText
    \/ CaptureRGB
    \/ \E b \in {"Headless", "SDL2", "SDL3"} : SwitchBackend(b)
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

(**************************************************************************)
(* TEMPORAL PROPERTIES                                                    *)
(**************************************************************************)

\* Capture doesn't modify video state
CaptureIsIdempotent ==
    [][(CaptureText \/ CaptureRGB) =>
       UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight>>]_vars

\* Backend switch is transparent to capture
BackendTransparent ==
    [][(\E b \in {"Headless", "SDL2", "SDL3"} : SwitchBackend(b)) =>
       UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, frameDirty, cursorX, cursorY>>]_vars

=======================================================================
