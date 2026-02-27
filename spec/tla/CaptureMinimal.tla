------------------------ MODULE CaptureMinimal ------------------------
(**************************************************************************)
(* Legends -- Minimal Capture for CI Model Checking                       *)
(*                                                                        *)
(* Reduces to 3 video modes for tractable state space.                    *)
(* Verifies dimensions consistency under all mode transitions,            *)
(* dirty flag lifecycle, and framebuffer size consistency.                 *)
(*                                                                        *)
(* Expected: ~100 distinct states with 1 worker                           *)
(**************************************************************************)
EXTENDS Integers, TLC

(**************************************************************************)
(* TYPES (reduced: 3 modes instead of 7)                                  *)
(**************************************************************************)

\* @type: Set(Str);
VideoMode == {"TEXT_80x25", "MODE_13h", "TEXT_40x25"}

\* @type: Set(Str);
Backend == {"Headless", "SDL2", "SDL3"}

(**************************************************************************)
(* MODE DIMENSION FUNCTIONS                                               *)
(**************************************************************************)

\* @type: Str -> Int;
ModeColumns(mode) ==
    CASE mode = "TEXT_40x25" -> 40
      [] mode = "TEXT_80x25" -> 80
      [] mode = "MODE_13h"   -> 80

\* @type: Str -> Int;
ModeRows(mode) ==
    CASE mode = "TEXT_40x25" -> 25
      [] mode = "TEXT_80x25" -> 25
      [] mode = "MODE_13h"   -> 25

\* @type: Str -> Int;
ModePixelWidth(mode) ==
    CASE mode = "TEXT_80x25" -> 640
      [] mode = "TEXT_40x25" -> 320
      [] mode = "MODE_13h"   -> 320

\* @type: Str -> Int;
ModePixelHeight(mode) ==
    CASE mode = "TEXT_80x25" -> 400
      [] mode = "TEXT_40x25" -> 400
      [] mode = "MODE_13h"   -> 200

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    videoMode,      \* @type: Str;
    textColumns,    \* @type: Int;
    textRows,       \* @type: Int;
    rgbWidth,       \* @type: Int;
    rgbHeight,      \* @type: Int;
    rgbBufferSize,  \* @type: Int;
    frameDirty,     \* @type: Bool;
    activeBackend   \* @type: Str;

vars == <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
          rgbBufferSize, frameDirty, activeBackend>>

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ videoMode \in VideoMode
    /\ textColumns \in {40, 80}
    /\ textRows \in {25}
    /\ rgbWidth \in {320, 640}
    /\ rgbHeight \in {200, 400}
    /\ rgbBufferSize \in {0, rgbWidth * rgbHeight * 3}
    /\ frameDirty \in BOOLEAN
    /\ activeBackend \in Backend

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

\* Gate 5a: Dimensions match mode
DimensionsConsistent ==
    /\ textColumns = ModeColumns(videoMode)
    /\ textRows = ModeRows(videoMode)
    /\ rgbWidth = ModePixelWidth(videoMode)
    /\ rgbHeight = ModePixelHeight(videoMode)

\* Gate 5b: RGB24 format, pitch = width * 3
FormatFixed ==
    rgbBufferSize = 0 \/ rgbBufferSize = rgbWidth * rgbHeight * 3

\* Gate 5c: Backend independent -- dimensions from mode, not backend
BackendIndependent ==
    /\ textColumns = ModeColumns(videoMode)
    /\ rgbWidth = ModePixelWidth(videoMode)

\* Framebuffer size is either 0 or w*h*3
FramebufferSizeConsistent ==
    rgbBufferSize = rgbWidth * rgbHeight * 3 \/ rgbBufferSize = 0

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
    /\ activeBackend = "Headless"

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

SetVideoMode(mode) ==
    /\ videoMode' = mode
    /\ textColumns' = ModeColumns(mode)
    /\ textRows' = ModeRows(mode)
    /\ rgbWidth' = ModePixelWidth(mode)
    /\ rgbHeight' = ModePixelHeight(mode)
    /\ rgbBufferSize' = 0
    /\ frameDirty' = TRUE
    /\ UNCHANGED activeBackend

WriteChar ==
    /\ frameDirty' = TRUE
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, activeBackend>>

CaptureText ==
    /\ frameDirty' = FALSE
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, activeBackend>>

CaptureRGB ==
    /\ frameDirty' = FALSE
    /\ rgbBufferSize' = rgbWidth * rgbHeight * 3
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   activeBackend>>

SwitchBackend(b) ==
    /\ activeBackend' = b
    /\ UNCHANGED <<videoMode, textColumns, textRows, rgbWidth, rgbHeight,
                   rgbBufferSize, frameDirty>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E m \in VideoMode : SetVideoMode(m)
    \/ WriteChar
    \/ CaptureText
    \/ CaptureRGB
    \/ \E b \in Backend : SwitchBackend(b)
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================

