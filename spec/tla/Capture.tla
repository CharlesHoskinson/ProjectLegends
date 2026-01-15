---------------------------- MODULE Capture ----------------------------
(*
 * Legends - Screen Capture Contract
 *
 * This module specifies the capture API:
 * - Text capture (CP437 character cells)
 * - RGB capture (pre-scaler framebuffer)
 * - Backend-independent output
 *
 * Key invariants:
 * - DimensionsConsistent: Dimensions don't change arbitrarily
 * - FormatFixed: RGB24 format, no padding
 * - BackendIndependent: Same state produces same capture
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    MaxColumns,         \* Maximum text columns
    MaxRows,            \* Maximum text rows
    MaxWidth,           \* Maximum pixel width
    MaxHeight           \* Maximum pixel height

\* =====================================================================
\* TYPES
\* =====================================================================

\* Video mode types
VideoMode == {"TEXT_80x25", "TEXT_80x43", "TEXT_80x50", "TEXT_40x25",
              "MODE_13h", "MODE_12h", "CUSTOM"}

\* Text cell (CP437 + VGA attribute)
\* attribute: bits 0-3 = foreground, 4-6 = background, 7 = blink
TextCell == [character: 0..255, attribute: 0..255]

\* Text mode info
TextInfo == [
    columns: 1..MaxColumns,
    rows: 1..MaxRows,
    active_page: 0..7,
    cursor_x: 0..MaxColumns,
    cursor_y: 0..MaxRows,
    cursor_visible: BOOLEAN
]

\* RGB pixel (24-bit)
RGBPixel == [r: 0..255, g: 0..255, b: 0..255]

\* Capture result
CaptureResult == {"OK", "NULL_HANDLE", "BUFFER_TOO_SMALL"}

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    videoMode,          \* Current video mode
    textBuffer,         \* Text mode buffer (sequence of cells)
    textInfo,           \* Text mode metadata
    rgbBuffer,          \* RGB framebuffer
    rgbWidth,           \* Framebuffer width
    rgbHeight,          \* Framebuffer height
    frameDirty,         \* Frame dirty flag
    activeBackend       \* Current PAL backend

vars == <<videoMode, textBuffer, textInfo, rgbBuffer,
          rgbWidth, rgbHeight, frameDirty, activeBackend>>

\* =====================================================================
\* HELPER OPERATORS
\* =====================================================================

\* Calculate dimensions for video mode
ModeColumns(mode) ==
    CASE mode = "TEXT_40x25" -> 40
      [] mode \in {"TEXT_80x25", "TEXT_80x43", "TEXT_80x50"} -> 80
      [] OTHER -> 80

ModeRows(mode) ==
    CASE mode = "TEXT_80x25" -> 25
      [] mode = "TEXT_40x25" -> 25
      [] mode = "TEXT_80x43" -> 43
      [] mode = "TEXT_80x50" -> 50
      [] OTHER -> 25

ModePixelWidth(mode) ==
    CASE mode = "TEXT_80x25" -> 640
      [] mode = "TEXT_40x25" -> 320
      [] mode = "MODE_13h" -> 320
      [] mode = "MODE_12h" -> 640
      [] OTHER -> 640

ModePixelHeight(mode) ==
    CASE mode = "TEXT_80x25" -> 400
      [] mode = "TEXT_40x25" -> 400
      [] mode = "MODE_13h" -> 200
      [] mode = "MODE_12h" -> 480
      [] OTHER -> 400

\* RGB24 size calculation (no padding)
RGB24Size(w, h) == w * h * 3

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

TypeOK ==
    /\ videoMode \in VideoMode
    /\ textInfo.columns \in 1..MaxColumns
    /\ textInfo.rows \in 1..MaxRows
    /\ textInfo.active_page \in 0..7
    /\ textInfo.cursor_x \in 0..textInfo.columns
    /\ textInfo.cursor_y \in 0..textInfo.rows
    /\ textInfo.cursor_visible \in BOOLEAN
    /\ rgbWidth \in 1..MaxWidth
    /\ rgbHeight \in 1..MaxHeight
    /\ frameDirty \in BOOLEAN
    /\ activeBackend \in {"Headless", "SDL2", "SDL3"}

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

(*
 * DimensionsConsistent - Dimensions match video mode
 *)
DimensionsConsistent ==
    /\ textInfo.columns = ModeColumns(videoMode)
    /\ textInfo.rows = ModeRows(videoMode)
    /\ rgbWidth = ModePixelWidth(videoMode)
    /\ rgbHeight = ModePixelHeight(videoMode)

(*
 * FormatFixed - RGB format is always RGB24, no padding
 *
 * Pitch = width * 3 (no row padding)
 * Total size = width * height * 3
 *)
FormatFixed ==
    \* Size calculation is pure function of dimensions
    RGB24Size(rgbWidth, rgbHeight) = rgbWidth * rgbHeight * 3

(*
 * BackendIndependent - Capture doesn't depend on backend
 *
 * Same video state produces same capture regardless of backend.
 *)
BackendIndependent ==
    \* Dimensions determined by videoMode, not by backend
    /\ textInfo.columns = ModeColumns(videoMode)
    /\ rgbWidth = ModePixelWidth(videoMode)

(*
 * CellCountMatches - Text buffer size matches dimensions
 *)
CellCountMatches ==
    Len(textBuffer) = textInfo.columns * textInfo.rows

(*
 * CursorInBounds - Cursor position is within screen
 *)
CursorInBounds ==
    /\ textInfo.cursor_x < textInfo.columns
    /\ textInfo.cursor_y < textInfo.rows

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

\* Initial text cell (space with default attribute)
InitCell == [character |-> 32, attribute |-> 7]  \* ' ' with light gray on black

Init ==
    /\ videoMode = "TEXT_80x25"
    /\ textBuffer = [i \in 1..(80*25) |-> InitCell]
    /\ textInfo = [
        columns |-> 80,
        rows |-> 25,
        active_page |-> 0,
        cursor_x |-> 0,
        cursor_y |-> 0,
        cursor_visible |-> TRUE
       ]
    /\ rgbBuffer = <<>>  \* Simplified: not modeling actual pixels
    /\ rgbWidth = 640
    /\ rgbHeight = 400
    /\ frameDirty = TRUE
    /\ activeBackend = "Headless"

\* =====================================================================
\* ACTIONS - CAPTURE
\* =====================================================================

(*
 * legends_capture_text(handle, buffer, size, &count, &info)
 *
 * Capture text mode screen.
 * Returns cells and metadata.
 *)
CaptureText ==
    \* Capture clears dirty flag
    /\ frameDirty' = FALSE
    /\ UNCHANGED <<videoMode, textBuffer, textInfo, rgbBuffer,
                   rgbWidth, rgbHeight, activeBackend>>

(*
 * legends_capture_rgb(handle, buffer, size, &actual, &w, &h)
 *
 * Capture RGB framebuffer.
 * Format: RGB24, no padding.
 *)
CaptureRGB ==
    \* Capture clears dirty flag
    /\ frameDirty' = FALSE
    /\ UNCHANGED <<videoMode, textBuffer, textInfo, rgbBuffer,
                   rgbWidth, rgbHeight, activeBackend>>

(*
 * legends_is_frame_dirty(handle, &dirty)
 *
 * Check if frame changed since last capture.
 *)
CheckDirty ==
    UNCHANGED vars

(*
 * legends_get_cursor(handle, &x, &y, &visible)
 *
 * Get cursor position and visibility.
 *)
GetCursor ==
    UNCHANGED vars

\* =====================================================================
\* ACTIONS - VIDEO MODE CHANGES
\* =====================================================================

(*
 * Set video mode (INT 10h, AH=00h)
 *)
SetVideoMode(mode) ==
    /\ videoMode' = mode
    /\ textInfo' = [
        columns |-> ModeColumns(mode),
        rows |-> ModeRows(mode),
        active_page |-> 0,
        cursor_x |-> 0,
        cursor_y |-> 0,
        cursor_visible |-> TRUE
       ]
    /\ rgbWidth' = ModePixelWidth(mode)
    /\ rgbHeight' = ModePixelHeight(mode)
    /\ textBuffer' = [i \in 1..(ModeColumns(mode) * ModeRows(mode)) |-> InitCell]
    /\ frameDirty' = TRUE
    /\ UNCHANGED <<rgbBuffer, activeBackend>>

(*
 * Write character to screen (sets dirty)
 *)
WriteCharacter(x, y, char, attr) ==
    /\ x < textInfo.columns
    /\ y < textInfo.rows
    /\ LET idx == y * textInfo.columns + x + 1
       IN textBuffer' = [textBuffer EXCEPT ![idx] = [character |-> char, attribute |-> attr]]
    /\ frameDirty' = TRUE
    /\ UNCHANGED <<videoMode, textInfo, rgbBuffer, rgbWidth, rgbHeight, activeBackend>>

(*
 * Move cursor
 *)
MoveCursor(x, y) ==
    /\ x < textInfo.columns
    /\ y < textInfo.rows
    /\ textInfo' = [textInfo EXCEPT !.cursor_x = x, !.cursor_y = y]
    /\ UNCHANGED <<videoMode, textBuffer, rgbBuffer, rgbWidth, rgbHeight, frameDirty, activeBackend>>

\* =====================================================================
\* ACTIONS - BACKEND SWITCH
\* =====================================================================

(*
 * Switch PAL backend - capture output remains identical
 *)
SwitchBackend(backend) ==
    /\ activeBackend' = backend
    \* Critical: nothing else changes - backend is transparent
    /\ UNCHANGED <<videoMode, textBuffer, textInfo, rgbBuffer,
                   rgbWidth, rgbHeight, frameDirty>>

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================

Next ==
    \/ CaptureText
    \/ CaptureRGB
    \/ CheckDirty
    \/ GetCursor
    \/ \E m \in VideoMode : SetVideoMode(m)
    \/ \E x \in 0..79, y \in 0..24, c \in 32..126, a \in 0..255 :
        WriteCharacter(x, y, c, a)
    \/ \E x \in 0..79, y \in 0..24 : MoveCursor(x, y)
    \/ \E b \in {"Headless", "SDL2", "SDL3"} : SwitchBackend(b)
    \/ UNCHANGED vars

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars

\* =====================================================================
\* PROPERTIES
\* =====================================================================

(*
 * CaptureIsIdempotent - Multiple captures return same data
 *)
CaptureIsIdempotent ==
    \* Capture doesn't modify video state (only dirty flag)
    [][(CaptureText \/ CaptureRGB) =>
       UNCHANGED <<videoMode, textBuffer, textInfo, rgbWidth, rgbHeight>>]_vars

(*
 * DirtyFlagWorks - Flag tracks changes correctly
 *)
DirtyFlagWorks ==
    \* Writing sets dirty, capturing clears it
    [][WriteCharacter => frameDirty']_vars

(*
 * BackendTransparent - Backend switch doesn't affect capture
 *)
BackendTransparent ==
    [][SwitchBackend =>
       UNCHANGED <<videoMode, textBuffer, textInfo, rgbBuffer,
                   rgbWidth, rgbHeight, frameDirty>>]_vars

=======================================================================
