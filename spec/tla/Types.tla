---------------------------- MODULE Types ----------------------------
(**************************************************************************)
(* Legends Emukernel -- Core Type Definitions                             *)
(*                                                                        *)
(* READING GUIDE                                                          *)
(* This is the foundation module imported by all other specifications.    *)
(* It defines shared types, error codes, and helper operators.  Nothing   *)
(* in this module has state or behaviour -- it is purely definitional.    *)
(*                                                                        *)
(* Key sections:                                                          *)
(*   ErrorCode      -- the 14+1 error code set matching legends_embed.h  *)
(*   ConfigRecord   -- bounded model of legends_config_t                  *)
(*   AbstractHash   -- concrete polynomial hash (replaces old CHOOSE)    *)
(*   BitSet/ClearBit -- 8-bit register manipulation for PIC modelling    *)
(*                                                                        *)
(* Apalache type annotations are provided on all operators and constants  *)
(* using the @type convention.  When running with TLC these are comments; *)
(* Apalache parses them for type checking.                                *)
(*                                                                        *)
(* Design decisions:                                                      *)
(*   - All numeric domains are bounded (Cycles, EventIds, ...)            *)
(*   - Record types are defined as set comprehensions, not schemas        *)
(*   - Explicit tieKey field ensures deterministic event ordering         *)
(*   - Error codes are the complete set from legends_embed.h              *)
(*   - CPU bridge types anticipate Phase-A roadmap                        *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(**************************************************************************)
(* CONSTANTS -- Bounds for model checking                                 *)
(**************************************************************************)
CONSTANTS
    MaxCycle,       \* @type: Int;  Maximum virtual time (cycles)
    MaxEvents,      \* @type: Int;  Maximum events in queue
    MaxPorts,       \* @type: Int;  Number of I/O ports
    MaxMemRegions   \* @type: Int;  Number of memory regions

(**************************************************************************)
(* ERROR CODES                                                            *)
(*                                                                        *)
(* Complete set of 14+1 error codes from legends_embed.h.                 *)
(* Every API function returns one of these.  The numeric value in the     *)
(* comment matches the C enum.                                            *)
(**************************************************************************)

\* @type: Set(Str);
ErrorCode == {
    "OK",                   \*  0  LEGENDS_OK
    "NULL_HANDLE",          \* -1  LEGENDS_ERR_NULL_HANDLE
    "NULL_POINTER",         \* -2  LEGENDS_ERR_NULL_POINTER
    "ALREADY_CREATED",      \* -3  LEGENDS_ERR_ALREADY_CREATED
    "NOT_INITIALIZED",      \* -4  LEGENDS_ERR_NOT_INITIALIZED
    "REENTRANT_CALL",       \* -5  LEGENDS_ERR_REENTRANT_CALL
    "BUFFER_TOO_SMALL",     \* -6  LEGENDS_ERR_BUFFER_TOO_SMALL
    "INVALID_CONFIG",       \* -7  LEGENDS_ERR_INVALID_CONFIG
    "INVALID_STATE",        \* -8  LEGENDS_ERR_INVALID_STATE
    "VERSION_MISMATCH",     \* -9  LEGENDS_ERR_VERSION_MISMATCH
    "IO_FAILED",            \* -10 LEGENDS_ERR_IO_FAILED
    "OUT_OF_MEMORY",        \* -11 LEGENDS_ERR_OUT_OF_MEMORY
    "NOT_SUPPORTED",        \* -12 LEGENDS_ERR_NOT_SUPPORTED
    "INTERNAL",             \* -13 LEGENDS_ERR_INTERNAL
    "WRONG_THREAD"          \* -14 LEGENDS_ERR_WRONG_THREAD
}

\* @type: Int -> Str;
ErrorCodeNumToStr(n) ==
    CASE n =  0 -> "OK"
      [] n = -1 -> "NULL_HANDLE"
      [] n = -2 -> "NULL_POINTER"
      [] n = -3 -> "ALREADY_CREATED"
      [] n = -4 -> "NOT_INITIALIZED"
      [] n = -5 -> "REENTRANT_CALL"
      [] n = -6 -> "BUFFER_TOO_SMALL"
      [] n = -7 -> "INVALID_CONFIG"
      [] n = -8 -> "INVALID_STATE"
      [] n = -9 -> "VERSION_MISMATCH"
      [] n = -10 -> "IO_FAILED"
      [] n = -11 -> "OUT_OF_MEMORY"
      [] n = -12 -> "NOT_SUPPORTED"
      [] n = -13 -> "INTERNAL"
      [] n = -14 -> "WRONG_THREAD"

(**************************************************************************)
(* INSTANCE LIFECYCLE STATES                                              *)
(**************************************************************************)

\* @type: Set(Str);
InstanceState == {"NONE", "CREATED", "DESTROYED"}

(**************************************************************************)
(* REENTRANCY STATES                                                      *)
(*                                                                        *)
(* Models whether the emulator is currently inside a step call,           *)
(* inside a PAL callback invoked by that step, or idle.                   *)
(**************************************************************************)

\* @type: Set(Str);
ReentrancyPhase == {"IDLE", "IN_STEP", "IN_CALLBACK"}

(**************************************************************************)
(* API OPERATIONS                                                         *)
(**************************************************************************)

\* @type: Set(Str);
Operation == {
    "CREATE", "DESTROY", "RESET",
    "STEP", "CAPTURE", "INPUT",
    "SAVE", "LOAD", "QUERY"
}

(**************************************************************************)
(* CONFIGURATION RECORD                                                   *)
(*                                                                        *)
(* Mirrors legends_config_t from legends_embed.h.  Each field is bounded  *)
(* for TLC; real ranges are documented in comments.                       *)
(*                                                                        *)
(* USAGE:                                                                 *)
(*   ConfigValid(cfg) checks whether a config record is acceptable for   *)
(*   legends_create().  Invalid configs (wrong version, zero cycles_per_ms*)
(*   etc.) are rejected before any instance is created.                  *)
(*                                                                        *)
(* See also: ConfigValidation.tla for the full config validation model.  *)
(**************************************************************************)

\* @type: Set({deterministic: Bool, cycles_per_ms: Int, audio_rate: Int, version_major: Int});
ConfigRecord == {
    [deterministic |-> d, cycles_per_ms |-> c, audio_rate |-> a, version_major |-> v]
    : d \in BOOLEAN,
      c \in {50, 100, 200},         \* real: 1..1193182
      a \in {11025, 22050, 44100},   \* real: 8000..48000
      v \in {1, 2}                   \* API major version
}

\* @type: {deterministic: Bool, cycles_per_ms: Int, audio_rate: Int, version_major: Int} -> Bool;
ConfigValid(cfg) ==
    /\ cfg.cycles_per_ms > 0
    /\ cfg.audio_rate > 0
    /\ cfg.version_major = 1

(**************************************************************************)
(* CORE DOMAIN SETS (bounded for TLC)                                     *)
(**************************************************************************)

\* @type: Set(Int);
Cycles == 0..MaxCycle

\* @type: Set(Int);
EventIds == 0..(MaxEvents - 1)

(**************************************************************************)
(* I/O PORT SET                                                           *)
(*                                                                        *)
(* Key ports for the emulated system.  Hex values in comments.            *)
(*   PIC master: 0x20-0x21   PIC slave: 0xA0-0xA1                        *)
(*   PIT:        0x40-0x43   KBD:       0x60-0x61                         *)
(**************************************************************************)

\* @type: Set(Int);
PortSet == {32, 33, 64, 65, 66, 67, 96, 97, 160, 161}

\* @type: Set(Str);
MemRegion == {"RAM", "VGA", "ROM", "UNMAPPED"}

(**************************************************************************)
(* EVENT SYSTEM TYPES                                                     *)
(**************************************************************************)

\* @type: Set(Str);
EventKind == {"PIT_TICK", "KBD_SCAN", "DMA_TC", "TIMER_CB", "IRQ_CHECK"}

\* @type: Set(Int);
PayloadRange == 0..255

\* @type: Set(Int);
TieKeyRange == 0..100

\* @type: Set({id: Int, deadline: Int, kind: Str, payload: Int, tieKey: Int});
Event == { [id |-> i, deadline |-> d, kind |-> k, payload |-> p, tieKey |-> t]
           : i \in EventIds, d \in Cycles, k \in EventKind,
             p \in PayloadRange, t \in TieKeyRange }

(**************************************************************************)
(* CPU STATE TYPES                                                        *)
(**************************************************************************)

\* @type: Set(Str);
CPUMode == {"Real", "Protected", "V86"}

\* @type: Set({IF: Bool, halted: Bool, mode: Str});
CPUState == { [IF |-> f, halted |-> h, mode |-> m]
              : f \in BOOLEAN, h \in BOOLEAN, m \in CPUMode }

(**************************************************************************)
(* CPU BRIDGE TYPES (Phase A roadmap)                                     *)
(*                                                                        *)
(* Abstract register model for the x86 CPU bridge.  Only the registers    *)
(* that affect observable behaviour are modelled.                          *)
(**************************************************************************)

\* @type: Set(Int);
RegisterValue == 0..65535   \* 16-bit for model checking; real: 32-bit

\* @type: Set({ax: Int, bx: Int, cx: Int, dx: Int});
CPURegisterSet == { [ax |-> a, bx |-> b, cx |-> c, dx |-> d]
                    : a \in RegisterValue, b \in RegisterValue,
                      c \in RegisterValue, d \in RegisterValue }

\* @type: Set({cf: Bool, zf: Bool, sf: Bool, of: Bool, intf: Bool});
FlagSet == { [cf |-> c, zf |-> z, sf |-> s, of |-> o, intf |-> i]
             : c \in BOOLEAN, z \in BOOLEAN, s \in BOOLEAN,
               o \in BOOLEAN, i \in BOOLEAN }

\* @type: Set(Int);
InstructionPointer == 0..1048575   \* 20-bit real-mode address space

(**************************************************************************)
(* INTERRUPT CONTROLLER (8259A PIC) TYPES                                 *)
(**************************************************************************)

\* @type: Set(Int);
RegRange == 0..255

\* @type: Set(Int);
CascadeIRQ == 0..7

\* @type: Set({irr: Int, imr: Int, isr: Int, vector_base: Int, cascade_irq: Int});
PICState == { [irr |-> r, imr |-> m, isr |-> s, vector_base |-> v, cascade_irq |-> c]
              : r \in RegRange, m \in RegRange, s \in RegRange,
                v \in RegRange, c \in CascadeIRQ }

(**************************************************************************)
(* DMA CONTROLLER TYPES                                                   *)
(**************************************************************************)

\* @type: Set(Int);
DMACount == 0..1023

\* @type: Set({enabled: Bool, masked: Bool, count: Int, request: Bool, tc_reached: Bool, autoinit: Bool});
DMAChannelState == { [enabled |-> e, masked |-> ma, count |-> c,
                      request |-> r, tc_reached |-> tc, autoinit |-> ai]
                     : e \in BOOLEAN, ma \in BOOLEAN, c \in DMACount,
                       r \in BOOLEAN, tc \in BOOLEAN, ai \in BOOLEAN }

(**************************************************************************)
(* I/O PORT HANDLER TYPES                                                 *)
(**************************************************************************)

\* @type: Set(Str);
IOHandler == {"PIC", "PIT", "DMA", "KBD", "VGA", "NONE"}

(**************************************************************************)
(* SAVE STATE HEADER TYPES                                                *)
(*                                                                        *)
(* Models the V3 binary save-state format header.                         *)
(*   magic:   4-byte identifier "LGND"                                    *)
(*   version: format version (2 or 3)                                     *)
(*   crc:     CRC32 of payload                                            *)
(*   size:    payload size in bytes                                       *)
(**************************************************************************)

\* @type: Set(Int);
SaveVersion == {2, 3}

\* @type: Set(Int);
CRCRange == 0..65535  \* bounded for TLC; real: 32-bit

\* @type: Set({magic: Str, version: Int, crc: Int, size: Int});
SaveHeader == { [magic |-> "LGND", version |-> v, crc |-> c, size |-> s]
                : v \in SaveVersion, c \in CRCRange, s \in 0..65535 }

(**************************************************************************)
(* THREAD IDENTIFIERS                                                     *)
(**************************************************************************)

\* @type: Set(Str);
ThreadId == {"Main", "AudioCallback", "InputPoll", "Timer", "None"}

(**************************************************************************)
(* PAL BACKEND TYPES                                                      *)
(**************************************************************************)

\* @type: Set(Str);
Backend == {"Headless", "SDL2", "SDL3"}

\* @type: Set(Str);
PALComponent == {"Window", "Context", "AudioSink", "HostClock", "InputSource"}

(**************************************************************************)
(* VIDEO MODE TYPES                                                       *)
(**************************************************************************)

\* @type: Set(Str);
VideoMode == {"TEXT_80x25", "TEXT_80x43", "TEXT_80x50", "TEXT_40x25",
              "MODE_13h", "MODE_12h", "CUSTOM"}

(**************************************************************************)
(* SCANCODE TYPES                                                         *)
(**************************************************************************)

\* @type: Set(Int);
AllScancodes == 1..127

\* @type: Set(Int);
MouseButton == {1, 2, 4}  \* Left=1, Right=2, Middle=4

(**************************************************************************)
(* HELPER OPERATORS                                                       *)
(**************************************************************************)

\* @type: Set(Int) -> Int;
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* @type: Set(Int) -> Int;
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Convert a set of integers to a sorted sequence (ascending)
\* @type: Set(Int) -> Seq(Int);
RECURSIVE SetToSeq(_)
SetToSeq(S) ==
  IF S = {} THEN <<>>
  ELSE LET min == Min(S)
       IN <<min>> \o SetToSeq(S \ {min})

(**************************************************************************)
(* BIT MANIPULATION OPERATORS                                             *)
(*                                                                        *)
(* For working with 8-bit registers (IRR, IMR, ISR) in the PIC model.    *)
(* Preconditions: bit in 0..7, reg in 0..255.                             *)
(*                                                                        *)
(* USAGE EXAMPLES:                                                        *)
(*   BitSet(5, 0)   => TRUE   (bit 0 of 5=0b101 is set)                 *)
(*   BitSet(5, 1)   => FALSE  (bit 1 of 5=0b101 is not set)             *)
(*   SetBit(4, 0)   => 5      (4=0b100 with bit 0 set => 0b101=5)       *)
(*   ClearBit(5, 0) => 4      (5=0b101 with bit 0 cleared => 0b100=4)   *)
(*   LowestBit(6)   => 1      (6=0b110, lowest set bit is 1)            *)
(*   PopCount(7)    => 3      (7=0b111, three bits set)                  *)
(**************************************************************************)

\* @type: (Int, Int) -> Bool;
BitSet(reg, bit) ==
    /\ bit \in 0..7
    /\ reg \in 0..255
    /\ (reg % (2^(bit+1))) \div (2^bit) = 1

\* @type: (Int, Int) -> Int;
SetBit(reg, bit) ==
    IF BitSet(reg, bit) THEN reg ELSE reg + 2^bit

\* @type: (Int, Int) -> Int;
ClearBit(reg, bit) ==
    IF BitSet(reg, bit) THEN reg - 2^bit ELSE reg

\* Get lowest set bit (for priority encoding).
\* Returns -1 if no bits are set.
\* @type: Int -> Int;
LowestBit(reg) ==
  IF reg = 0 THEN -1
  ELSE CHOOSE b \in 0..7 : BitSet(reg, b) /\ \A b2 \in 0..(b-1) : ~BitSet(reg, b2)

\* Count number of set bits in an 8-bit register.
\* @type: Int -> Int;
PopCount(reg) == Cardinality({b \in 0..7 : BitSet(reg, b)})

(**************************************************************************)
(* ABSTRACT HASH OPERATOR                                                 *)
(*                                                                        *)
(* Maps a (config, inputSeq, stepSeq, cycle) tuple to an abstract hash.   *)
(* Modelled as an injective function over a small domain for TLC.         *)
(* The key property: identical inputs always produce an identical hash     *)
(* (determinism), and different inputs produce different hashes within     *)
(* the finite model (collision freedom).                                  *)
(*                                                                        *)
(* WHY POLYNOMIAL HASH INSTEAD OF CHOOSE:                                *)
(* The v1 specs used CHOOSE h \in HashDomain : TRUE, which is trivially  *)
(* satisfiable -- TLC picks an arbitrary value, so the "determinism"      *)
(* invariant was vacuously true.  This concrete polynomial rolling hash   *)
(* (multiply-accumulate mod 997) is deterministic by construction:        *)
(* same inputs always produce the same output, no CHOOSE involved.       *)
(*                                                                        *)
(* WHY MODULO 997:                                                       *)
(* 997 is prime, which gives good distribution for polynomial hashing.   *)
(* Within the small finite models used for TLC (MaxInputs <= 3), the     *)
(* hash is collision-free.  For larger models, collisions are possible   *)
(* but do not affect the correctness of the determinism property.        *)
(*                                                                        *)
(* USAGE:                                                                 *)
(*   AbstractHash(1, <<"KEY_A", "KEY_B">>, <<100, 200>>, 300)            *)
(*   => (1*7 + HashInputs*13 + HashSteps*19 + 300) % 997                *)
(*                                                                        *)
(* The domain is parameterised by the importing module so that each       *)
(* specification can choose a tractable hash range.                       *)
(**************************************************************************)

\* @type: (Int, Seq(Str), Seq(Int), Int) -> Int;
AbstractHash(cfgId, inputs, steps, cycle) ==
    LET
        \* Fold input sequence into a single integer via simple
        \* polynomial-rolling scheme modulo a prime.
        RECURSIVE InputHash(_, _)
        InputHash(seq, acc) ==
            IF seq = <<>> THEN acc
            ELSE LET head == CASE Head(seq) = "KEY_A"      -> 1
                               [] Head(seq) = "KEY_B"      -> 2
                               [] Head(seq) = "KEY_ENTER"  -> 3
                               [] Head(seq) = "MOUSE_MOVE" -> 4
                               [] OTHER                    -> 0
                 IN InputHash(Tail(seq), (acc * 31 + head) % 997)
        \* Fold step sequence similarly.
        RECURSIVE StepHash(_, _)
        StepHash(seq, acc) ==
            IF seq = <<>> THEN acc
            ELSE StepHash(Tail(seq), (acc * 37 + Head(seq)) % 997)
        ih == InputHash(inputs, 0)
        sh == StepHash(steps, 0)
    IN (cfgId * 7 + ih * 13 + sh * 19 + cycle) % 997

=======================================================================
