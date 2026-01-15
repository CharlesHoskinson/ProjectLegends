---------------------------- MODULE Types ----------------------------
(*
 * Legends Emukernel - Core Type Definitions
 *
 * This module defines the fundamental types and helper operators used
 * throughout the emukernel TLA+ specification. All domains are bounded
 * to ensure TLC model-checkability.
 *
 * Key design decisions:
 * - All numeric domains are bounded (Cycles, EventIds, etc.)
 * - Record types are defined as set comprehensions (not schemas)
 * - Explicit tieKey field ensures deterministic event ordering
 *)
EXTENDS Integers, Sequences, FiniteSets

\* =====================================================================
\* CONSTANTS - Bounds for model checking
\* =====================================================================
CONSTANTS
    MaxCycle,       \* Maximum virtual time (cycles)
    MaxEvents,      \* Maximum events in queue
    MaxPorts,       \* Number of I/O ports (unused, for future)
    MaxMemRegions   \* Number of memory regions (unused, for future)

\* =====================================================================
\* Core Domain Sets (bounded for TLC)
\* =====================================================================

\* Virtual time measured in cycles
Cycles == 0..MaxCycle

\* Event identifiers - one less than MaxEvents to match Cardinality bound
EventIds == 0..(MaxEvents - 1)

\* Key I/O ports for the emulated system
\* Using hex notation: 0x20=32, 0x21=33, 0x40=64, etc.
\* PIC: 0x20-0x21 (master), 0xA0-0xA1 (slave)
\* PIT: 0x40-0x43
\* KBD: 0x60-0x61
PortSet == {32, 33, 64, 65, 66, 67, 96, 97, 160, 161}

\* Memory region types
MemRegion == {"RAM", "VGA", "ROM", "UNMAPPED"}

\* =====================================================================
\* Event System Types
\* =====================================================================

\* Abstract device event kinds
EventKind == {"PIT_TICK", "KBD_SCAN", "DMA_TC", "TIMER_CB", "IRQ_CHECK"}

\* Bounded ranges for event fields (TLC tractability)
PayloadRange == 0..255
TieKeyRange == 0..100

\* Event record structure - defined as SET of valid records
\* The tieKey field ensures deterministic ordering when deadlines match
Event == { [id |-> i, deadline |-> d, kind |-> k, payload |-> p, tieKey |-> t]
           : i \in EventIds, d \in Cycles, k \in EventKind,
             p \in PayloadRange, t \in TieKeyRange }

\* =====================================================================
\* CPU State Types
\* =====================================================================

\* CPU operating modes
CPUMode == {"Real", "Protected", "V86"}

\* CPU state - abstract model (no instruction-level decode)
\* IF: Interrupt Flag - when TRUE, interrupts can be delivered
\* halted: CPU is in HLT state, waiting for interrupt
\* mode: Current operating mode
CPUState == { [IF |-> f, halted |-> h, mode |-> m]
              : f \in BOOLEAN, h \in BOOLEAN, m \in CPUMode }

\* =====================================================================
\* Interrupt Controller (8259A PIC) Types
\* =====================================================================

\* PIC register ranges (8-bit)
RegRange == 0..255
CascadeIRQ == 0..7

\* PIC controller state
\* irr: Interrupt Request Register - pending interrupt requests
\* imr: Interrupt Mask Register - masked (disabled) interrupts
\* isr: In-Service Register - currently being serviced
\* vector_base: Base interrupt vector (8 for master, 112 for slave)
\* cascade_irq: IRQ line used for slave cascade (usually 2)
PICState == { [irr |-> r, imr |-> m, isr |-> s, vector_base |-> v, cascade_irq |-> c]
              : r \in RegRange, m \in RegRange, s \in RegRange,
                v \in RegRange, c \in CascadeIRQ }

\* =====================================================================
\* DMA Controller Types
\* =====================================================================

\* DMA count range - bounded for TLC (full range is 0..65535)
DMACount == 0..1023

\* DMA channel state - control semantics only, not byte-level data
\* enabled: Channel is enabled
\* masked: Channel is masked (transfers blocked)
\* count: Remaining transfer count
\* request: DMA request pending from device
\* tc_reached: Terminal count has been reached
\* autoinit: Auto-reinitialize on terminal count
DMAChannelState == { [enabled |-> e, masked |-> ma, count |-> c,
                      request |-> r, tc_reached |-> tc, autoinit |-> ai]
                     : e \in BOOLEAN, ma \in BOOLEAN, c \in DMACount,
                       r \in BOOLEAN, tc \in BOOLEAN, ai \in BOOLEAN }

\* =====================================================================
\* I/O Port Handler Types
\* =====================================================================

\* Device handlers for I/O ports
IOHandler == {"PIC", "PIT", "DMA", "KBD", "VGA", "NONE"}

\* =====================================================================
\* Error State Types (for invariant checking)
\* =====================================================================

\* Error conditions that should never occur
ErrorState == {"NONE", "OOB", "MASKED_IRQ", "DMA_TC_MISFIRE"}

\* =====================================================================
\* Helper Operators
\* =====================================================================

\* Minimum element of a non-empty set
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Maximum element of a non-empty set
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Convert a set to a sorted sequence (ascending order)
\* Useful for deterministic iteration over sets
RECURSIVE SetToSeq(_)
SetToSeq(S) ==
  IF S = {} THEN <<>>
  ELSE LET min == Min(S)
       IN <<min>> \o SetToSeq(S \ {min})

\* =====================================================================
\* Bit Manipulation Operators
\* For working with 8-bit registers (IRR, IMR, ISR)
\* =====================================================================

\* Test if bit 'bit' is set in register 'reg'
BitSet(reg, bit) == (reg % (2^(bit+1))) \div (2^bit) = 1

\* Set bit 'bit' in register 'reg'
SetBit(reg, bit) == IF BitSet(reg, bit) THEN reg ELSE reg + 2^bit

\* Clear bit 'bit' in register 'reg'
ClearBit(reg, bit) == IF BitSet(reg, bit) THEN reg - 2^bit ELSE reg

\* Get lowest set bit (for priority encoding)
\* Returns -1 if no bits set
LowestBit(reg) ==
  IF reg = 0 THEN -1
  ELSE CHOOSE b \in 0..7 : BitSet(reg, b) /\ \A b2 \in 0..(b-1) : ~BitSet(reg, b2)

\* Count number of set bits
PopCount(reg) == Cardinality({b \in 0..7 : BitSet(reg, b)})

=======================================================================
