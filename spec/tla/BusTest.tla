---------------------------- MODULE BusTest ----------------------------
(*
 * Legends Emukernel - Bus Routing Test Harness
 *
 * This module tests the Bus module's memory and I/O routing.
 * It verifies:
 * 1. Disjoint memory ranges invariant
 * 2. Correct routing to handlers
 * 3. Dynamic remapping
 *)
EXTENDS Bus, Types, Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    InitialMasks,
    InitialVectorBase

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    memmap,     \* Current memory map (set of MemRegionRecord)
    iomap,      \* Current I/O map (function PortSet -> IOHandler)
    trace       \* Trace of operations for verification

vars == <<memmap, iomap, trace>>

\* =====================================================================
\* TYPE INVARIANTS
\* =====================================================================

TypeOK ==
    /\ MemMapWellFormed(memmap)
    /\ SingleHandlerPerPort(iomap)
    /\ trace \in Seq([op: {"MEM_READ", "MEM_WRITE", "IO_READ", "IO_WRITE"},
                      addr: MemAddr \cup PortSet,
                      handler: MemRegion \cup IOHandler])

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

\* Memory ranges must not overlap
MemRangesDisjoint == RangesDisjoint(memmap)

\* I/O ports have single handlers (trivially true for function)
IOHandlersUnique == SingleHandlerPerPort(iomap)

\* Routing is deterministic
RoutingIsDeterministic == RoutingDeterminism(memmap, iomap)

\* Combined safety invariant
SafetyInvariant == TypeOK /\ MemRangesDisjoint /\ IOHandlersUnique

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

\* Standard PC-compatible initialization
Init ==
    /\ memmap = StandardMemMap
    /\ iomap = StandardIOMap
    /\ trace = <<>>

\* Empty map initialization (for testing dynamic add)
EmptyInit ==
    /\ memmap = {}
    /\ iomap = [p \in PortSet |-> "NONE"]
    /\ trace = <<>>

\* =====================================================================
\* ACTIONS
\* =====================================================================

(*
 * MemReadAction - Perform a memory read
 *)
MemReadAction(addr) ==
    LET handler == MemRead(memmap, addr)
    IN /\ trace' = Append(trace, [op |-> "MEM_READ", addr |-> addr, handler |-> handler])
       /\ UNCHANGED <<memmap, iomap>>

(*
 * MemWriteAction - Perform a memory write
 *)
MemWriteAction(addr) ==
    LET handler == MemWrite(memmap, addr)
    IN /\ trace' = Append(trace, [op |-> "MEM_WRITE", addr |-> addr, handler |-> handler])
       /\ UNCHANGED <<memmap, iomap>>

(*
 * IOReadAction - Perform an I/O port read
 *)
IOReadAction(port) ==
    LET handler == IORead(iomap, port)
    IN /\ trace' = Append(trace, [op |-> "IO_READ", addr |-> port, handler |-> handler])
       /\ UNCHANGED <<memmap, iomap>>

(*
 * IOWriteAction - Perform an I/O port write
 *)
IOWriteAction(port) ==
    LET handler == IOWrite(iomap, port)
    IN /\ trace' = Append(trace, [op |-> "IO_WRITE", addr |-> port, handler |-> handler])
       /\ UNCHANGED <<memmap, iomap>>

(*
 * AddRegionAction - Add a new memory region (non-overlapping)
 *)
AddRegionAction ==
    /\ Cardinality(memmap) < MaxMemRegions
    /\ \E lo \in MemAddr, hi \in MemAddr, h \in MemRegion :
        /\ lo <= hi
        /\ LET newRegion == [lo |-> lo, hi |-> hi, handler |-> h, priority |-> 0]
           IN /\ \A r \in memmap : ~RangesOverlap(r, newRegion)
              /\ memmap' = memmap \cup {newRegion}
              /\ UNCHANGED <<iomap, trace>>

(*
 * RemapPortAction - Change an I/O port handler
 *)
RemapPortAction ==
    \E p \in PortSet, h \in IOHandler :
        /\ iomap' = RemapIOPort(iomap, p, h)
        /\ UNCHANGED <<memmap, trace>>

(*
 * Idle - No operation
 *)
Idle == UNCHANGED vars

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================

Next ==
    \/ \E addr \in 0..100 : MemReadAction(addr)   \* Bounded for TLC
    \/ \E addr \in 0..100 : MemWriteAction(addr)
    \/ \E port \in PortSet : IOReadAction(port)
    \/ \E port \in PortSet : IOWriteAction(port)
    \/ AddRegionAction
    \/ RemapPortAction
    \/ Idle

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars

\* =====================================================================
\* ROUTING VERIFICATION PROPERTIES
\* =====================================================================

(*
 * CorrectRAMRouting - RAM addresses route to RAM handler
 *)
CorrectRAMRouting ==
    \A addr \in 0..100 :  \* First 100 addresses should be RAM
        FindMemHandler(memmap, addr) = "RAM"

(*
 * CorrectVGARouting - VGA addresses route to VGA handler
 *)
CorrectVGARouting ==
    \A addr \in 640..700 :  \* VGA window
        FindMemHandler(memmap, addr) = "VGA"

(*
 * CorrectPICRouting - PIC ports route to PIC handler
 *)
CorrectPICRouting ==
    /\ IORead(iomap, 32) = "PIC"   \* 0x20
    /\ IORead(iomap, 33) = "PIC"   \* 0x21
    /\ IORead(iomap, 160) = "PIC"  \* 0xA0
    /\ IORead(iomap, 161) = "PIC"  \* 0xA1

(*
 * CorrectPITRouting - PIT ports route to PIT handler
 *)
CorrectPITRouting ==
    /\ IORead(iomap, 64) = "PIT"   \* 0x40
    /\ IORead(iomap, 65) = "PIT"   \* 0x41
    /\ IORead(iomap, 66) = "PIT"   \* 0x42
    /\ IORead(iomap, 67) = "PIT"   \* 0x43

\* =====================================================================
\* SCENARIO: DISJOINT RANGES
\* =====================================================================

(*
 * DisjointRangesInit - Initialize with standard map
 * Verify that standard map has no overlaps
 *)
DisjointRangesInit == Init

(*
 * DisjointRangesCorrect - Standard map is disjoint
 *)
DisjointRangesCorrect == RangesDisjoint(StandardMemMap)

\* =====================================================================
\* SCENARIO: DYNAMIC REMAP
\* =====================================================================

(*
 * DynamicRemapInit - Start with empty map
 *)
DynamicRemapInit == EmptyInit

(*
 * AfterRemap - After remapping, the new handler is used
 *)
AfterRemapCorrect ==
    \A p \in PortSet, h \in IOHandler :
        IORead(RemapIOPort(iomap, p, h), p) = h

\* =====================================================================
\* HALMOS-STYLE LEMMAS (documented, not checked by TLC)
\* =====================================================================

(*
 * Lemma 1: MemRangesDisjoint => UniqueMemHandler(addr)
 *   If memory ranges don't overlap, each address has exactly one handler.
 *
 * Proof sketch:
 *   - RangesDisjoint means no two regions share any address
 *   - FindMemHandler returns the handler of the containing region
 *   - If disjoint, at most one region contains any address
 *   - Therefore, handler is unique (or UNMAPPED if none)
 *)

(*
 * Lemma 2: SingleHandlerIO => UniqueIOHandler(port)
 *   Each port maps to exactly one handler (trivial for functions).
 *
 * Proof sketch:
 *   - iomap is a function [PortSet -> IOHandler]
 *   - Functions are single-valued by definition
 *   - Therefore, iomap[p] is unique for each p
 *)

(*
 * Lemma 3: Ownership discipline
 *   Only the resolved handler's state changes on a bus op.
 *
 * Proof sketch:
 *   - BusMemOp routes addr to handler H
 *   - The Next relation for memory ops only modifies H's state
 *   - UNCHANGED clause ensures other handlers' state is preserved
 *   - Therefore, ownership is maintained
 *)

=======================================================================
