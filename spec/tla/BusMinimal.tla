-------------------------- MODULE BusMinimal --------------------------
(*
 * Minimal Bus Routing Test
 *
 * Tests memory and I/O routing without full kernel state.
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxMemRegions

MemAddr == 0..1023
MemRegion == {"RAM", "VGA", "ROM", "UNMAPPED"}
PortSet == {32, 33, 64, 65, 66, 67, 96, 97, 160, 161}
IOHandler == {"PIC", "PIT", "KBD", "NONE"}

\* =====================================================================
\* MEMORY MAP OPERATIONS
\* =====================================================================

RangesOverlap(r1, r2) ==
    /\ r1.lo <= r2.hi
    /\ r2.lo <= r1.hi

RangesDisjoint(regions) ==
    \A r1, r2 \in regions :
        r1 # r2 => ~RangesOverlap(r1, r2)

AddrInRange(addr, region) ==
    addr >= region.lo /\ addr <= region.hi

MinSet(S) == CHOOSE x \in S : \A y \in S : x <= y

FindMemHandler(regions, addr) ==
    LET matching == {r \in regions : AddrInRange(addr, r)}
    IN IF matching = {}
       THEN "UNMAPPED"
       ELSE LET winner == CHOOSE r \in matching : TRUE
            IN winner.handler

IORead(iomap, port) ==
    IF port \in DOMAIN iomap THEN iomap[port] ELSE "NONE"

\* =====================================================================
\* STANDARD MAPS
\* =====================================================================

StandardMemMap == {
    [lo |-> 0,   hi |-> 639, handler |-> "RAM"],
    [lo |-> 640, hi |-> 767, handler |-> "VGA"],
    [lo |-> 768, hi |-> 895, handler |-> "ROM"],
    [lo |-> 896, hi |-> 1023, handler |-> "ROM"]
}

StandardIOMap == [p \in PortSet |->
    CASE p \in {32, 33}         -> "PIC"
      [] p \in {160, 161}       -> "PIC"
      [] p \in {64, 65, 66, 67} -> "PIT"
      [] p \in {96, 97}         -> "KBD"
      [] OTHER                  -> "NONE"
]

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES memmap, iomap

vars == <<memmap, iomap>>

\* =====================================================================
\* INVARIANTS
\* =====================================================================

TypeOK ==
    /\ \A r \in memmap : r.lo \in MemAddr /\ r.hi \in MemAddr /\ r.handler \in MemRegion
    /\ Cardinality(memmap) <= MaxMemRegions
    /\ \A p \in PortSet : iomap[p] \in IOHandler

\* Memory ranges must not overlap
MemRangesDisjoint == RangesDisjoint(memmap)

\* Correct routing for RAM
CorrectRAMRouting == \A addr \in 0..100 : FindMemHandler(memmap, addr) = "RAM"

\* Correct routing for VGA
CorrectVGARouting == \A addr \in 640..700 : FindMemHandler(memmap, addr) = "VGA"

\* Correct PIC routing
CorrectPICRouting ==
    /\ IORead(iomap, 32) = "PIC"
    /\ IORead(iomap, 33) = "PIC"
    /\ IORead(iomap, 160) = "PIC"
    /\ IORead(iomap, 161) = "PIC"

\* Correct PIT routing
CorrectPITRouting ==
    /\ IORead(iomap, 64) = "PIT"
    /\ IORead(iomap, 65) = "PIT"
    /\ IORead(iomap, 66) = "PIT"
    /\ IORead(iomap, 67) = "PIT"

\* All invariants
AllInvariants ==
    /\ TypeOK
    /\ MemRangesDisjoint
    /\ CorrectRAMRouting
    /\ CorrectVGARouting
    /\ CorrectPICRouting
    /\ CorrectPITRouting

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

Init ==
    /\ memmap = StandardMemMap
    /\ iomap = StandardIOMap

\* =====================================================================
\* NEXT (no changes - just verify initial state)
\* =====================================================================

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

=======================================================================
