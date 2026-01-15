------------------------------ MODULE Bus ------------------------------
(*
 * Legends Emukernel - Bus Routing Specification
 *
 * This module specifies the memory and I/O bus routing semantics.
 * The bus is responsible for:
 * - Mapping memory addresses to handlers (RAM, VGA, ROM, devices)
 * - Mapping I/O ports to device handlers
 * - Enforcing ownership discipline (one handler per address/port)
 *
 * Key invariants:
 * - MemRangesDisjoint: No overlapping memory regions
 * - SingleHandlerIO: Each port has exactly one handler
 * - RoutingDeterminism: Same address always routes to same handler
 *
 * Design decisions:
 * - Memory map uses explicit ranges [lo, hi, handler]
 * - I/O map uses direct port -> handler function
 * - Dynamic remapping supported (e.g., VGA bank switching)
 *)
EXTENDS Types, Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    MaxCycle,
    MaxEvents,
    MaxMemRegions

\* =====================================================================
\* MEMORY MAP TYPES
\* =====================================================================

\* Memory address range (bounded for TLC)
\* Real x86 has 1MB in real mode, 4GB in protected mode
\* We use small bounds for model checking
MemAddr == 0..1023

\* Memory region record
\* lo, hi: Address range (inclusive)
\* handler: Device that handles this range
\* priority: For overlapping resolution (higher wins)
MemRegionRecord == { [lo |-> l, hi |-> h, handler |-> hnd, priority |-> p]
                     : l \in MemAddr, h \in MemAddr,
                       hnd \in MemRegion, p \in 0..10 }

\* =====================================================================
\* MEMORY MAP OPERATIONS
\* =====================================================================

(*
 * RangesOverlap(r1, r2) - Check if two ranges overlap
 *)
RangesOverlap(r1, r2) ==
    /\ r1.lo <= r2.hi
    /\ r2.lo <= r1.hi

(*
 * RangesDisjoint(regions) - All regions are non-overlapping
 *
 * This is a critical safety invariant. If regions overlap,
 * the routing becomes ambiguous (or priority-based).
 *)
RangesDisjoint(regions) ==
    \A r1, r2 \in regions :
        r1 # r2 => ~RangesOverlap(r1, r2)

(*
 * AddrInRange(addr, region) - Check if address is in region
 *)
AddrInRange(addr, region) ==
    /\ addr >= region.lo
    /\ addr <= region.hi

(*
 * FindMemHandler(regions, addr) - Find handler for address
 *
 * Returns the handler for the region containing addr.
 * If no region contains addr, returns "UNMAPPED".
 * If multiple regions (shouldn't happen with RangesDisjoint),
 * returns highest priority.
 *)
FindMemHandler(regions, addr) ==
    LET matching == {r \in regions : AddrInRange(addr, r)}
    IN IF matching = {}
       THEN "UNMAPPED"
       ELSE LET maxPri == CHOOSE p \in {r.priority : r \in matching} :
                            \A r \in matching : p >= r.priority
                winner == CHOOSE r \in matching : r.priority = maxPri
            IN winner.handler

(*
 * MemRead(regions, addr) - Read operation routing
 *
 * Returns the handler that should service this read.
 * The actual data transfer is handled by the device.
 *)
MemRead(regions, addr) == FindMemHandler(regions, addr)

(*
 * MemWrite(regions, addr) - Write operation routing
 *
 * Returns the handler that should service this write.
 *)
MemWrite(regions, addr) == FindMemHandler(regions, addr)

\* =====================================================================
\* I/O PORT OPERATIONS
\* =====================================================================

(*
 * IORead(iomap, port) - I/O port read routing
 *
 * Returns the handler for the given port.
 * iomap is a function [PortSet -> IOHandler].
 *)
IORead(iomap, port) ==
    IF port \in DOMAIN iomap
    THEN iomap[port]
    ELSE "NONE"

(*
 * IOWrite(iomap, port) - I/O port write routing
 *)
IOWrite(iomap, port) == IORead(iomap, port)

(*
 * SingleHandlerPerPort(iomap) - Each port has exactly one handler
 *
 * This is trivially true for a function, but we check anyway
 * to document the invariant.
 *)
SingleHandlerPerPort(iomap) ==
    \A p \in DOMAIN iomap : iomap[p] \in IOHandler

\* =====================================================================
\* STANDARD MEMORY MAP (IBM PC/AT compatible)
\* =====================================================================

(*
 * Standard PC memory layout (simplified for TLC bounds):
 *
 * Real layout:
 *   0x00000 - 0x9FFFF: Conventional RAM (640KB)
 *   0xA0000 - 0xBFFFF: VGA framebuffer (128KB)
 *   0xC0000 - 0xEFFFF: ROM/BIOS extensions
 *   0xF0000 - 0xFFFFF: System BIOS (64KB)
 *
 * Simplified for model checking (1KB total):
 *   0-639:    RAM
 *   640-767:  VGA
 *   768-895:  ROM
 *   896-1023: BIOS (also ROM)
 *)

StandardMemMap == {
    [lo |-> 0,   hi |-> 639, handler |-> "RAM", priority |-> 0],
    [lo |-> 640, hi |-> 767, handler |-> "VGA", priority |-> 0],
    [lo |-> 768, hi |-> 895, handler |-> "ROM", priority |-> 0],
    [lo |-> 896, hi |-> 1023, handler |-> "ROM", priority |-> 0]
}

(*
 * StandardIOMap - Standard PC I/O port assignments
 *
 * Key ports:
 *   0x20-0x21: Master PIC (8259A)
 *   0x40-0x43: PIT (8253/8254)
 *   0x60-0x64: Keyboard controller (8042)
 *   0xA0-0xA1: Slave PIC
 *   0x3D4-0x3D5: VGA CRTC
 *   etc.
 *)
StandardIOMap == [p \in PortSet |->
    CASE p \in {32, 33}         -> "PIC"    \* 0x20-0x21
      [] p \in {160, 161}       -> "PIC"    \* 0xA0-0xA1
      [] p \in {64, 65, 66, 67} -> "PIT"    \* 0x40-0x43
      [] p \in {96, 97}         -> "KBD"    \* 0x60-0x61
      [] OTHER                  -> "NONE"
]

\* =====================================================================
\* BUS INVARIANTS
\* =====================================================================

(*
 * MemMapWellFormed(regions) - Memory map validity
 *)
MemMapWellFormed(regions) ==
    /\ \A r \in regions : r \in MemRegionRecord
    /\ \A r \in regions : r.lo <= r.hi
    /\ Cardinality(regions) <= MaxMemRegions

(*
 * MemRangesDisjoint - No overlapping memory regions
 *
 * This is the key safety property for deterministic routing.
 *)
MemRangesDisjointInv(regions) == RangesDisjoint(regions)

(*
 * SingleHandlerIO - Each port maps to exactly one handler
 *)
SingleHandlerIOInv(iomap) == SingleHandlerPerPort(iomap)

(*
 * RoutingDeterminism - Same input always produces same output
 *
 * This is implicit in the functional nature of the operators,
 * but we make it explicit for documentation.
 *)
RoutingDeterminism(regions, iomap) ==
    \A addr \in MemAddr :
        LET h1 == FindMemHandler(regions, addr)
            h2 == FindMemHandler(regions, addr)
        IN h1 = h2

\* =====================================================================
\* OWNERSHIP DISCIPLINE
\* =====================================================================

(*
 * OwnershipLemma: Only the resolved handler's state changes on bus op
 *
 * This is a design principle rather than a checkable invariant.
 * When a bus operation targets address A:
 * 1. Route A to handler H
 * 2. Only H's state may change
 * 3. All other handlers' state must remain unchanged
 *
 * In TLA+, this is enforced by the Next relation structure:
 *   BusRead(addr) => LET H == FindHandler(addr)
 *                    IN H.HandleRead(addr) /\ UNCHANGED others
 *)

\* =====================================================================
\* DYNAMIC REMAPPING
\* =====================================================================

(*
 * AddMemRegion(regions, region) - Add a new memory region
 *
 * Used for dynamic mapping (e.g., loading ROM, EMS pages).
 * Must not overlap existing regions (or must have higher priority).
 *)
AddMemRegion(regions, region) ==
    IF \A r \in regions : ~RangesOverlap(r, region)
    THEN regions \cup {region}
    ELSE regions  \* Reject overlapping addition

(*
 * RemoveMemRegion(regions, lo, hi) - Remove region by range
 *)
RemoveMemRegion(regions, lo, hi) ==
    {r \in regions : ~(r.lo = lo /\ r.hi = hi)}

(*
 * RemapIOPort(iomap, port, handler) - Change port handler
 *)
RemapIOPort(iomap, port, handler) ==
    [iomap EXCEPT ![port] = handler]

\* =====================================================================
\* VGA BANK SWITCHING (Example of dynamic remapping)
\* =====================================================================

(*
 * VGA uses bank switching to access more than 64KB of video memory
 * through the 128KB window at 0xA0000-0xBFFFF.
 *
 * Model: VGA has internal bank register, window shows different
 * portions of VRAM based on bank setting.
 *
 * This is abstracted here - the handler is always "VGA", but
 * internally VGA uses bank register to determine actual VRAM offset.
 *)

\* Bank is a state variable in the VGA device, not in the bus.
\* The bus always routes 0xA0000-0xBFFFF to VGA.
\* VGA internally computes: actual_addr = (bank * 64KB) + (addr - 0xA0000)

\* =====================================================================
\* BUS OPERATIONS FOR EMUKERNEL
\* =====================================================================

(*
 * BusMemOp(memmap, addr, op) - Memory bus operation
 *
 * op is one of "READ", "WRITE"
 * Returns the handler to dispatch to.
 *)
BusMemOp(memmap, addr, op) ==
    CASE op = "READ"  -> MemRead(memmap, addr)
      [] op = "WRITE" -> MemWrite(memmap, addr)
      [] OTHER        -> "UNMAPPED"

(*
 * BusIOOp(iomap, port, op) - I/O bus operation
 *)
BusIOOp(iomap, port, op) ==
    CASE op = "READ"  -> IORead(iomap, port)
      [] op = "WRITE" -> IOWrite(iomap, port)
      [] OTHER        -> "NONE"

\* =====================================================================
\* TEST HELPERS
\* =====================================================================

(*
 * VerifyMemRouting(regions, tests) - Verify routing for test cases
 *
 * tests is a sequence of [addr |-> a, expected |-> h]
 *)
VerifyMemRouting(regions, tests) ==
    \A i \in 1..Len(tests) :
        FindMemHandler(regions, tests[i].addr) = tests[i].expected

(*
 * VerifyIORouting(iomap, tests) - Verify I/O routing
 *)
VerifyIORouting(iomap, tests) ==
    \A i \in 1..Len(tests) :
        IORead(iomap, tests[i].port) = tests[i].expected

=======================================================================
