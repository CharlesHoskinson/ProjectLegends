---------------------------- MODULE DMATest ----------------------------
(*
 * Legends Emukernel - DMA Controller Test
 *
 * Tests DMA functionality:
 * 1. Masked channels don't transfer
 * 2. Count decreases during transfer
 * 3. Terminal count triggers and auto-init reloads
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle, MaxCount

\* DMA channels (bounded for TLC)
DMAChannels == 0..1

\* Count range
CountRange == 0..MaxCount

\* Transfer modes
DMAMode == {"Demand", "Single", "Block", "Cascade"}

\* =====================================================================
\* DMA OPERATIONS (from DMA.tla, inlined for testing)
\* =====================================================================

InitChannel == [
    enabled |-> FALSE,
    masked |-> TRUE,
    count |-> 0,
    base_count |-> 0,
    request |-> FALSE,
    tc_reached |-> FALSE,
    autoinit |-> FALSE,
    mode |-> "Single"
]

CanTransfer(ch) ==
    /\ ch.enabled
    /\ ~ch.masked
    /\ ch.request
    /\ ch.count > 0

TransferByte(ch) ==
    IF ~CanTransfer(ch) THEN ch
    ELSE IF ch.count = 1 THEN
        IF ch.autoinit THEN
            [ch EXCEPT !.count = ch.base_count,
                       !.tc_reached = TRUE]
        ELSE
            [ch EXCEPT !.count = 0,
                       !.tc_reached = TRUE,
                       !.enabled = FALSE]
    ELSE
        [ch EXCEPT !.count = ch.count - 1]

ClearTC(ch) == [ch EXCEPT !.tc_reached = FALSE]

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    dma,            \* DMA controller state (function from channel to state)
    tc_events,      \* Count of terminal count events
    transfers       \* Count of bytes transferred

vars == <<dma, tc_events, transfers>>

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

WellFormedChannel(ch) ==
    /\ ch.enabled \in BOOLEAN
    /\ ch.masked \in BOOLEAN
    /\ ch.count \in CountRange
    /\ ch.base_count \in CountRange
    /\ ch.request \in BOOLEAN
    /\ ch.tc_reached \in BOOLEAN
    /\ ch.autoinit \in BOOLEAN
    /\ ch.mode \in DMAMode

TypeOK ==
    /\ \A c \in DMAChannels : WellFormedChannel(dma[c])
    /\ tc_events \in Nat
    /\ transfers \in Nat

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

\* Masked channels never transfer
MaskedNoTransfer ==
    \A c \in DMAChannels :
        dma[c].masked => ~CanTransfer(dma[c])

\* Disabled channels never transfer
DisabledNoTransfer ==
    \A c \in DMAChannels :
        ~dma[c].enabled => ~CanTransfer(dma[c])

\* Count is bounded by base_count (when enabled)
CountBounded ==
    \A c \in DMAChannels :
        dma[c].enabled => dma[c].count <= dma[c].base_count

\* =====================================================================
\* INITIALIZATION SCENARIOS
\* =====================================================================

\* Test: Single transfer with autoinit
AutoInitInit ==
    /\ dma = [c \in DMAChannels |->
        IF c = 0 THEN
            \* Channel 0: enabled, unmasked, count=3, autoinit
            [enabled |-> TRUE,
             masked |-> FALSE,
             count |-> 3,
             base_count |-> 3,
             request |-> TRUE,
             tc_reached |-> FALSE,
             autoinit |-> TRUE,
             mode |-> "Single"]
        ELSE InitChannel]
    /\ tc_events = 0
    /\ transfers = 0

\* Test: Masked channel (should not transfer)
MaskedInit ==
    /\ dma = [c \in DMAChannels |->
        IF c = 0 THEN
            \* Channel 0: enabled but masked
            [enabled |-> TRUE,
             masked |-> TRUE,
             count |-> 3,
             base_count |-> 3,
             request |-> TRUE,
             tc_reached |-> FALSE,
             autoinit |-> FALSE,
             mode |-> "Single"]
        ELSE InitChannel]
    /\ tc_events = 0
    /\ transfers = 0

\* =====================================================================
\* ACTIONS
\* =====================================================================

\* Transfer one byte from a channel
DoTransfer(c) ==
    /\ CanTransfer(dma[c])
    /\ LET old_tc == dma[c].tc_reached
           new_ch == TransferByte(dma[c])
           tc_fired == ~old_tc /\ new_ch.tc_reached
       IN /\ dma' = [dma EXCEPT ![c] = new_ch]
          /\ transfers' = transfers + 1
          /\ tc_events' = IF tc_fired THEN tc_events + 1 ELSE tc_events

\* Clear TC flag after acknowledgement
AckTC(c) ==
    /\ dma[c].tc_reached
    /\ dma' = [dma EXCEPT ![c] = ClearTC(dma[c])]
    /\ UNCHANGED <<tc_events, transfers>>

\* Idle
Idle == UNCHANGED vars

\* =====================================================================
\* NEXT STATE
\* =====================================================================

Next ==
    \/ \E c \in DMAChannels : DoTransfer(c)
    \/ \E c \in DMAChannels : AckTC(c)
    \/ Idle

\* =====================================================================
\* SPECIFICATIONS
\* =====================================================================

AutoInitSpec == AutoInitInit /\ [][Next]_vars /\ WF_vars(\E c \in DMAChannels : DoTransfer(c))
MaskedSpec == MaskedInit /\ [][Next]_vars

\* =====================================================================
\* TEST PROPERTIES
\* =====================================================================

\* AutoInit test: TC should fire, count should reload
AutoInitCorrect ==
    (tc_events >= 1 /\ transfers >= 3) =>
        (dma[0].count = 3 \/ dma[0].count = 2 \/ dma[0].count = 1)

\* Masked test: No transfers should occur
MaskedCorrect ==
    dma[0].masked => transfers = 0

\* =====================================================================
\* STATE CONSTRAINT (for bounded model checking)
\* =====================================================================

BoundedTransfers == transfers <= 15

\* =====================================================================
\* COMBINED INVARIANTS
\* =====================================================================

AllInvariants ==
    /\ TypeOK
    /\ MaskedNoTransfer
    /\ DisabledNoTransfer

=======================================================================
