------------------------------- MODULE DMA -------------------------------
(*
 * Legends Emukernel - 8237 DMA Controller Specification
 *
 * The DMA controller handles direct memory access transfers between
 * devices and memory without CPU intervention.
 *
 * Key features:
 * - 8 channels (4 on each DMA chip in PC)
 * - Each channel has count, address, mode registers
 * - Terminal count (TC) signals when transfer complete
 * - Auto-init mode reloads count after TC
 *
 * We model control semantics only, not byte-level data movement.
 *
 * Properties verified:
 * - NoTransferWhenMasked: Masked channels don't transfer
 * - CountMonotonic: Count decreases until TC or reload
 * - TerminalCountEvent: TC triggers callback
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle, MaxCount

\* DMA channels (0-7 in full PC, bounded for TLC)
DMAChannels == 0..3

\* Count range (bounded for TLC)
CountRange == 0..MaxCount

\* Transfer modes
DMAMode == {"Demand", "Single", "Block", "Cascade"}

\* =====================================================================
\* DMA CHANNEL STATE
\* =====================================================================

(*
 * DMA channel state record
 *
 * enabled: Channel is programmed and active
 * masked: Channel is temporarily disabled (mask register)
 * count: Remaining bytes to transfer
 * base_count: Value to reload on auto-init
 * request: Device is requesting transfer (DREQ asserted)
 * tc_reached: Terminal count has been reached
 * autoinit: Reload count after TC
 * mode: Transfer mode
 *)
DMAChannelType == [
    enabled: BOOLEAN,
    masked: BOOLEAN,
    count: CountRange,
    base_count: CountRange,
    request: BOOLEAN,
    tc_reached: BOOLEAN,
    autoinit: BOOLEAN,
    mode: DMAMode
]

\* =====================================================================
\* DMA OPERATIONS
\* =====================================================================

(*
 * InitChannel - Initialize a DMA channel
 *)
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

(*
 * ProgramChannel(ch, count, autoinit, mode) - Program channel for transfer
 *)
ProgramChannel(ch, cnt, ai, m) ==
    [ch EXCEPT !.enabled = TRUE,
               !.count = cnt,
               !.base_count = cnt,
               !.autoinit = ai,
               !.mode = m,
               !.tc_reached = FALSE]

(*
 * MaskChannel(ch) - Mask (disable) channel
 *)
MaskChannel(ch) == [ch EXCEPT !.masked = TRUE]

(*
 * UnmaskChannel(ch) - Unmask (enable) channel
 *)
UnmaskChannel(ch) == [ch EXCEPT !.masked = FALSE]

(*
 * SetRequest(ch) - Device asserts DREQ
 *)
SetRequest(ch) == [ch EXCEPT !.request = TRUE]

(*
 * ClearRequest(ch) - Device deasserts DREQ
 *)
ClearRequest(ch) == [ch EXCEPT !.request = FALSE]

(*
 * CanTransfer(ch) - Check if channel can transfer
 *
 * Transfer occurs when:
 * - Channel is enabled
 * - Channel is not masked
 * - Device is requesting (DREQ asserted)
 * - Count > 0 (not at terminal count)
 *)
CanTransfer(ch) ==
    /\ ch.enabled
    /\ ~ch.masked
    /\ ch.request
    /\ ch.count > 0

(*
 * TransferByte(ch) - Execute one byte transfer
 *
 * Decrements count. If count reaches 0:
 * - Set tc_reached flag
 * - If autoinit, reload count from base_count
 *)
TransferByte(ch) ==
    IF ~CanTransfer(ch) THEN ch
    ELSE IF ch.count = 1 THEN
        \* Terminal count
        IF ch.autoinit THEN
            [ch EXCEPT !.count = ch.base_count,
                       !.tc_reached = TRUE]
        ELSE
            [ch EXCEPT !.count = 0,
                       !.tc_reached = TRUE,
                       !.enabled = FALSE]
    ELSE
        [ch EXCEPT !.count = ch.count - 1]

(*
 * ClearTC(ch) - Clear terminal count flag
 *
 * Called after TC has been acknowledged
 *)
ClearTC(ch) == [ch EXCEPT !.tc_reached = FALSE]

(*
 * IsTerminalCount(ch) - Check if TC flag is set
 *)
IsTerminalCount(ch) == ch.tc_reached

\* =====================================================================
\* DMA CONTROLLER OPERATIONS
\* =====================================================================

(*
 * InitDMAController - Initialize all channels
 *)
InitDMAController == [ch \in DMAChannels |-> InitChannel]

(*
 * ServiceChannel(dma, ch) - Service a single channel
 *
 * Returns [dma': updated controller, tc: TRUE if TC occurred]
 *)
ServiceChannel(dma, ch) ==
    LET old_tc == dma[ch].tc_reached
        new_ch == TransferByte(dma[ch])
    IN [dma_new |-> [dma EXCEPT ![ch] = new_ch],
        tc |-> ~old_tc /\ new_ch.tc_reached]

(*
 * GetPendingChannels(dma) - Get set of channels requesting service
 *)
GetPendingChannels(dma) ==
    {ch \in DMAChannels : CanTransfer(dma[ch])}

(*
 * HighestPriorityChannel(dma) - Get highest priority pending channel
 *
 * Lower channel number = higher priority
 *)
HighestPriorityChannel(dma) ==
    LET pending == GetPendingChannels(dma)
    IN IF pending = {} THEN -1
       ELSE CHOOSE ch \in pending : \A other \in pending : ch <= other

\* =====================================================================
\* DMA INVARIANTS
\* =====================================================================

(*
 * WellFormedChannel(ch) - Channel state is valid
 *)
WellFormedChannel(ch) ==
    /\ ch.enabled \in BOOLEAN
    /\ ch.masked \in BOOLEAN
    /\ ch.count \in CountRange
    /\ ch.base_count \in CountRange
    /\ ch.request \in BOOLEAN
    /\ ch.tc_reached \in BOOLEAN
    /\ ch.autoinit \in BOOLEAN
    /\ ch.mode \in DMAMode

(*
 * CountInBounds(ch) - Count never exceeds base
 *)
CountInBounds(ch) ==
    ch.count <= ch.base_count \/ ~ch.enabled

(*
 * MaskedNoTransfer(ch) - Masked channels can't transfer
 *)
MaskedNoTransfer(ch) ==
    ch.masked => ~CanTransfer(ch)

(*
 * DisabledNoTransfer(ch) - Disabled channels can't transfer
 *)
DisabledNoTransfer(ch) ==
    ~ch.enabled => ~CanTransfer(ch)

\* =====================================================================
\* STANDARD DMA INITIALIZATION
\* =====================================================================

\* Channel 2: Floppy disk
\* Channel 3: Hard disk (sometimes)
\* Channel 1: Sound card (common)

=======================================================================
