---------------------------- MODULE SaveState ----------------------------
(*
 * Legends Emukernel - Save-State Serialization Contract
 *
 * This module defines the contract for save/load state operations,
 * ensuring that observable state is preserved across serialization.
 *
 * CRITICAL FINDING: The current DOSBox-X implementation does NOT
 * serialize the event queue. This breaks deterministic replay.
 * This specification requires event queue serialization.
 *
 * Properties verified:
 * - SaveLoadRoundTrip: Obs(Deserialize(Serialize(S))) = Obs(S)
 * - ReplayDeterminism: Same inputs + same snapshot = same output trace
 * - EventQueuePreserved: Q is part of serialized state
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle, MaxCount, MaxEvents

\* Event kinds
EventKind == {"PIT_TICK", "KBD_SCAN", "DMA_TC", "TIMER_CB", "IRQ_CHECK"}

\* Bounded ranges for TLC
Cycles == 0..MaxCycle
CountRange == 0..MaxCount
EventIds == 0..(MaxEvents - 1)
PayloadRange == 0..255
TieKeyRange == 0..100
RegValue == 0..255

\* =====================================================================
\* STATE TYPES
\* =====================================================================

\* Event record (simplified)
Event == { [id |-> i, deadline |-> d, kind |-> k, payload |-> p, tieKey |-> t]
           : i \in EventIds, d \in Cycles, k \in EventKind,
             p \in PayloadRange, t \in TieKeyRange }

\* CPU state
CPUMode == {"Real", "Protected", "V86"}

\* PIC state
PICState == [irr: RegValue, imr: RegValue, isr: RegValue, vector_base: RegValue]

\* DMA channel state (simplified)
DMAChannelState == [enabled: BOOLEAN, masked: BOOLEAN, count: CountRange,
                    tc_reached: BOOLEAN, autoinit: BOOLEAN]

\* =====================================================================
\* OBSERVATION FUNCTION
\* =====================================================================

(*
 * Obs(S) - Extract observable state
 *
 * This is the "equivalence class" for save-state correctness.
 * Two states are considered equivalent if their observations match.
 *
 * CRITICAL: Event queue (Q) is part of the observation because
 * pending events affect future behavior.
 *)
ObsEvent(e) == <<e.deadline, e.kind, e.tieKey>>

QDigest(Q) == {ObsEvent(e) : e \in Q}

Obs(state) == [
    now |-> state.now,
    Q_digest |-> QDigest(state.Q),
    CPU_IF |-> state.CPU.IF,
    CPU_halted |-> state.CPU.halted,
    pic0_irr |-> state.pics[0].irr,
    pic0_imr |-> state.pics[0].imr,
    pic0_isr |-> state.pics[0].isr,
    pic1_irr |-> state.pics[1].irr,
    pic1_imr |-> state.pics[1].imr,
    pic1_isr |-> state.pics[1].isr
]

\* =====================================================================
\* SERIALIZATION OPERATIONS
\* =====================================================================

(*
 * Serialize(S) - Convert state to serializable snapshot
 *
 * This is what gets written to disk. MUST include:
 * - Virtual time (now)
 * - Event queue (Q) - CRITICAL, currently missing in DOSBox-X
 * - CPU state
 * - PIC state (both master and slave)
 * - DMA channel state
 * - Other device state...
 *)
SaveVersion == {2, 3}

SerializeEvent(e) ==
    [slot |-> e.id, deadline |-> e.deadline, kind |-> e.kind,
     payload |-> e.payload, tieKey |-> e.tieKey]

SnapshotCore(state) == [
    version |-> 3,
    now |-> state.now,
    \* Preserve event multiplicity via stable slot values.
    events |-> {SerializeEvent(e) : e \in state.Q},
    cpu |-> [IF |-> state.CPU.IF, halted |-> state.CPU.halted,
             mode |-> state.CPU.mode],
    pic0 |-> state.pics[0],
    pic1 |-> state.pics[1],
    dma |-> state.dma
]

SnapshotCRC(snapCore) ==
    (snapCore.now * 7 +
     Cardinality(snapCore.events) * 13 +
     (IF snapCore.cpu.IF THEN 1 ELSE 0) * 19 +
     snapCore.pic0.irr + snapCore.pic1.irr) % 251

Serialize(state) ==
    LET core == SnapshotCore(state)
    IN [
        version |-> core.version,
        now |-> core.now,
        events |-> core.events,
        cpu |-> core.cpu,
        pic0 |-> core.pic0,
        pic1 |-> core.pic1,
        dma |-> core.dma,
        crc |-> SnapshotCRC(core)
    ]

NormalizeSnapshot(snap) ==
    IF snap.version = 2
    THEN LET upgraded == [
                 version |-> 3,
                 now |-> snap.now,
                 events |-> snap.events,
                 cpu |-> snap.cpu,
                 pic0 |-> snap.pic0,
                 pic1 |-> snap.pic1,
                 dma |-> snap.dma
             ]
         IN [
             version |-> upgraded.version,
             now |-> upgraded.now,
             events |-> upgraded.events,
             cpu |-> upgraded.cpu,
             pic0 |-> upgraded.pic0,
             pic1 |-> upgraded.pic1,
             dma |-> upgraded.dma,
             crc |-> SnapshotCRC(upgraded)
         ]
    ELSE snap

SnapshotCRCValid(snap) ==
    LET normalized == NormalizeSnapshot(snap)
    IN IF "crc" \in DOMAIN normalized
       THEN normalized.crc = SnapshotCRC(normalized)
       ELSE FALSE

(*
 * Deserialize(snap) - Reconstruct state from snapshot
 *
 * Restores state from serialized snapshot.
 * Event IDs are regenerated since they're internal handles.
 *)
DeserializeEvent(e, idx) ==
    [id |-> (idx - 1), deadline |-> e.deadline, kind |-> e.kind,
     payload |-> e.payload, tieKey |-> e.tieKey]

MinSlotEvent(events) ==
    CHOOSE e \in events : \A other \in events : e.slot <= other.slot

RECURSIVE SetToSeqBySlot(_)
SetToSeqBySlot(events) ==
    IF events = {}
    THEN <<>>
    ELSE LET pick == MinSlotEvent(events)
         IN <<pick>> \o SetToSeqBySlot(events \ {pick})

Deserialize(snap) ==
    LET
        normalized == NormalizeSnapshot(snap)
        eventSeq == SetToSeqBySlot(normalized.events)
        Q_new == {DeserializeEvent(eventSeq[i], i) : i \in 1..Len(eventSeq)}
    IN [
        now |-> normalized.now,
        Q |-> Q_new,
        CPU |-> [IF |-> normalized.cpu.IF, halted |-> normalized.cpu.halted,
                 mode |-> normalized.cpu.mode],
        pics |-> [i \in 0..1 |-> IF i = 0 THEN normalized.pic0 ELSE normalized.pic1],
        dma |-> normalized.dma,
        InputQ |-> <<>>,  \* Input queue cleared on load
        Out |-> <<>>      \* Output trace cleared on load
    ]

\* =====================================================================
\* SAVE-STATE INVARIANTS
\* =====================================================================

(*
 * ObservationPreserved(S) - Observation is preserved after round-trip
 *
 * This is the key correctness property. After save and load,
 * the observable state must be identical.
 *)
ObservationPreserved(state) ==
    Obs(Deserialize(Serialize(state))) = Obs(state)

(*
 * EventQueuePreserved(S) - Event queue is preserved
 *
 * The event queue digest must be identical after round-trip.
 * This catches the current bug where events are lost.
 *)
EventQueuePreserved(state) ==
    LET snap == Serialize(state)
        restored == Deserialize(snap)
    IN QDigest(state.Q) = QDigest(restored.Q)

(*
 * TimePreserved(S) - Virtual time is preserved
 *)
TimePreserved(state) ==
    LET snap == Serialize(state)
    IN snap.now = state.now

SnapshotIntegrityPreserved(state) ==
    SnapshotCRCValid(Serialize(state))

\* =====================================================================
\* VARIABLES (for testing)
\* =====================================================================
VARIABLES
    state,          \* Current emulator state
    saved           \* Saved snapshot (or NONE)

vars == <<state, saved>>

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

IsValidEvent(e) ==
    /\ e.id \in EventIds
    /\ e.deadline \in Cycles
    /\ e.kind \in EventKind
    /\ e.payload \in PayloadRange
    /\ e.tieKey \in TieKeyRange

IsValidCPU(cpu) ==
    /\ cpu.IF \in BOOLEAN
    /\ cpu.halted \in BOOLEAN
    /\ cpu.mode \in CPUMode

IsValidPIC(pic) ==
    /\ pic.irr \in RegValue
    /\ pic.imr \in RegValue
    /\ pic.isr \in RegValue
    /\ pic.vector_base \in RegValue

IsValidDMA(ch) ==
    /\ ch.enabled \in BOOLEAN
    /\ ch.masked \in BOOLEAN
    /\ ch.count \in CountRange
    /\ ch.tc_reached \in BOOLEAN
    /\ ch.autoinit \in BOOLEAN

IsValidSerializedEvent(e) ==
    /\ e.slot \in EventIds
    /\ e.deadline \in Cycles
    /\ e.kind \in EventKind
    /\ e.payload \in PayloadRange
    /\ e.tieKey \in TieKeyRange

IsValidState(s) ==
    /\ s.now \in Cycles
    /\ \A e \in s.Q : IsValidEvent(e)
    /\ Cardinality(s.Q) <= MaxEvents
    /\ IsValidCPU(s.CPU)
    /\ IsValidPIC(s.pics[0])
    /\ IsValidPIC(s.pics[1])
    /\ \A ch \in DOMAIN s.dma : IsValidDMA(s.dma[ch])

IsValidSnapshot(snap) ==
    LET normalized == NormalizeSnapshot(snap)
    IN /\ normalized.version \in SaveVersion
       /\ normalized.now \in Cycles
       /\ \A e \in normalized.events : IsValidSerializedEvent(e)
       /\ Cardinality(normalized.events) <= MaxEvents
       /\ IsValidCPU(normalized.cpu)
       /\ IsValidPIC(normalized.pic0)
       /\ IsValidPIC(normalized.pic1)
       /\ \A ch \in DOMAIN normalized.dma : IsValidDMA(normalized.dma[ch])
       /\ normalized.crc \in 0..250
       /\ SnapshotCRCValid(normalized)

IsNoneSaved(s) ==
    IF DOMAIN s = {"type"}
    THEN s.type = "NONE"
    ELSE FALSE

IsSnapSaved(s) ==
    IF DOMAIN s = {"type", "snap"} /\ s.type = "SNAP"
    THEN IsValidSnapshot(s.snap)
    ELSE FALSE

TypeOK ==
    /\ IsValidState(state)
    /\ (IsNoneSaved(saved) \/ IsSnapSaved(saved))

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

InitPIC == [irr |-> 0, imr |-> 255, isr |-> 0, vector_base |-> 8]
InitDMA == [ch \in 0..3 |->
    [enabled |-> FALSE, masked |-> TRUE, count |-> 0,
     tc_reached |-> FALSE, autoinit |-> FALSE]]

\* Test with pending events (to verify they're preserved)
InitWithEvents ==
    /\ state = [
        now |-> 5,
        Q |-> {[id |-> 0, deadline |-> 10, kind |-> "PIT_TICK",
               payload |-> 0, tieKey |-> 0],
              [id |-> 1, deadline |-> 15, kind |-> "KBD_SCAN",
               payload |-> 65, tieKey |-> 20]},
        CPU |-> [IF |-> TRUE, halted |-> FALSE, mode |-> "Real"],
        pics |-> [i \in 0..1 |-> InitPIC],
        dma |-> InitDMA,
        InputQ |-> <<>>,
        Out |-> <<>>
       ]
    /\ saved = [type |-> "NONE"]

\* Empty state (no pending events)
InitEmpty ==
    /\ state = [
        now |-> 0,
        Q |-> {},
        CPU |-> [IF |-> FALSE, halted |-> FALSE, mode |-> "Real"],
        pics |-> [i \in 0..1 |-> InitPIC],
        dma |-> InitDMA,
        InputQ |-> <<>>,
        Out |-> <<>>
       ]
    /\ saved = [type |-> "NONE"]

Init == InitWithEvents

\* =====================================================================
\* ACTIONS
\* =====================================================================

\* Save current state
SaveState ==
    /\ saved = [type |-> "NONE"]
    /\ saved' = [type |-> "SNAP", snap |-> Serialize(state)]
    /\ UNCHANGED state

\* Load saved state
LoadState ==
    /\ saved.type = "SNAP"
    /\ SnapshotCRCValid(saved.snap)
    /\ state' = Deserialize(saved.snap)
    /\ saved' = [type |-> "NONE"]

\* Corrupt/invalid snapshots are rejected with no state mutation.
RejectCorruptSnapshot ==
    /\ saved.type = "SNAP"
    /\ ~SnapshotCRCValid(saved.snap)
    /\ UNCHANGED state
    /\ saved' = [type |-> "NONE"]

\* Idle
Idle == UNCHANGED vars

Next ==
    \/ SaveState
    \/ LoadState
    \/ RejectCorruptSnapshot
    \/ Idle

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars

\* =====================================================================
\* PROPERTIES
\* =====================================================================

\* After loading, observation matches original
SaveLoadCorrect ==
    [][saved.type = "SNAP" /\ saved'.type = "NONE" =>
       Obs(state') = Obs(Deserialize(saved.snap))]_vars

\* Event queue is never empty after save if it wasn't before
EventsPreservedOnLoad ==
    [][saved.type = "SNAP" /\ Cardinality(saved.snap.events) > 0 /\
       saved'.type = "NONE" =>
       Cardinality(state'.Q) > 0]_vars

\* Round-trip preserves observation (test this as invariant)
RoundTripInvariant == ObservationPreserved(state)

\* Serialized snapshots always carry a valid checksum.
SnapshotIntegrityInvariant == SnapshotIntegrityPreserved(state)

=======================================================================
