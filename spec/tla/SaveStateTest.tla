-------------------------- MODULE SaveStateTest --------------------------
(*
 * Legends Emukernel - Save-State Test
 *
 * Tests save/load round-trip preserves observable state.
 * CRITICAL: Verifies event queue is preserved (current bug fix).
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle, MaxEvents

\* Bounded ranges
Cycles == 0..MaxCycle
EventIds == 0..(MaxEvents - 1)
PayloadRange == 0..10
TieKeyRange == 0..50
RegValue == 0..255
EventKind == {"PIT_TICK", "KBD_SCAN", "DMA_TC"}

\* =====================================================================
\* OBSERVATION FUNCTION
\* =====================================================================

ObsEvent(e) == <<e.deadline, e.kind, e.tieKey>>

QDigest(Q) == {ObsEvent(e) : e \in Q}

Obs(s) == [
    now |-> s.now,
    Q_digest |-> QDigest(s.Q),
    cpu_if |-> s.cpu_if,
    pic_irr |-> s.pic_irr
]

\* =====================================================================
\* SERIALIZATION (Simplified)
\* =====================================================================

\* Helper to convert set to sequence (must be defined before use)
RECURSIVE SetToSeqRec(_)
SetToSeqRec(S) ==
    IF S = {} THEN <<>>
    ELSE LET min == CHOOSE x \in S : \A y \in S :
              (x.deadline < y.deadline) \/
              (x.deadline = y.deadline /\ x.tieKey <= y.tieKey)
         IN <<min>> \o SetToSeqRec(S \ {min})

SerializeEvent(e) == [deadline |-> e.deadline, kind |-> e.kind,
                      payload |-> e.payload, tieKey |-> e.tieKey]

Serialize(s) == [
    now |-> s.now,
    events |-> {SerializeEvent(e) : e \in s.Q},
    cpu_if |-> s.cpu_if,
    pic_irr |-> s.pic_irr
]

\* Deserialize with fresh IDs
DeserializeEvents(evts) ==
    LET evtSeq == SetToSeqRec(evts)
        n == Cardinality(evts)
    IN IF n = 0 THEN {}
       ELSE {[id |-> i, deadline |-> evtSeq[i+1].deadline,
              kind |-> evtSeq[i+1].kind,
              payload |-> evtSeq[i+1].payload,
              tieKey |-> evtSeq[i+1].tieKey]
             : i \in 0..(n-1)}

Deserialize(snap) == [
    now |-> snap.now,
    Q |-> DeserializeEvents(snap.events),
    cpu_if |-> snap.cpu_if,
    pic_irr |-> snap.pic_irr
]

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    state,          \* Current state
    has_snap,       \* TRUE if snapshot exists
    snap,           \* Saved snapshot
    has_loaded,     \* TRUE if loaded state exists
    loaded          \* Loaded state

vars == <<state, has_snap, snap, has_loaded, loaded>>

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

IsValidEvent(e) ==
    /\ e.id \in EventIds
    /\ e.deadline \in Cycles
    /\ e.kind \in EventKind
    /\ e.payload \in PayloadRange
    /\ e.tieKey \in TieKeyRange

IsValidState(s) ==
    /\ s.now \in Cycles
    /\ \A e \in s.Q : IsValidEvent(e)
    /\ Cardinality(s.Q) <= MaxEvents
    /\ s.cpu_if \in BOOLEAN
    /\ s.pic_irr \in RegValue

TypeOK ==
    /\ IsValidState(state)
    /\ has_snap \in BOOLEAN
    /\ has_loaded \in BOOLEAN

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

\* Dummy snapshot for initialization (never used until Save)
DummySnap == [now |-> 0, events |-> {}, cpu_if |-> FALSE, pic_irr |-> 0]

\* Dummy state for initialization (never used until Load)
DummyState == [now |-> 0, Q |-> {}, cpu_if |-> FALSE, pic_irr |-> 0]

\* Test with 2 pending events
Init ==
    /\ state = [
        now |-> 5,
        Q |-> {[id |-> 0, deadline |-> 10, kind |-> "PIT_TICK",
               payload |-> 0, tieKey |-> 0],
              [id |-> 1, deadline |-> 15, kind |-> "KBD_SCAN",
               payload |-> 5, tieKey |-> 20]},
        cpu_if |-> TRUE,
        pic_irr |-> 3
       ]
    /\ has_snap = FALSE
    /\ snap = DummySnap
    /\ has_loaded = FALSE
    /\ loaded = DummyState

\* =====================================================================
\* ACTIONS
\* =====================================================================

\* Save state
Save ==
    /\ ~has_snap
    /\ has_snap' = TRUE
    /\ snap' = Serialize(state)
    /\ UNCHANGED <<state, has_loaded, loaded>>

\* Load state
Load ==
    /\ has_snap
    /\ has_loaded' = TRUE
    /\ loaded' = Deserialize(snap)
    /\ UNCHANGED <<state, has_snap, snap>>

\* Check observation preserved
Verify ==
    /\ has_loaded
    /\ Obs(state) = Obs(loaded)
    /\ UNCHANGED vars

Idle == UNCHANGED vars

Next ==
    \/ Save
    \/ Load
    \/ Verify
    \/ Idle

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars /\ WF_vars(Save) /\ WF_vars(Load)

\* =====================================================================
\* PROPERTIES
\* =====================================================================

\* Key invariant: If loaded, observation matches original
ObservationPreserved ==
    has_loaded => Obs(loaded) = Obs(state)

\* Event count preserved
EventCountPreserved ==
    has_loaded => Cardinality(loaded.Q) = Cardinality(state.Q)

\* Time preserved
TimePreserved ==
    has_loaded => loaded.now = state.now

\* Event queue digest preserved (key test for the bug fix)
EventDigestPreserved ==
    has_loaded => QDigest(loaded.Q) = QDigest(state.Q)

=======================================================================
