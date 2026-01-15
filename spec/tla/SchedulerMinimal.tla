------------------------ MODULE SchedulerMinimal ------------------------
(*
 * Minimal Scheduler Test - No environmental nondeterminism
 *
 * This stripped-down spec tests scheduler properties without
 * the state space explosion from input queues and device state.
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle, MaxEvents

Cycles == 0..MaxCycle
EventIds == 0..(MaxEvents - 1)
EventKind == {"PIT_TICK", "TIMER_CB", "KBD_SCAN"}
TieKeyRange == 0..50

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    now,        \* Current time
    Q,          \* Event queue (set of records)
    processed   \* Sequence of processed event IDs

vars == <<now, Q, processed>>

\* =====================================================================
\* HELPERS
\* =====================================================================

MinSet(S) == CHOOSE x \in S : \A y \in S : x <= y

IsValidEvent(e) ==
    /\ e.id \in EventIds
    /\ e.deadline \in Cycles
    /\ e.kind \in EventKind
    /\ e.tieKey \in TieKeyRange

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

TypeOK ==
    /\ now \in Cycles
    /\ \A e \in Q : IsValidEvent(e)
    /\ Cardinality(Q) <= MaxEvents
    /\ processed \in Seq(EventIds)
    /\ Len(processed) <= MaxEvents

\* =====================================================================
\* SCHEDULER LOGIC
\* =====================================================================

DueEvents == {e \in Q : e.deadline <= now}

SelectNext ==
    IF DueEvents = {} THEN [found |-> FALSE]
    ELSE LET minD == MinSet({e.deadline : e \in DueEvents})
             atMinD == {e \in DueEvents : e.deadline = minD}
             minT == MinSet({e.tieKey : e \in atMinD})
             winner == CHOOSE e \in atMinD : e.tieKey = minT
         IN [found |-> TRUE, event |-> winner]

\* Selection is deterministic
SelectionDeterministic ==
    DueEvents # {} =>
    LET minD == MinSet({e.deadline : e \in DueEvents})
        atMinD == {e \in DueEvents : e.deadline = minD}
        minT == MinSet({e.tieKey : e \in atMinD})
    IN Cardinality({e \in atMinD : e.tieKey = minT}) = 1

\* Events not in the past
EventsNotInPast == \A e \in Q : e.deadline >= now

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

Init ==
    /\ now = 0
    /\ Q = {}
    /\ processed = <<>>

\* Pre-loaded scenario for tie-break testing
TieBreakInit ==
    /\ now = 0
    /\ Q = { [id |-> 0, deadline |-> 3, kind |-> "TIMER_CB", tieKey |-> 40],
             [id |-> 1, deadline |-> 3, kind |-> "PIT_TICK", tieKey |-> 0],
             [id |-> 2, deadline |-> 3, kind |-> "KBD_SCAN", tieKey |-> 20] }
    /\ processed = <<>>

\* =====================================================================
\* ACTIONS
\* =====================================================================

\* Process a due event
ProcessEvent ==
    LET sel == SelectNext
    IN /\ sel.found
       /\ Q' = Q \ {sel.event}
       /\ processed' = Append(processed, sel.event.id)
       /\ UNCHANGED now

\* Advance time (only when no events due)
AdvanceTime ==
    /\ DueEvents = {}
    /\ Q # {}
    /\ now < MaxCycle
    /\ now' = MinSet({e.deadline : e \in Q})
    /\ UNCHANGED <<Q, processed>>

\* Tick time by 1 (when queue empty)
TickTime ==
    /\ Q = {}
    /\ now < MaxCycle
    /\ now' = now + 1
    /\ UNCHANGED <<Q, processed>>

\* Idle (finished)
Idle ==
    /\ Q = {}
    /\ now = MaxCycle
    /\ UNCHANGED vars

\* =====================================================================
\* NEXT STATE
\* =====================================================================

Next ==
    \/ ProcessEvent
    \/ AdvanceTime
    \/ TickTime
    \/ Idle

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars /\ WF_vars(ProcessEvent) /\ WF_vars(AdvanceTime)

TieBreakSpec == TieBreakInit /\ [][Next]_vars /\ WF_vars(ProcessEvent)

\* =====================================================================
\* PROPERTIES
\* =====================================================================

\* Tie-break correctness: IDs processed in order 1, 2, 0
TieBreakCorrect ==
    (Len(processed) = 3) => (processed = <<1, 2, 0>>)

\* All events eventually processed
EventsProcessed == <>(Q = {})

=======================================================================
