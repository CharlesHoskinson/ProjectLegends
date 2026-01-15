------------------------ MODULE SchedulerTest ------------------------
(*
 * Legends Emukernel - Scheduler Test Harness
 *
 * This module provides a standalone test harness for verifying
 * the Scheduler module's properties. It defines a minimal state
 * machine focused on scheduler operations.
 *
 * Test scenarios:
 * 1. TieBreak - Multiple events with same deadline, verify ordering
 * 2. Cancel - Schedule then cancel events, verify removal
 * 3. TimeAdvance - Verify time jumps to next event deadline
 *)
EXTENDS Scheduler, Types, Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    InitialMasks,       \* Unused but required by Types
    InitialVectorBase   \* Unused but required by Types

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    now,        \* Current virtual time
    Q,          \* Event queue
    processed,  \* Sequence of processed event IDs (for verification)
    nextId      \* Next event ID to assign

vars == <<now, Q, processed, nextId>>

\* =====================================================================
\* TYPE INVARIANTS
\* =====================================================================

TypeOK ==
    /\ now \in Cycles
    /\ QueueWellFormed(Q)
    /\ processed \in Seq(EventIds)
    /\ nextId \in EventIds \cup {MaxEvents}

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

\* No event should be scheduled in the past
EventsNotInPast == \A e \in Q : e.deadline >= now

\* Time must be monotonic (checked as action property)
MonotonicTime == now' >= now

\* Combined invariant
SafetyInvariant == TypeOK /\ EventsNotInPast

\* =====================================================================
\* DETERMINISM INVARIANT
\* =====================================================================

\* Selection must be deterministic for all reachable states
SelectionDeterministic ==
    DueEvents(Q, now) # {} => DeterministicSelection(Q, now)

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

Init ==
    /\ now = 0
    /\ Q = {}
    /\ processed = <<>>
    /\ nextId = 0

\* =====================================================================
\* ACTIONS
\* =====================================================================

(*
 * ScheduleEvent - Add a new event to the queue
 *
 * Nondeterministically chooses deadline, kind, and payload.
 * TieKey is assigned based on event kind.
 *)
ScheduleEvent ==
    /\ nextId < MaxEvents
    /\ Cardinality(Q) < MaxEvents
    /\ \E deadline \in now..(now + 5),
          kind \in EventKind,
          payload \in 0..3 :
        LET e == MakeEvent(nextId, deadline, kind, payload)
        IN /\ Q' = Schedule(Q, e)
           /\ nextId' = nextId + 1
    /\ UNCHANGED <<now, processed>>

(*
 * ScheduleMultipleSameDeadline - Add multiple events at same deadline
 *
 * This specifically tests tie-breaking behavior.
 *)
ScheduleMultipleSameDeadline ==
    /\ nextId + 2 < MaxEvents
    /\ Cardinality(Q) + 2 < MaxEvents
    /\ \E deadline \in now..(now + 3) :
        LET e1 == MakeEventWithTieKey(nextId, deadline, "TIMER_CB", 1, 40)
            e2 == MakeEventWithTieKey(nextId + 1, deadline, "PIT_TICK", 2, 0)
            e3 == MakeEventWithTieKey(nextId + 2, deadline, "KBD_SCAN", 3, 20)
        IN /\ Q' = Q \cup {e1, e2, e3}
           /\ nextId' = nextId + 3
    /\ UNCHANGED <<now, processed>>

(*
 * ProcessEvent - Process the next due event
 *)
ProcessEvent ==
    LET result == PopNextEvent(Q, now)
    IN /\ result.found
       /\ Q' = result.Q_new
       /\ processed' = Append(processed, result.event.id)
       /\ UNCHANGED <<now, nextId>>

(*
 * CancelEvent - Cancel an event by ID
 *)
CancelEventAction ==
    /\ Q # {}
    /\ \E e \in Q :
        /\ Q' = Cancel(Q, e.id)
        /\ UNCHANGED <<now, processed, nextId>>

(*
 * AdvanceTime - Move time forward
 *)
AdvanceTime ==
    /\ DueEvents(Q, now) = {}  \* No events to process
    /\ now < MaxCycle
    /\ now' = TimeStep(Q, now)
    /\ UNCHANGED <<Q, processed, nextId>>

(*
 * Idle - System is idle (no events, at max time)
 *)
Idle ==
    /\ Q = {}
    /\ now = MaxCycle
    /\ UNCHANGED vars

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================

Next ==
    \/ ScheduleEvent
    \/ ScheduleMultipleSameDeadline
    \/ ProcessEvent
    \/ CancelEventAction
    \/ AdvanceTime
    \/ Idle

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

\* Weak fairness ensures progress
Spec == Init /\ [][Next]_vars /\ WF_vars(ProcessEvent) /\ WF_vars(AdvanceTime)

\* =====================================================================
\* LIVENESS PROPERTIES
\* =====================================================================

\* Time will eventually progress
TimeProgresses == <>(now > 0)

\* Events will eventually be processed (if any are scheduled)
EventsProcessed == [](Q # {} => <>(processed # <<>>))

\* =====================================================================
\* TIE-BREAK VERIFICATION
\* =====================================================================

(*
 * TieBreakCorrect - When multiple events have same deadline,
 * lower tieKey is processed first.
 *
 * This is verified by examining the `processed` sequence.
 * If events e1, e2 have same deadline and e1.tieKey < e2.tieKey,
 * then e1's ID appears before e2's ID in `processed`.
 *)

\* Helper: Get event by ID from a set
GetEventById(events, id) ==
    CHOOSE e \in events : e.id = id

\* =====================================================================
\* SCENARIOS FOR TLC
\* =====================================================================

(*
 * Scenario: TieBreak
 *
 * Initial state has 3 events at deadline 5 with different tieKeys:
 *   Event 0: tieKey=40 (TIMER_CB)
 *   Event 1: tieKey=0  (PIT_TICK)  <- Should be first
 *   Event 2: tieKey=20 (KBD_SCAN)
 *
 * Expected processing order: 1, 2, 0
 *)
TieBreakInit ==
    /\ now = 0
    /\ Q = { [id |-> 0, deadline |-> 5, kind |-> "TIMER_CB", payload |-> 0, tieKey |-> 40],
             [id |-> 1, deadline |-> 5, kind |-> "PIT_TICK", payload |-> 0, tieKey |-> 0],
             [id |-> 2, deadline |-> 5, kind |-> "KBD_SCAN", payload |-> 0, tieKey |-> 20] }
    /\ processed = <<>>
    /\ nextId = 3

\* Verify: After processing all 3, order should be 1, 2, 0
TieBreakCorrect ==
    (Len(processed) = 3) => (processed = <<1, 2, 0>>)

(*
 * Scenario: Cancel
 *
 * Initial state has 2 events. We cancel one before its deadline.
 * Only the remaining event should be processed.
 *)
CancelInit ==
    /\ now = 0
    /\ Q = { [id |-> 0, deadline |-> 5, kind |-> "TIMER_CB", payload |-> 0, tieKey |-> 40],
             [id |-> 1, deadline |-> 10, kind |-> "PIT_TICK", payload |-> 0, tieKey |-> 0] }
    /\ processed = <<>>
    /\ nextId = 2

\* After canceling event 0, only event 1 should be processed
CancelCorrect ==
    (0 \notin {e.id : e \in Q} /\ Len(processed) > 0) =>
        (processed[1] = 1)

(*
 * Scenario: TimeJump
 *
 * Verify that time jumps directly to next event deadline
 * instead of incrementing by 1 each step.
 *)
TimeJumpInit ==
    /\ now = 0
    /\ Q = { [id |-> 0, deadline |-> 10, kind |-> "TIMER_CB", payload |-> 0, tieKey |-> 40] }
    /\ processed = <<>>
    /\ nextId = 1

\* After one time step with no due events, now should jump to 10
TimeJumpCorrect ==
    (Q # {} /\ DueEvents(Q, now) = {}) =>
        (TimeStep(Q, now) = 10)

=======================================================================
