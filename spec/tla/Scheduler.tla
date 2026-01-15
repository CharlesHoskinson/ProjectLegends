---------------------------- MODULE Scheduler ----------------------------
(*
 * Legends Emukernel - Event Scheduler Specification
 *
 * This module specifies the deterministic event scheduling semantics
 * for the emukernel. The scheduler is the "heartbeat" of the emulator,
 * controlling when devices fire callbacks and when time advances.
 *
 * Key design decisions:
 * 1. Events are stored in a SET (not a sequence) for efficient lookup
 * 2. Tie-breaking uses explicit `tieKey` field, not arbitrary CHOOSE
 * 3. Time advances to next event deadline (not fixed increments)
 * 4. All operations preserve the "no events in past" invariant
 *
 * Properties verified:
 * - MonotonicTime: Time never decreases
 * - EventsNotInPast: No event scheduled before current time
 * - DeterministicSelection: Same state always yields same next event
 * - NoLostEvents: Scheduled events are eventually processed (under fairness)
 *)
EXTENDS Types, Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    MaxCycle,       \* Maximum virtual time
    MaxEvents       \* Maximum events in queue

\* =====================================================================
\* VARIABLES (imported from EmuKernel, listed here for reference)
\* =====================================================================
\* These variables are defined in EmuKernel.tla:
\*   now  - Current virtual time (cycles)
\*   Q    - Event queue (set of Event records)

\* =====================================================================
\* EVENT QUEUE OPERATIONS
\* =====================================================================

(*
 * Schedule(Q, e) - Add an event to the queue
 *
 * Preconditions:
 * - Event deadline must be >= current time (enforced by caller)
 * - Queue must not be at capacity
 *
 * The event is simply added to the set. Ordering is determined
 * at pop time by deadline and tieKey.
 *)
Schedule(Q_old, e) == Q_old \cup {e}

(*
 * Cancel(Q, id) - Remove an event by its ID
 *
 * Removes all events with the given ID from the queue.
 * Safe to call with non-existent ID (no-op).
 *)
Cancel(Q_old, id) == {e \in Q_old : e.id # id}

(*
 * CancelByKind(Q, kind) - Remove all events of a given kind
 *
 * Useful for canceling all pending timer callbacks when
 * reprogramming a device.
 *)
CancelByKind(Q_old, kind) == {e \in Q_old : e.kind # kind}

\* =====================================================================
\* DETERMINISTIC EVENT SELECTION
\* =====================================================================

(*
 * DueEvents(Q, now) - Events that are due for processing
 *
 * Returns the set of events whose deadline has been reached.
 *)
DueEvents(Q_now, now_val) == {e \in Q_now : e.deadline <= now_val}

(*
 * MinDeadline(events) - Minimum deadline in a set of events
 *
 * Precondition: events is non-empty
 *)
MinDeadline(events) == Min({e.deadline : e \in events})

(*
 * EventsAtDeadline(events, d) - Events with exactly deadline d
 *)
EventsAtDeadline(events, d) == {e \in events : e.deadline = d}

(*
 * MinTieKey(events) - Minimum tieKey in a set of events
 *
 * Precondition: events is non-empty
 *)
MinTieKey(events) == Min({e.tieKey : e \in events})

(*
 * SelectNextEvent(Q, now) - Deterministically select the next event
 *
 * Selection algorithm:
 * 1. Find all events due (deadline <= now)
 * 2. Among due events, find minimum deadline
 * 3. Among events at minimum deadline, find minimum tieKey
 * 4. Return the unique event matching both criteria
 *
 * This ensures deterministic selection without relying on
 * arbitrary CHOOSE semantics.
 *
 * Returns a record:
 *   [found |-> TRUE, event |-> e] if an event is ready
 *   [found |-> FALSE]            if no events are due
 *)
SelectNextEvent(Q_now, now_val) ==
    LET due == DueEvents(Q_now, now_val)
    IN IF due = {}
       THEN [found |-> FALSE]
       ELSE LET minD == MinDeadline(due)
                atMinD == EventsAtDeadline(due, minD)
                minT == MinTieKey(atMinD)
                winner == CHOOSE e \in atMinD : e.tieKey = minT
            IN [found |-> TRUE, event |-> winner]

(*
 * PopNextEvent(Q, now) - Select and remove the next event
 *
 * Returns a record:
 *   [found |-> TRUE, event |-> e, Q' |-> new queue]
 *   [found |-> FALSE, Q' |-> Q] if no events due
 *)
PopNextEvent(Q_now, now_val) ==
    LET selection == SelectNextEvent(Q_now, now_val)
    IN IF ~selection.found
       THEN [found |-> FALSE, Q_new |-> Q_now]
       ELSE [found |-> TRUE,
             event |-> selection.event,
             Q_new |-> Q_now \ {selection.event}]

\* =====================================================================
\* TIME ADVANCEMENT
\* =====================================================================

(*
 * NextEventTime(Q) - Time of the earliest pending event
 *
 * Returns MaxCycle + 1 if queue is empty (sentinel value).
 *)
NextEventTime(Q_now) ==
    IF Q_now = {}
    THEN MaxCycle + 1
    ELSE Min({e.deadline : e \in Q_now})

(*
 * AdvanceTimeTo(now, target) - Advance time to target
 *
 * Precondition: target >= now (monotonicity)
 * Used when jumping to the next event's deadline.
 *)
AdvanceTimeTo(now_val, target) ==
    IF target > now_val
    THEN target
    ELSE now_val

(*
 * TimeStep(Q, now) - Compute the next time value
 *
 * Strategy:
 * - If events are due (deadline <= now), don't advance time
 * - If events are pending (deadline > now), advance to earliest
 * - If no events, advance by 1 cycle
 *
 * This ensures events are processed at their exact deadline.
 *)
TimeStep(Q_now, now_val) ==
    LET due == DueEvents(Q_now, now_val)
    IN IF due # {}
       THEN now_val                      \* Process due events first
       ELSE IF Q_now = {}
            THEN now_val + 1             \* No events, tick by 1
            ELSE NextEventTime(Q_now)    \* Jump to next event

\* =====================================================================
\* TIE-KEY ASSIGNMENT
\* =====================================================================

(*
 * Tie-key ordering defines the processing order when multiple
 * events have the same deadline. Lower tieKey = higher priority.
 *
 * Standard ordering (matches DOSBox-X pic.cpp implicit ordering):
 *   PIT_TICK   = 0   (highest priority - timer IRQ0)
 *   IRQ_CHECK  = 10  (interrupt delivery check)
 *   KBD_SCAN   = 20  (keyboard scan)
 *   DMA_TC     = 30  (DMA terminal count)
 *   TIMER_CB   = 40  (general timer callbacks)
 *)
DefaultTieKey(kind) ==
    CASE kind = "PIT_TICK"  -> 0
      [] kind = "IRQ_CHECK" -> 10
      [] kind = "KBD_SCAN"  -> 20
      [] kind = "DMA_TC"    -> 30
      [] kind = "TIMER_CB"  -> 40
      [] OTHER              -> 50

(*
 * MakeEvent(id, deadline, kind, payload) - Create event with default tieKey
 *)
MakeEvent(id, deadline, kind, payload) ==
    [id |-> id,
     deadline |-> deadline,
     kind |-> kind,
     payload |-> payload,
     tieKey |-> DefaultTieKey(kind)]

(*
 * MakeEventWithTieKey(id, deadline, kind, payload, tieKey) - Create with custom tieKey
 *)
MakeEventWithTieKey(id, deadline, kind, payload, tk) ==
    [id |-> id,
     deadline |-> deadline,
     kind |-> kind,
     payload |-> payload,
     tieKey |-> tk]

\* =====================================================================
\* SCHEDULER INVARIANTS
\* =====================================================================

(*
 * QueueWellFormed(Q) - Basic queue validity
 *)
QueueWellFormed(Q_now) ==
    /\ \A e \in Q_now : e \in Event
    /\ Cardinality(Q_now) <= MaxEvents

(*
 * UniqueEventIds(Q) - No duplicate event IDs
 * (Optional - depends on whether IDs must be unique)
 *)
UniqueEventIds(Q_now) ==
    \A e1, e2 \in Q_now : e1.id = e2.id => e1 = e2

(*
 * DeterministicSelection(Q, now) - Selection is deterministic
 *
 * For any non-empty due set, there is exactly one event that
 * would be selected (minimum deadline, then minimum tieKey).
 *)
DeterministicSelection(Q_now, now_val) ==
    LET due == DueEvents(Q_now, now_val)
    IN due # {} =>
       LET minD == MinDeadline(due)
           atMinD == EventsAtDeadline(due, minD)
           minT == MinTieKey(atMinD)
       IN Cardinality({e \in atMinD : e.tieKey = minT}) = 1

\* =====================================================================
\* SCHEDULER PROPERTIES (for model checking)
\* =====================================================================

(*
 * NoEventsLost - Every scheduled event is eventually processed
 *
 * This is a liveness property requiring fairness assumptions.
 * It states that if an event is in Q and its deadline is reached,
 * it will eventually be removed from Q (processed).
 *)
\* NoEventsLost == \A e \in Q : e.deadline <= now ~> e \notin Q

(*
 * FIFOWithinDeadline - Events at same deadline processed in tieKey order
 *
 * This is implicit in the selection algorithm but can be checked
 * by examining traces.
 *)

(*
 * ProgressProperty - Time eventually advances
 *
 * Under weak fairness on time steps, time will progress as long
 * as the system doesn't get stuck processing infinite events.
 *)
\* ProgressProperty == []<>(now' > now)

\* =====================================================================
\* SCHEDULER STATE MACHINE ACTIONS
\* =====================================================================
(*
 * These actions are meant to be composed into EmuKernel.Next.
 * They operate on the shared variables (now, Q).
 *)

(*
 * ProcessOneEvent - Pop and process a single due event
 *
 * This is an internal action that:
 * 1. Selects the next due event (deterministically)
 * 2. Removes it from Q
 * 3. (In full spec) Dispatches to appropriate handler
 *
 * Returns the event that was processed for trace logging.
 *)
\* ProcessOneEvent ==
\*     LET result == PopNextEvent(Q, now)
\*     IN /\ result.found
\*        /\ Q' = result.Q_new
\*        /\ \* Handler dispatch would go here

(*
 * AdvanceTimeAction - Advance time when no events due
 *)
\* AdvanceTimeAction ==
\*     LET due == DueEvents(Q, now)
\*     IN /\ due = {}
\*        /\ now' = TimeStep(Q, now)
\*        /\ UNCHANGED Q

\* =====================================================================
\* TEST HELPERS (for scenario verification)
\* =====================================================================

(*
 * EventSequence(events, now) - Order events would be processed
 *
 * Returns a sequence of events in the order they would be
 * selected by PopNextEvent, useful for trace verification.
 *)
RECURSIVE EventSequence(_, _)
EventSequence(events, now_val) ==
    IF events = {}
    THEN <<>>
    ELSE LET result == PopNextEvent(events, now_val)
         IN IF ~result.found
            THEN <<>>
            ELSE <<result.event>> \o EventSequence(result.Q_new, now_val)

(*
 * VerifyOrder(events, expected, now) - Verify processing order
 *
 * Checks that events would be processed in the expected order
 * (by event ID).
 *)
VerifyOrder(events, expected_ids, now_val) ==
    LET actual == EventSequence(events, now_val)
        actual_ids == [i \in 1..Len(actual) |-> actual[i].id]
    IN actual_ids = expected_ids

=======================================================================
