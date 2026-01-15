-------------------------- MODULE EmuKernel --------------------------
(*
 * Legends Emukernel - Top-Level State Machine Specification
 *
 * This module specifies the core state machine for the Legends emulation
 * kernel. It defines:
 * - Machine state variables (time, events, CPU, devices)
 * - Observation function for save-state equivalence
 * - Type and safety invariants
 * - State transitions (time steps, input injection)
 *
 * The specification is designed to be:
 * - Model-checkable with TLC (bounded domains)
 * - Deterministic (explicit tie-breaking, no hidden nondeterminism)
 * - Usable for conformance testing against implementation
 *
 * Key invariants:
 * - MonotonicTime: Virtual time never decreases
 * - EventsNotInPast: No events scheduled before current time
 * - TypeOK: All state variables within their type bounds
 *)
EXTENDS Types, Integers, Sequences, FiniteSets, TLC

\* Import Scheduler operators (uses LOCAL INSTANCE to avoid variable conflicts)
\* Note: Scheduler.tla provides Schedule, Cancel, PopNextEvent, TimeStep, etc.

\* =====================================================================
\* DEFAULT VALUES - Hardcoded for TLC compatibility
\* =====================================================================
\* PIC initialization: all interrupts masked initially (0xFF = 255)
\* Master PIC (i=0): vector base 8 (IRQ 0-7 -> INT 8-15)
\* Slave PIC (i=1): vector base 112 (IRQ 8-15 -> INT 112-119)
InitialMasks == [i \in {0, 1} |-> 255]
InitialVectorBase == [i \in {0, 1} |-> IF i = 0 THEN 8 ELSE 112]

\* =====================================================================
\* STATE VARIABLES
\* =====================================================================
VARIABLES
    now,        \* Current virtual time (cycles)
    Q,          \* Event queue (set of Event records)
    CPU,        \* CPU state record
    pics,       \* PIC controllers [0..1] -> PICState
    dma,        \* DMA channels [0..7] -> DMAChannelState
    IOMap,      \* Port -> Handler mapping
    InputQ,     \* External input queue (sequence from environment)
    Out         \* Output trace (sequence of observations)

\* Tuple of all variables for UNCHANGED clauses
vars == <<now, Q, CPU, pics, dma, IOMap, InputQ, Out>>

\* =====================================================================
\* OBSERVATION FUNCTION
\* =====================================================================
(*
 * Obs(S) defines what state must be preserved across save/load.
 * Two states are equivalent iff their observations are equal.
 * This is the "single source of truth" for determinism.
 *
 * Critical: Q_digest includes the event queue! The current DOSBox-X
 * implementation does NOT serialize the event queue, which breaks
 * deterministic replay.
 *)

Obs(S) == [
    now       |-> S.now,
    Q_digest  |-> {<<e.deadline, e.kind, e.tieKey>> : e \in S.Q},
    CPU_IF    |-> S.CPU.IF,
    CPU_halted|-> S.CPU.halted,
    pic0_irr  |-> S.pics[0].irr,
    pic0_imr  |-> S.pics[0].imr,
    pic0_isr  |-> S.pics[0].isr,
    pic1_irr  |-> S.pics[1].irr,
    pic1_imr  |-> S.pics[1].imr,
    pic1_isr  |-> S.pics[1].isr
]

\* Current observation (for use in properties)
CurrentState == [
    now    |-> now,
    Q      |-> Q,
    CPU    |-> CPU,
    pics   |-> pics,
    dma    |-> dma,
    IOMap  |-> IOMap,
    InputQ |-> InputQ,
    Out    |-> Out
]

CurrentObs == Obs(CurrentState)

\* Digest of event queue for comparison
Q_digest(S) == {<<e.deadline, e.kind, e.tieKey>> : e \in S.Q}

\* =====================================================================
\* TYPE INVARIANTS
\* =====================================================================
(*
 * TypeOK ensures all state variables are within their defined domains.
 * Uses structural checks instead of set membership to avoid TLC explosion.
 *)

\* Check if an event record is well-formed
IsValidEvent(e) ==
    /\ e.id \in EventIds
    /\ e.deadline \in Cycles
    /\ e.kind \in EventKind
    /\ e.payload \in PayloadRange
    /\ e.tieKey \in TieKeyRange

\* Check if a CPU state record is well-formed
IsValidCPU(c) ==
    /\ c.IF \in BOOLEAN
    /\ c.halted \in BOOLEAN
    /\ c.mode \in CPUMode

\* Check if a PIC state record is well-formed
IsValidPIC(p) ==
    /\ p.irr \in 0..255
    /\ p.imr \in 0..255
    /\ p.isr \in 0..255
    /\ p.vector_base \in 0..255
    /\ p.cascade_irq \in 0..7

\* Check if a DMA channel state is well-formed
IsValidDMA(d) ==
    /\ d.enabled \in BOOLEAN
    /\ d.masked \in BOOLEAN
    /\ d.count \in DMACount
    /\ d.request \in BOOLEAN
    /\ d.tc_reached \in BOOLEAN
    /\ d.autoinit \in BOOLEAN

TypeOK ==
    /\ now \in Cycles
    /\ \A e \in Q : IsValidEvent(e)
    /\ Cardinality(Q) <= MaxEvents
    /\ IsValidCPU(CPU)
    /\ \A i \in {0, 1} : IsValidPIC(pics[i])
    /\ \A ch \in 0..7 : IsValidDMA(dma[ch])
    /\ \A p \in PortSet : IOMap[p] \in IOHandler

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

\* Time must never decrease (monotonic)
\* Note: This is checked as an action property in TLC
MonotonicTime == now' >= now

\* No event should be scheduled in the past
EventsNotInPast == \A e \in Q : e.deadline >= now

\* Combined well-formedness check
StateWellFormed == TypeOK /\ EventsNotInPast

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

\* Initialize a PIC controller
InitPIC(i) == [
    irr        |-> 0,
    imr        |-> InitialMasks[i],
    isr        |-> 0,
    vector_base|-> InitialVectorBase[i],
    cascade_irq|-> 2
]

\* Initialize a DMA channel (all masked/disabled)
InitDMA(ch) == [
    enabled   |-> FALSE,
    masked    |-> TRUE,
    count     |-> 0,
    request   |-> FALSE,
    tc_reached|-> FALSE,
    autoinit  |-> FALSE
]

\* Initialize I/O port mapping
\* Maps ports to their handler devices
InitIOMap == [p \in PortSet |->
    CASE p \in {32, 33}           -> "PIC"   \* 0x20-0x21 Master PIC
      [] p \in {160, 161}         -> "PIC"   \* 0xA0-0xA1 Slave PIC
      [] p \in {64, 65, 66, 67}   -> "PIT"   \* 0x40-0x43 PIT
      [] p \in {96, 97}           -> "KBD"   \* 0x60-0x61 Keyboard
      [] OTHER                    -> "NONE"
]

\* Initial state predicate
Init ==
    /\ now = 0
    /\ Q = {}
    /\ CPU = [IF |-> FALSE, halted |-> FALSE, mode |-> "Real"]
    /\ pics = [i \in 0..1 |-> InitPIC(i)]
    /\ dma = [ch \in 0..7 |-> InitDMA(ch)]
    /\ IOMap = InitIOMap
    /\ InputQ = <<>>
    /\ Out = <<>>

\* =====================================================================
\* SCHEDULER HELPERS (inline from Scheduler.tla for self-containment)
\* =====================================================================

\* Events that are due for processing
DueEvents == {e \in Q : e.deadline <= now}

\* Minimum of a non-empty set
MinSet(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Select next event deterministically (deadline then tieKey)
SelectNext ==
    IF DueEvents = {}
    THEN [found |-> FALSE]
    ELSE LET minD == MinSet({e.deadline : e \in DueEvents})
             atMinD == {e \in DueEvents : e.deadline = minD}
             minT == MinSet({e.tieKey : e \in atMinD})
             winner == CHOOSE e \in atMinD : e.tieKey = minT
         IN [found |-> TRUE, event |-> winner]

\* Next event deadline (or MaxCycle+1 if empty)
NextEventTime ==
    IF Q = {} THEN MaxCycle + 1
    ELSE MinSet({e.deadline : e \in Q})

\* =====================================================================
\* STATE TRANSITIONS
\* =====================================================================

(*
 * Environment step: External input injection
 * The environment (host/agent) can inject inputs into InputQ.
 * This is the ONLY source of nondeterminism in the specification.
 *)
EnvInjectInput(input) ==
    /\ InputQ' = Append(InputQ, input)
    /\ UNCHANGED <<now, Q, CPU, pics, dma, IOMap, Out>>

(*
 * Kernel step: Process a due event
 * Selects the next due event (deterministically) and removes it from Q.
 * In the full spec, this would also dispatch to the appropriate handler.
 *)
KernelProcessEvent ==
    LET sel == SelectNext
    IN /\ sel.found
       /\ Q' = Q \ {sel.event}
       /\ Out' = Append(Out, [time |-> now, event |-> sel.event.kind])
       /\ UNCHANGED <<now, CPU, pics, dma, IOMap, InputQ>>

(*
 * Kernel step: Advance time when no events due
 * Uses scheduler-aware time step:
 * - If events pending but not due, jump to next deadline
 * - If no events, increment by 1
 *)
KernelTimeStep ==
    /\ DueEvents = {}           \* No events due now
    /\ now < MaxCycle           \* Haven't reached max time
    /\ IF Q = {}
       THEN now' = now + 1                          \* No events: tick by 1
       ELSE now' = MinSet({e.deadline : e \in Q})   \* Jump to next deadline
    /\ UNCHANGED <<Q, CPU, pics, dma, IOMap, InputQ, Out>>

(*
 * Kernel idle: At max time with no events
 * The system can idle (stutter) when at maximum time.
 *)
KernelIdle ==
    /\ Q = {}
    /\ now = MaxCycle
    /\ UNCHANGED vars

(*
 * Schedule a new event (for testing/scenarios)
 * Creates an event with given parameters and adds to Q.
 *)
ScheduleNewEvent(id, deadline, kind, payload, tieKey) ==
    LET e == [id |-> id, deadline |-> deadline, kind |-> kind,
              payload |-> payload, tieKey |-> tieKey]
    IN /\ deadline >= now       \* Cannot schedule in past
       /\ Cardinality(Q) < MaxEvents
       /\ Q' = Q \cup {e}
       /\ UNCHANGED <<now, CPU, pics, dma, IOMap, InputQ, Out>>

(*
 * Cancel an event by ID
 *)
CancelEvent(id) ==
    /\ Q' = {e \in Q : e.id # id}
    /\ UNCHANGED <<now, CPU, pics, dma, IOMap, InputQ, Out>>

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================
(*
 * The next-state relation is a disjunction of all possible transitions.
 * Priority order (for understanding, not enforcement):
 * 1. Process due events (KernelProcessEvent)
 * 2. Advance time if no events due (KernelTimeStep)
 * 3. Accept external input (EnvInjectInput)
 * 4. Idle at max time (KernelIdle)
 * 5. Stuttering (UNCHANGED vars)
 *)

Next ==
    \/ KernelProcessEvent   \* Process due events
    \/ KernelTimeStep       \* Advance time when no events due
    \/ KernelIdle           \* Idle at max time
    \/ \E input \in {"KEY_A", "KEY_B", "NONE"} : EnvInjectInput(input)
    \/ UNCHANGED vars       \* Stuttering step for completeness

\* =====================================================================
\* SPECIFICATION
\* =====================================================================
(*
 * The temporal formula combining:
 * - Initial state
 * - Next-state transitions (with stuttering)
 * - Weak fairness on KernelProcessEvent (events eventually processed)
 * - Weak fairness on KernelTimeStep (time eventually progresses)
 *)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(KernelProcessEvent)
        /\ WF_vars(KernelTimeStep)

\* =====================================================================
\* LIVENESS PROPERTIES
\* =====================================================================

\* Time will eventually progress (requires fairness)
TimeProgresses == <>(now > 0)

\* =====================================================================
\* SAVE-STATE PROPERTIES
\* =====================================================================
(*
 * These properties verify save-state correctness.
 * The EventLoss property should NEVER be satisfiable after fixing
 * the implementation to serialize the event queue.
 *
 * Note: Serialize/Deserialize operators will be defined in
 * SaveState.tla (Milestone 6). For now, these are placeholders.
 *)

\* Placeholder - will be defined in SaveState.tla
Serialize(S) == S
Deserialize(snap) == snap

\* Event Loss property - should NEVER be TRUE in correct implementation
\* This detects if serialization loses event queue information
EventLoss ==
    \E S \in {CurrentState} :
        Q_digest(Deserialize(Serialize(S))) # Q_digest(S)

\* =====================================================================
\* SCHEDULER INVARIANTS
\* =====================================================================

\* Selection is deterministic when events are due
SelectionDeterministic ==
    DueEvents # {} =>
    LET minD == MinSet({e.deadline : e \in DueEvents})
        atMinD == {e \in DueEvents : e.deadline = minD}
        minT == MinSet({e.tieKey : e \in atMinD})
    IN Cardinality({e \in atMinD : e.tieKey = minT}) = 1

\* Events are processed in correct order (tieKey within deadline)
\* This is implicitly enforced by SelectNext

\* =====================================================================
\* TRACE VERIFICATION HELPERS
\* =====================================================================

\* Get processing order for a set of events
RECURSIVE ProcessingOrder(_)
ProcessingOrder(events) ==
    IF events = {} THEN <<>>
    ELSE LET due == {e \in events : e.deadline <= now}
         IN IF due = {}
            THEN <<>>  \* No events due yet
            ELSE LET minD == MinSet({e.deadline : e \in due})
                     atMinD == {e \in due : e.deadline = minD}
                     minT == MinSet({e.tieKey : e \in atMinD})
                     winner == CHOOSE e \in atMinD : e.tieKey = minT
                 IN <<winner.id>> \o ProcessingOrder(events \ {winner})

\* Verify that Out trace matches expected event order
TraceMatchesExpected(expected_ids) ==
    LET actual_ids == [i \in 1..Len(Out) |-> Out[i].event]
    IN TRUE  \* Placeholder - full implementation in conformance oracle

=======================================================================
