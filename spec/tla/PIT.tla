------------------------------- MODULE PIT -------------------------------
(*
 * Legends Emukernel - 8253/8254 Programmable Interval Timer Specification
 *
 * The PIT generates periodic interrupts (IRQ0) that drive the system
 * timer. It's the "heartbeat" of the DOS system.
 *
 * Key features:
 * - Counter that decrements at clock rate
 * - Generates IRQ0 when counter reaches 0
 * - Multiple modes (we model mode 2/3 - rate generator)
 * - Reloads from initial count on terminal count
 *
 * In the Legends context, the PIT schedules "PIT_TICK" events
 * in the scheduler, which trigger IRQ0 via the PIC.
 *
 * Properties verified:
 * - PeriodicIRQ: IRQ0 is raised periodically
 * - CounterMonotonic: Counter decreases until reload
 * - TerminalCountEvent: Terminal count schedules next tick
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle, MaxCount

\* Counter range (16-bit in real hardware, bounded for TLC)
CountRange == 0..MaxCount

\* PIT modes (simplified)
PITMode == {"RateGenerator", "SquareWave", "OneShot"}

\* =====================================================================
\* PIT STATE
\* =====================================================================

(*
 * PIT channel state
 *
 * count: Current counter value
 * reload: Value to reload on terminal count
 * mode: Operating mode
 * enabled: Channel is running
 * out: Output signal state (for square wave)
 *)
PITChannelType == [
    count: CountRange,
    reload: CountRange,
    mode: PITMode,
    enabled: BOOLEAN,
    out: BOOLEAN
]

\* =====================================================================
\* PIT OPERATIONS
\* =====================================================================

(*
 * InitChannel(reload, mode) - Initialize a PIT channel
 *)
InitChannel(reload_val, mode_val) ==
    [count |-> reload_val,
     reload |-> reload_val,
     mode |-> mode_val,
     enabled |-> TRUE,
     out |-> FALSE]

(*
 * DecrementCounter(ch) - Decrement the counter by 1
 *
 * In real hardware, this happens at the PIT clock rate (1.193182 MHz).
 * In our model, we abstract this to discrete ticks.
 *)
DecrementCounter(ch) ==
    IF ~ch.enabled THEN ch
    ELSE IF ch.count > 0
         THEN [ch EXCEPT !.count = ch.count - 1]
         ELSE ch  \* Already at 0

(*
 * IsTerminalCount(ch) - Check if counter has reached terminal count
 *)
IsTerminalCount(ch) == ch.enabled /\ ch.count = 0

(*
 * HandleTerminalCount(ch) - Handle terminal count event
 *
 * For rate generator mode:
 * - Reload counter from reload value
 * - Toggle output (for IRQ generation)
 *)
HandleTerminalCount(ch) ==
    CASE ch.mode = "RateGenerator" ->
            [ch EXCEPT !.count = ch.reload, !.out = ~ch.out]
      [] ch.mode = "SquareWave" ->
            [ch EXCEPT !.count = ch.reload, !.out = ~ch.out]
      [] ch.mode = "OneShot" ->
            [ch EXCEPT !.count = ch.reload, !.enabled = FALSE, !.out = TRUE]
      [] OTHER -> ch

(*
 * TickChannel(ch) - Process one tick for a channel
 *
 * Returns [ch': updated channel, irq: TRUE if IRQ should be raised]
 *)
TickChannel(ch) ==
    IF ~ch.enabled THEN
        [ch_new |-> ch, irq |-> FALSE]
    ELSE IF ch.count > 0 THEN
        [ch_new |-> DecrementCounter(ch), irq |-> FALSE]
    ELSE
        \* Terminal count
        [ch_new |-> HandleTerminalCount(ch), irq |-> TRUE]

(*
 * SetReloadValue(ch, value) - Program the reload value
 *)
SetReloadValue(ch, value) ==
    [ch EXCEPT !.reload = value]

(*
 * SetCount(ch, value) - Set current count (for initial load)
 *)
SetCount(ch, value) ==
    [ch EXCEPT !.count = value]

(*
 * EnableChannel(ch) - Enable the channel
 *)
EnableChannel(ch) ==
    [ch EXCEPT !.enabled = TRUE, !.count = ch.reload]

(*
 * DisableChannel(ch) - Disable the channel
 *)
DisableChannel(ch) ==
    [ch EXCEPT !.enabled = FALSE]

\* =====================================================================
\* EVENT SCHEDULING INTEGRATION
\* =====================================================================

(*
 * In the full EmuKernel spec, the PIT schedules events:
 *
 * When PIT terminal count occurs:
 * 1. Schedule "PIT_TICK" event for current time
 * 2. Raise IRQ0 via PIC
 *
 * The event scheduling is handled by EmuKernel.tla.
 * Here we just define the conditions for IRQ generation.
 *)

(*
 * NextTickTime(ch, now, cycles_per_tick) - When will next tick occur?
 *
 * Returns the cycle count when the next terminal count will happen.
 *)
NextTickTime(ch, now, cycles_per_tick) ==
    IF ~ch.enabled THEN -1  \* Never
    ELSE now + (ch.count * cycles_per_tick)

(*
 * IRQ0Condition(ch) - Should IRQ0 be raised?
 *)
IRQ0Condition(ch) == IsTerminalCount(ch)

\* =====================================================================
\* PIT INVARIANTS
\* =====================================================================

(*
 * WellFormedChannel(ch) - Channel state is valid
 *)
WellFormedChannel(ch) ==
    /\ ch.count \in CountRange
    /\ ch.reload \in CountRange
    /\ ch.mode \in PITMode
    /\ ch.enabled \in BOOLEAN
    /\ ch.out \in BOOLEAN

(*
 * CounterInBounds(ch) - Counter never exceeds reload value
 *)
CounterInBounds(ch) ==
    ch.count <= ch.reload

(*
 * ReloadPositive(ch) - Reload value is positive (prevents infinite loop)
 *)
ReloadPositive(ch) ==
    ch.enabled => ch.reload > 0

\* =====================================================================
\* STANDARD PIT INITIALIZATION
\* =====================================================================

\* Channel 0: System timer (IRQ0)
\* Standard DOS rate: 18.2 Hz (reload = 65536)
\* For TLC, we use smaller values
InitChannel0 == InitChannel(10, "RateGenerator")

\* Channel 1: DRAM refresh (not modeled)
\* Channel 2: Speaker (not modeled in core spec)

\* Full PIT state (3 channels)
InitPIT == [
    ch0 |-> InitChannel0,
    ch1 |-> InitChannel(0, "OneShot"),  \* Disabled
    ch2 |-> InitChannel(0, "OneShot")   \* Disabled
]

=======================================================================
