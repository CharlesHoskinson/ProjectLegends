---- MODULE SaveStateTest_TTrace_1768377546 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, SaveStateTest

_expression ==
    LET SaveStateTest_TEExpression == INSTANCE SaveStateTest_TEExpression
    IN SaveStateTest_TEExpression!expression
----

_trace ==
    LET SaveStateTest_TETrace == INSTANCE SaveStateTest_TETrace
    IN SaveStateTest_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        loaded = ({})
        /\
        state = ([Q |-> {[deadline |-> 10, kind |-> "PIT_TICK", tieKey |-> 0, payload |-> 0, id |-> 0], [deadline |-> 15, kind |-> "KBD_SCAN", tieKey |-> 20, payload |-> 5, id |-> 1]}, now |-> 5, cpu_if |-> TRUE, pic_irr |-> 3])
        /\
        snap = ([now |-> 5, cpu_if |-> TRUE, pic_irr |-> 3, events |-> {[deadline |-> 10, kind |-> "PIT_TICK", tieKey |-> 0, payload |-> 0], [deadline |-> 15, kind |-> "KBD_SCAN", tieKey |-> 20, payload |-> 5]}])
    )
----

_init ==
    /\ snap = _TETrace[1].snap
    /\ state = _TETrace[1].state
    /\ loaded = _TETrace[1].loaded
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ snap  = _TETrace[i].snap
        /\ snap' = _TETrace[j].snap
        /\ state  = _TETrace[i].state
        /\ state' = _TETrace[j].state
        /\ loaded  = _TETrace[i].loaded
        /\ loaded' = _TETrace[j].loaded

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("SaveStateTest_TTrace_1768377546.json", _TETrace)

=============================================================================

 Note that you can extract this module `SaveStateTest_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `SaveStateTest_TEExpression.tla` file takes precedence 
  over the module `SaveStateTest_TEExpression` below).

---- MODULE SaveStateTest_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, SaveStateTest

expression == 
    [
        \* To hide variables of the `SaveStateTest` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        snap |-> snap
        ,state |-> state
        ,loaded |-> loaded
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_snapUnchanged |-> snap = snap'
        
        \* Format the `snap` variable as Json value.
        \* ,_snapJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(snap)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_snapModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].snap # _TETrace[s-1].snap
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE SaveStateTest_TETrace ----
\*EXTENDS IOUtils, TLC, SaveStateTest
\*
\*trace == IODeserialize("SaveStateTest_TTrace_1768377546.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE SaveStateTest_TETrace ----
EXTENDS TLC, SaveStateTest

trace == 
    <<
    ([loaded |-> {},state |-> [Q |-> {[deadline |-> 10, kind |-> "PIT_TICK", tieKey |-> 0, payload |-> 0, id |-> 0], [deadline |-> 15, kind |-> "KBD_SCAN", tieKey |-> 20, payload |-> 5, id |-> 1]}, now |-> 5, cpu_if |-> TRUE, pic_irr |-> 3],snap |-> {}]),
    ([loaded |-> {},state |-> [Q |-> {[deadline |-> 10, kind |-> "PIT_TICK", tieKey |-> 0, payload |-> 0, id |-> 0], [deadline |-> 15, kind |-> "KBD_SCAN", tieKey |-> 20, payload |-> 5, id |-> 1]}, now |-> 5, cpu_if |-> TRUE, pic_irr |-> 3],snap |-> [now |-> 5, cpu_if |-> TRUE, pic_irr |-> 3, events |-> {[deadline |-> 10, kind |-> "PIT_TICK", tieKey |-> 0, payload |-> 0], [deadline |-> 15, kind |-> "KBD_SCAN", tieKey |-> 20, payload |-> 5]}]])
    >>
----


=============================================================================

---- CONFIG SaveStateTest_TTrace_1768377546 ----
CONSTANTS
    MaxCycle = 20
    MaxEvents = 3

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Jan 14 00:59:06 MST 2026