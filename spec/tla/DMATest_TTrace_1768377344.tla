---- MODULE DMATest_TTrace_1768377344 ----
EXTENDS Sequences, DMATest, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET DMATest_TEExpression == INSTANCE DMATest_TEExpression
    IN DMATest_TEExpression!expression
----

_trace ==
    LET DMATest_TETrace == INSTANCE DMATest_TETrace
    IN DMATest_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        transfers = (51)
        /\
        tc_events = (1)
        /\
        dma = ((0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"]))
    )
----

_init ==
    /\ tc_events = _TETrace[1].tc_events
    /\ dma = _TETrace[1].dma
    /\ transfers = _TETrace[1].transfers
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ tc_events  = _TETrace[i].tc_events
        /\ tc_events' = _TETrace[j].tc_events
        /\ dma  = _TETrace[i].dma
        /\ dma' = _TETrace[j].dma
        /\ transfers  = _TETrace[i].transfers
        /\ transfers' = _TETrace[j].transfers

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("DMATest_TTrace_1768377344.json", _TETrace)

=============================================================================

 Note that you can extract this module `DMATest_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `DMATest_TEExpression.tla` file takes precedence 
  over the module `DMATest_TEExpression` below).

---- MODULE DMATest_TEExpression ----
EXTENDS Sequences, DMATest, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `DMATest` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        tc_events |-> tc_events
        ,dma |-> dma
        ,transfers |-> transfers
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_tc_eventsUnchanged |-> tc_events = tc_events'
        
        \* Format the `tc_events` variable as Json value.
        \* ,_tc_eventsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(tc_events)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_tc_eventsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].tc_events # _TETrace[s-1].tc_events
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE DMATest_TETrace ----
\*EXTENDS IOUtils, DMATest, TLC
\*
\*trace == IODeserialize("DMATest_TTrace_1768377344.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE DMATest_TETrace ----
EXTENDS DMATest, TLC

trace == 
    <<
    ([transfers |-> 0,tc_events |-> 0,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> FALSE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 1,tc_events |-> 0,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> FALSE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 2,tc_events |-> 0,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> FALSE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 3,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 4,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 5,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 6,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 7,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 8,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 9,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 10,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 11,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 12,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 13,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 14,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 15,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 16,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 17,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 18,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 19,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 20,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 21,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 22,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 23,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 24,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 25,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 26,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 27,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 28,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 29,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 30,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 31,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 32,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 33,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 34,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 35,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 36,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 37,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 38,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 39,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 40,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 41,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 42,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 43,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 44,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 45,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 46,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 47,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 48,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 49,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 2, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 50,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 1, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])]),
    ([transfers |-> 51,tc_events |-> 1,dma |-> (0 :> [enabled |-> TRUE, masked |-> FALSE, count |-> 3, base_count |-> 3, request |-> TRUE, tc_reached |-> TRUE, autoinit |-> TRUE, mode |-> "Single"] @@ 1 :> [enabled |-> FALSE, masked |-> TRUE, count |-> 0, base_count |-> 0, request |-> FALSE, tc_reached |-> FALSE, autoinit |-> FALSE, mode |-> "Single"])])
    >>
----


=============================================================================

---- CONFIG DMATest_TTrace_1768377344 ----
CONSTANTS
    MaxCycle = 10
    MaxCount = 5

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
\* Generated on Wed Jan 14 00:55:44 MST 2026