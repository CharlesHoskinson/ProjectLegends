------------------------ MODULE InterruptTest ------------------------
(*
 * Legends Emukernel - Interrupt Subsystem Test
 *
 * Tests PIC functionality:
 * 1. Priority: Lower IRQ numbers have higher priority
 * 2. Masking: Masked IRQs are not delivered
 * 3. EOI: End-of-interrupt clears in-service bit
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle, MaxCount

\* IRQ lines
IRQLines == 0..7
RegValue == 0..255

\* =====================================================================
\* BIT OPERATIONS (from PIC.tla)
\* =====================================================================

BitSet(reg, bit) == (reg % (2^(bit+1))) \div (2^bit) = 1
SetBit(reg, bit) == IF BitSet(reg, bit) THEN reg ELSE reg + 2^bit
ClearBit(reg, bit) == IF BitSet(reg, bit) THEN reg - 2^bit ELSE reg
SetBits(reg) == {b \in 0..7 : BitSet(reg, b)}

LowestSetBit(reg) ==
    IF reg = 0 THEN -1
    ELSE CHOOSE b \in 0..7 : BitSet(reg, b) /\ \A b2 \in 0..(b-1) : ~BitSet(reg, b2)

\* =====================================================================
\* PIC OPERATIONS (from PIC.tla)
\* =====================================================================

WellFormedPIC(pic) ==
    /\ pic.irr \in RegValue
    /\ pic.imr \in RegValue
    /\ pic.isr \in RegValue
    /\ pic.vector_base \in RegValue

RaiseIRQ(pic, irq) == [pic EXCEPT !.irr = SetBit(pic.irr, irq)]
LowerIRQ(pic, irq) == [pic EXCEPT !.irr = ClearBit(pic.irr, irq)]

PendingIRQs(pic) ==
    LET requested == SetBits(pic.irr)
        masked == SetBits(pic.imr)
        in_service == SetBits(pic.isr)
    IN (requested \ masked) \ in_service

HighestPriorityIRQ(pic) ==
    LET pending == PendingIRQs(pic)
    IN IF pending = {} THEN -1
       ELSE CHOOSE irq \in pending : \A other \in pending : irq <= other

HasPendingInterrupt(pic) == PendingIRQs(pic) # {}

AcknowledgeIRQ(pic, irq) ==
    [pic EXCEPT !.irr = ClearBit(pic.irr, irq), !.isr = SetBit(pic.isr, irq)]

SendEOI(pic, irq) == [pic EXCEPT !.isr = ClearBit(pic.isr, irq)]

GetInterruptVector(pic, irq) == pic.vector_base + irq

DeliverInterrupt(pic, cpu_if) ==
    IF ~cpu_if THEN
        [delivered |-> FALSE, irq |-> -1, vector |-> -1, pic_new |-> pic]
    ELSE
        LET irq == HighestPriorityIRQ(pic)
        IN IF irq = -1 THEN
               [delivered |-> FALSE, irq |-> -1, vector |-> -1, pic_new |-> pic]
           ELSE
               [delivered |-> TRUE, irq |-> irq,
                vector |-> GetInterruptVector(pic, irq),
                pic_new |-> AcknowledgeIRQ(pic, irq)]

InitPIC == [irr |-> 0, imr |-> 255, isr |-> 0, vector_base |-> 8]

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    pic,            \* PIC state
    cpu_if,         \* CPU interrupt flag
    delivered       \* Sequence of delivered IRQs

vars == <<pic, cpu_if, delivered>>

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

TypeOK ==
    /\ WellFormedPIC(pic)
    /\ cpu_if \in BOOLEAN
    /\ delivered \in Seq(IRQLines)
    /\ Len(delivered) <= 10

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

\* Masked IRQs should never be delivered
MaskedIRQNotDelivered ==
    \A i \in 1..Len(delivered) :
        ~BitSet(pic.imr, delivered[i])

\* In-service IRQs block same-priority delivery
InServiceBlocksDelivery ==
    \A irq \in IRQLines :
        BitSet(pic.isr, irq) => irq \notin PendingIRQs(pic)

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

\* Priority test: IRQ1 and IRQ2 pending (IRR = 6 = 0b110)
PriorityInit ==
    /\ pic = [irr |-> 6, imr |-> 0, isr |-> 0, vector_base |-> 8]
    /\ cpu_if = TRUE
    /\ delivered = <<>>

\* Masking test: IRQ0 pending but masked
MaskingInit ==
    /\ pic = [irr |-> 1, imr |-> 1, isr |-> 0, vector_base |-> 8]
    /\ cpu_if = TRUE
    /\ delivered = <<>>

\* =====================================================================
\* ACTIONS
\* =====================================================================

\* Deliver an interrupt
DeliverInterruptAction ==
    LET result == DeliverInterrupt(pic, cpu_if)
    IN /\ result.delivered
       /\ pic' = result.pic_new
       /\ delivered' = Append(delivered, result.irq)
       /\ UNCHANGED cpu_if

\* Send EOI for an IRQ
SendEOIAction(irq) ==
    /\ BitSet(pic.isr, irq)
    /\ pic' = SendEOI(pic, irq)
    /\ UNCHANGED <<cpu_if, delivered>>

\* Idle
Idle == UNCHANGED vars

\* =====================================================================
\* NEXT STATE
\* =====================================================================

Next ==
    \/ DeliverInterruptAction
    \/ \E irq \in IRQLines : SendEOIAction(irq)
    \/ Idle

\* =====================================================================
\* SPECIFICATIONS
\* =====================================================================

PrioritySpec == PriorityInit /\ [][Next]_vars /\ WF_vars(DeliverInterruptAction)
MaskingSpec == MaskingInit /\ [][Next]_vars

\* =====================================================================
\* TEST PROPERTIES
\* =====================================================================

\* Priority test: IRQ1 delivered before IRQ2
PriorityCorrectResult ==
    (Len(delivered) >= 2) => (delivered[1] = 1 /\ delivered[2] = 2)

\* Masking test: IRQ0 should not be delivered (it's masked)
MaskingCorrectResult ==
    (pic.imr = 1 /\ pic.irr = 1) => (delivered = <<>>)

\* =====================================================================
\* COMBINED INVARIANTS
\* =====================================================================

AllInvariants ==
    /\ TypeOK
    /\ MaskedIRQNotDelivered
    /\ InServiceBlocksDelivery

=======================================================================
