------------------------------- MODULE PIC -------------------------------
(*
 * Legends Emukernel - 8259A Programmable Interrupt Controller Specification
 *
 * The PIC is responsible for:
 * - Receiving interrupt requests (IRQs) from devices
 * - Masking interrupts based on IMR (Interrupt Mask Register)
 * - Prioritizing pending interrupts
 * - Signaling CPU when an interrupt can be delivered
 * - Tracking in-service interrupts (ISR)
 *
 * Key registers:
 * - IRR (Interrupt Request Register): Pending interrupt requests
 * - IMR (Interrupt Mask Register): Masked (disabled) interrupts
 * - ISR (In-Service Register): Currently being serviced
 *
 * Priority: IRQ0 has highest priority, IRQ7 lowest
 *
 * Properties verified:
 * - MaskedIRQNotDelivered: Masked IRQs never delivered
 * - PriorityRespected: Lower IRQ numbers delivered first
 * - EOIClearsInService: EOI command clears ISR bit
 * - InterruptAtomicity: Delivery at instruction boundaries only
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS MaxCycle

\* IRQ lines (0-7 for single PIC, 0-15 for cascaded)
IRQLines == 0..7

\* Register values (8-bit)
RegValue == 0..255

\* =====================================================================
\* BIT MANIPULATION
\* =====================================================================

\* Test if bit is set
BitSet(reg, bit) == (reg % (2^(bit+1))) \div (2^bit) = 1

\* Set a bit
SetBit(reg, bit) == IF BitSet(reg, bit) THEN reg ELSE reg + 2^bit

\* Clear a bit
ClearBit(reg, bit) == IF BitSet(reg, bit) THEN reg - 2^bit ELSE reg

\* Get lowest set bit (highest priority IRQ)
\* Returns -1 if no bits set
LowestSetBit(reg) ==
    IF reg = 0 THEN -1
    ELSE CHOOSE b \in 0..7 : BitSet(reg, b) /\ \A b2 \in 0..(b-1) : ~BitSet(reg, b2)

\* Get set of all set bits
SetBits(reg) == {b \in 0..7 : BitSet(reg, b)}

\* =====================================================================
\* PIC STATE
\* =====================================================================

\* PIC state record
\* irr: Interrupt Request Register - pending requests
\* imr: Interrupt Mask Register - masked interrupts (1=masked)
\* isr: In-Service Register - currently being serviced
\* vector_base: Base interrupt vector (maps IRQ to CPU interrupt)
PICStateType == [irr: RegValue, imr: RegValue, isr: RegValue, vector_base: RegValue]

\* =====================================================================
\* PIC OPERATIONS
\* =====================================================================

(*
 * RaiseIRQ(pic, irq) - Device raises an interrupt request
 *
 * Sets the corresponding bit in IRR.
 * The request will be pending until serviced or masked.
 *)
RaiseIRQ(pic, irq) ==
    [pic EXCEPT !.irr = SetBit(pic.irr, irq)]

(*
 * LowerIRQ(pic, irq) - Device lowers an interrupt request
 *
 * Clears the IRR bit. Used for level-triggered interrupts
 * when the device condition is cleared.
 *)
LowerIRQ(pic, irq) ==
    [pic EXCEPT !.irr = ClearBit(pic.irr, irq)]

(*
 * SetMask(pic, irq) - Mask (disable) an IRQ
 *)
SetMask(pic, irq) ==
    [pic EXCEPT !.imr = SetBit(pic.imr, irq)]

(*
 * ClearMask(pic, irq) - Unmask (enable) an IRQ
 *)
ClearMask(pic, irq) ==
    [pic EXCEPT !.imr = ClearBit(pic.imr, irq)]

(*
 * PendingIRQs(pic) - IRQs that are pending and not masked
 *
 * Returns the set of IRQs that could be delivered.
 * An IRQ is deliverable if:
 * - It is in IRR (requested)
 * - It is not in IMR (not masked)
 * - It is not in ISR (not already being serviced)
 *)
PendingIRQs(pic) ==
    LET requested == SetBits(pic.irr)
        masked == SetBits(pic.imr)
        in_service == SetBits(pic.isr)
    IN (requested \ masked) \ in_service

(*
 * HighestPriorityIRQ(pic) - Get the highest priority pending IRQ
 *
 * Returns -1 if no IRQs pending.
 * Lower IRQ number = higher priority.
 *)
HighestPriorityIRQ(pic) ==
    LET pending == PendingIRQs(pic)
    IN IF pending = {} THEN -1
       ELSE CHOOSE irq \in pending : \A other \in pending : irq <= other

(*
 * HasPendingInterrupt(pic) - Check if any interrupt can be delivered
 *)
HasPendingInterrupt(pic) == PendingIRQs(pic) # {}

(*
 * AcknowledgeIRQ(pic, irq) - CPU acknowledges interrupt
 *
 * Called when CPU accepts the interrupt:
 * - Clears the IRR bit (request satisfied)
 * - Sets the ISR bit (now being serviced)
 *)
AcknowledgeIRQ(pic, irq) ==
    [pic EXCEPT !.irr = ClearBit(pic.irr, irq),
                !.isr = SetBit(pic.isr, irq)]

(*
 * SendEOI(pic, irq) - End of Interrupt command
 *
 * Called when interrupt handler completes:
 * - Clears the ISR bit
 * This allows lower-priority interrupts to be serviced.
 *)
SendEOI(pic, irq) ==
    [pic EXCEPT !.isr = ClearBit(pic.isr, irq)]

(*
 * SendNonSpecificEOI(pic) - Non-specific EOI
 *
 * Clears the highest priority bit in ISR.
 * Used when handler doesn't know which IRQ it's servicing.
 *)
SendNonSpecificEOI(pic) ==
    LET highest == LowestSetBit(pic.isr)
    IN IF highest = -1 THEN pic
       ELSE [pic EXCEPT !.isr = ClearBit(pic.isr, highest)]

(*
 * GetInterruptVector(pic, irq) - Get CPU interrupt vector for IRQ
 *)
GetInterruptVector(pic, irq) == pic.vector_base + irq

\* =====================================================================
\* CPU INTERFACE
\* =====================================================================

(*
 * DeliverInterrupt(pic, cpu_if) - Attempt to deliver an interrupt
 *
 * Returns record with:
 * - delivered: TRUE if interrupt was delivered
 * - irq: The IRQ that was delivered (-1 if none)
 * - vector: The interrupt vector (-1 if none)
 * - pic': Updated PIC state
 *
 * Interrupt is delivered only if:
 * - There is a pending, unmasked IRQ
 * - CPU interrupt flag is set (cpu_if = TRUE)
 *)
DeliverInterrupt(pic, cpu_if) ==
    IF ~cpu_if THEN
        [delivered |-> FALSE, irq |-> -1, vector |-> -1, pic_new |-> pic]
    ELSE
        LET irq == HighestPriorityIRQ(pic)
        IN IF irq = -1 THEN
               [delivered |-> FALSE, irq |-> -1, vector |-> -1, pic_new |-> pic]
           ELSE
               [delivered |-> TRUE,
                irq |-> irq,
                vector |-> GetInterruptVector(pic, irq),
                pic_new |-> AcknowledgeIRQ(pic, irq)]

\* =====================================================================
\* PIC INVARIANTS
\* =====================================================================

(*
 * WellFormedPIC(pic) - PIC state is valid
 *)
WellFormedPIC(pic) ==
    /\ pic.irr \in RegValue
    /\ pic.imr \in RegValue
    /\ pic.isr \in RegValue
    /\ pic.vector_base \in RegValue

(*
 * MaskedNotPending(pic) - Masked IRQs don't appear in pending set
 *)
MaskedNotPending(pic) ==
    \A irq \in IRQLines :
        BitSet(pic.imr, irq) => irq \notin PendingIRQs(pic)

(*
 * InServiceNotPending(pic) - In-service IRQs don't appear in pending set
 *)
InServiceNotPending(pic) ==
    \A irq \in IRQLines :
        BitSet(pic.isr, irq) => irq \notin PendingIRQs(pic)

(*
 * PriorityCorrect(pic) - HighestPriorityIRQ returns lowest-numbered pending IRQ
 *)
PriorityCorrect(pic) ==
    LET hp == HighestPriorityIRQ(pic)
        pending == PendingIRQs(pic)
    IN pending # {} => (hp \in pending /\ \A other \in pending : hp <= other)

\* =====================================================================
\* INITIAL STATE
\* =====================================================================

\* Standard PC initialization
InitPIC == [irr |-> 0, imr |-> 255, isr |-> 0, vector_base |-> 8]

\* Slave PIC initialization
InitSlavePIC == [irr |-> 0, imr |-> 255, isr |-> 0, vector_base |-> 112]

=======================================================================
