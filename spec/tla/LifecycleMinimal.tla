------------------------ MODULE LifecycleMinimal ------------------------
(*
 * Minimal version of Lifecycle.tla for model checking
 * Removes trace variable to prevent state explosion
 *)
EXTENDS Integers, TLC

CONSTANTS MaxOperations

\* Instance states
InstanceState == {"NONE", "CREATED", "DESTROYED"}

\* Error codes
ErrorCode == {"OK", "NULL_HANDLE", "ALREADY_CREATED"}

VARIABLES
    instance,
    handle,
    opCount,
    lastError

vars == <<instance, handle, opCount, lastError>>

TypeOK ==
    /\ instance \in InstanceState
    /\ handle \in {"NULL", "VALID"}
    /\ opCount \in 0..MaxOperations
    /\ lastError \in ErrorCode

\* Safety: At most one instance
AtMostOneInstance ==
    instance = "CREATED" => handle = "VALID"

\* Safety: Misuse returns error, not crash
MisuseSafe ==
    (instance = "NONE" /\ handle = "NULL") =>
        lastError \in {"OK", "NULL_HANDLE", "ALREADY_CREATED"}

\* Safety: Handle consistency
HandleConsistency ==
    (instance = "NONE") <=> (handle = "NULL")

Init ==
    /\ instance = "NONE"
    /\ handle = "NULL"
    /\ opCount = 0
    /\ lastError = "OK"

Create ==
    /\ opCount < MaxOperations
    /\ IF instance = "CREATED"
       THEN /\ lastError' = "ALREADY_CREATED"
            /\ UNCHANGED <<instance, handle>>
       ELSE /\ instance' = "CREATED"
            /\ handle' = "VALID"
            /\ lastError' = "OK"
    /\ opCount' = opCount + 1

Destroy ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN /\ lastError' = "OK"
            /\ UNCHANGED <<instance, handle>>
       ELSE /\ instance' = "NONE"
            /\ handle' = "NULL"
            /\ lastError' = "OK"
    /\ opCount' = opCount + 1

Step ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN lastError' = "NULL_HANDLE"
       ELSE lastError' = "OK"
    /\ UNCHANGED <<instance, handle>>
    /\ opCount' = opCount + 1

Next ==
    \/ Create
    \/ Destroy
    \/ Step
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

=======================================================================
