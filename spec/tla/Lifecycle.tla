---------------------------- MODULE Lifecycle ----------------------------
(*
 * Legends API - Instance Lifecycle Contract
 *
 * This module specifies the lifecycle of emulator instances, including:
 * - Single-instance-per-process rule (v1)
 * - Create/destroy state machine
 * - Error handling for misuse
 *
 * Key invariants:
 * - AtMostOneInstance: At most one active instance at any time
 * - MisuseSafe: Invalid operations return errors, never crash
 * - CreateDestroyLoop: Repeated create/destroy cycles work correctly
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* =====================================================================
\* CONSTANTS
\* =====================================================================
CONSTANTS
    MaxOperations   \* Maximum API calls to model-check

\* =====================================================================
\* TYPES
\* =====================================================================

\* API error codes (matching legends_embed.h)
ErrorCode == {
    "OK",                   \* LEGENDS_OK = 0
    "NULL_HANDLE",          \* LEGENDS_ERR_NULL_HANDLE = -1
    "NULL_POINTER",         \* LEGENDS_ERR_NULL_POINTER = -2
    "ALREADY_CREATED",      \* LEGENDS_ERR_ALREADY_CREATED = -3
    "NOT_INITIALIZED",      \* LEGENDS_ERR_NOT_INITIALIZED = -4
    "VERSION_MISMATCH",     \* LEGENDS_ERR_VERSION_MISMATCH = -9
    "INVALID_CONFIG"        \* LEGENDS_ERR_INVALID_CONFIG = -7
}

\* Instance states
InstanceState == {"NONE", "CREATED", "INITIALIZED", "DESTROYED"}

\* API operations
Operation == {
    "CREATE",           \* legends_create()
    "DESTROY",          \* legends_destroy()
    "RESET",            \* legends_reset()
    "STEP",             \* legends_step_ms() / legends_step_cycles()
    "CAPTURE",          \* legends_capture_text() / legends_capture_rgb()
    "INPUT",            \* legends_key_event() / legends_mouse_event()
    "SAVE",             \* legends_save_state()
    "LOAD"              \* legends_load_state()
}

\* =====================================================================
\* VARIABLES
\* =====================================================================
VARIABLES
    instance,       \* Current instance state
    handle,         \* Handle value (NULL or valid)
    opCount,        \* Operation counter
    lastError,      \* Last error code
    trace           \* Operation trace for debugging

vars == <<instance, handle, opCount, lastError, trace>>

\* =====================================================================
\* TYPE INVARIANT
\* =====================================================================

TypeOK ==
    /\ instance \in InstanceState
    /\ handle \in {"NULL", "VALID"}
    /\ opCount \in 0..MaxOperations
    /\ lastError \in ErrorCode
    /\ trace \in Seq(Operation)

\* =====================================================================
\* SAFETY INVARIANTS
\* =====================================================================

(*
 * AtMostOneInstance - v1 single-instance-per-process rule
 *
 * There can be at most one active (CREATED/INITIALIZED) instance.
 * This is enforced by returning ALREADY_CREATED on second create.
 *)
AtMostOneInstance ==
    instance \in {"CREATED", "INITIALIZED"} =>
        handle = "VALID"

(*
 * MisuseSafe - Invalid operations return errors, never crash
 *
 * Operations on invalid handles return appropriate error codes.
 * The system never enters an undefined state.
 *)
MisuseSafe ==
    \* If no instance, operations that need one fail gracefully
    /\ (instance = "NONE" /\ handle = "NULL") =>
        lastError \in {"OK", "NULL_HANDLE", "NULL_POINTER", "ALREADY_CREATED"}
    \* Valid instance has valid handle
    /\ (instance \in {"CREATED", "INITIALIZED"}) => handle = "VALID"

(*
 * HandleConsistency - Handle state matches instance state
 *)
HandleConsistency ==
    /\ (instance = "NONE") <=> (handle = "NULL")
    /\ (instance \in {"CREATED", "INITIALIZED"}) <=> (handle = "VALID")

\* =====================================================================
\* INITIALIZATION
\* =====================================================================

Init ==
    /\ instance = "NONE"
    /\ handle = "NULL"
    /\ opCount = 0
    /\ lastError = "OK"
    /\ trace = <<>>

\* =====================================================================
\* ACTIONS - API OPERATIONS
\* =====================================================================

(*
 * legends_create(config, &handle)
 *
 * Creates a new emulator instance.
 * - Returns ALREADY_CREATED if instance exists
 * - Returns INVALID_CONFIG if config is invalid
 * - Returns VERSION_MISMATCH if API version doesn't match
 * - Returns OK and sets handle on success
 *)
Create ==
    /\ opCount < MaxOperations
    /\ IF instance \in {"CREATED", "INITIALIZED"}
       THEN \* Already have an instance
            /\ lastError' = "ALREADY_CREATED"
            /\ UNCHANGED <<instance, handle>>
       ELSE \* Can create new instance
            /\ instance' = "INITIALIZED"  \* Created and initialized
            /\ handle' = "VALID"
            /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "CREATE")

(*
 * legends_destroy(handle)
 *
 * Destroys an emulator instance.
 * - Returns OK for NULL handle (no-op)
 * - Returns OK and destroys instance
 *)
Destroy ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN \* NULL handle is OK (no-op)
            /\ lastError' = "OK"
            /\ UNCHANGED <<instance, handle>>
       ELSE \* Destroy the instance
            /\ instance' = "NONE"
            /\ handle' = "NULL"
            /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "DESTROY")

(*
 * legends_step_ms(handle, ms, &result) / legends_step_cycles(...)
 *
 * Steps the emulator.
 * - Returns NULL_HANDLE if handle is NULL
 * - Returns OK on success
 *)
Step ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN
            /\ lastError' = "NULL_HANDLE"
            /\ UNCHANGED <<instance, handle>>
       ELSE
            /\ lastError' = "OK"
            /\ UNCHANGED <<instance, handle>>
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "STEP")

(*
 * legends_reset(handle)
 *
 * Resets the emulator to initial state.
 * - Returns NULL_HANDLE if handle is NULL
 * - Returns OK on success
 *)
Reset ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN
            /\ lastError' = "NULL_HANDLE"
            /\ UNCHANGED <<instance, handle>>
       ELSE
            /\ lastError' = "OK"
            /\ UNCHANGED <<instance, handle>>
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "RESET")

(*
 * legends_capture_text / legends_capture_rgb
 *
 * Captures screen content.
 * - Returns NULL_HANDLE if handle is NULL
 *)
Capture ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN lastError' = "NULL_HANDLE"
       ELSE lastError' = "OK"
    /\ UNCHANGED <<instance, handle>>
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "CAPTURE")

(*
 * legends_key_event / legends_mouse_event
 *
 * Injects input.
 * - Returns NULL_HANDLE if handle is NULL
 *)
Input ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN lastError' = "NULL_HANDLE"
       ELSE lastError' = "OK"
    /\ UNCHANGED <<instance, handle>>
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "INPUT")

(*
 * legends_save_state / legends_load_state
 *
 * Save/load state.
 * - Returns NULL_HANDLE if handle is NULL
 *)
SaveLoad ==
    /\ opCount < MaxOperations
    /\ IF handle = "NULL"
       THEN lastError' = "NULL_HANDLE"
       ELSE lastError' = "OK"
    /\ UNCHANGED <<instance, handle>>
    /\ opCount' = opCount + 1
    /\ trace' = Append(trace, "SAVE")

\* =====================================================================
\* NEXT STATE RELATION
\* =====================================================================

Next ==
    \/ Create
    \/ Destroy
    \/ Step
    \/ Reset
    \/ Capture
    \/ Input
    \/ SaveLoad
    \/ UNCHANGED vars  \* Stuttering

\* =====================================================================
\* SPECIFICATION
\* =====================================================================

Spec == Init /\ [][Next]_vars

\* =====================================================================
\* PROPERTIES
\* =====================================================================

(*
 * CreateDestroyLoop - Can create/destroy repeatedly
 *
 * This property ensures that after destroying an instance,
 * a new one can be created successfully.
 *)
CreateDestroyLoop ==
    [](instance = "NONE" =>
       <>(instance \in {"CREATED", "INITIALIZED"}))

(*
 * EventualDestruction - Created instances can be destroyed
 *)
EventualDestruction ==
    [](instance \in {"CREATED", "INITIALIZED"} =>
       <>(instance = "NONE"))

(*
 * NoOrphanedHandles - Handle is NULL when no instance exists
 *)
NoOrphanedHandles ==
    [](instance = "NONE" => handle = "NULL")

=======================================================================
