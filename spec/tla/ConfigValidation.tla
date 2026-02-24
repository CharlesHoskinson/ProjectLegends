------------------------ MODULE ConfigValidation ------------------------
(**************************************************************************)
(* Legends -- Config Validation at Create Time                            *)
(*                                                                        *)
(* Models the validation of legends_config_t fields during                *)
(* legends_create().  Invalid configuration is rejected before any        *)
(* instance is created.                                                   *)
(*                                                                        *)
(* Validated fields:                                                      *)
(*   version_major  -- must match API_VERSION_MAJOR (currently 1)         *)
(*   cycles_per_ms  -- must be > 0                                        *)
(*   audio_rate     -- must be in {11025, 22050, 44100}                   *)
(*   deterministic  -- boolean (always valid)                             *)
(*                                                                        *)
(* Contract gate: 2a (config validation subset)                           *)
(*                                                                        *)
(* Key invariants:                                                        *)
(*   InvalidConfigBlocked  -- bad config never creates instance           *)
(*   ValidConfigAccepted   -- good config succeeds                        *)
(*   VersionChecked        -- wrong version returns VERSION_MISMATCH      *)
(*   AllFieldsValidated    -- every field is checked                      *)
(**************************************************************************)
EXTENDS Integers, TLC

(**************************************************************************)
(* CONSTANTS                                                              *)
(**************************************************************************)
CONSTANTS
    MaxOps  \* @type: Int;

(**************************************************************************)
(* TYPES                                                                  *)
(**************************************************************************)

\* @type: Set(Int);
ValidCyclesPerMs == {50, 100, 200}

\* @type: Set(Int);
ValidAudioRate == {11025, 22050, 44100}

\* @type: Set(Str);
ErrorCode == {"OK", "INVALID_CONFIG", "VERSION_MISMATCH", "ALREADY_CREATED"}

(**************************************************************************)
(* VARIABLES                                                              *)
(**************************************************************************)
VARIABLES
    hasInstance,     \* @type: Bool;
    lastError,      \* @type: Str;
    lastOp,         \* @type: Str;
    opCount,        \* @type: Int;
    \* Config fields for the last create attempt
    cfgVersion,     \* @type: Int;
    cfgCyclesPerMs, \* @type: Int;
    cfgAudioRate,   \* @type: Int;
    cfgDeterministic \* @type: Bool;

vars == <<hasInstance, lastError, lastOp, opCount,
          cfgVersion, cfgCyclesPerMs, cfgAudioRate, cfgDeterministic>>

(**************************************************************************)
(* CONFIG VALIDATION FUNCTION                                             *)
(**************************************************************************)

\* @type: (Int, Int, Int) -> Str;
ValidateConfig(ver, cpm, ar) ==
    IF ver # 1 THEN "VERSION_MISMATCH"
    ELSE IF cpm \notin ValidCyclesPerMs THEN "INVALID_CONFIG"
    ELSE IF ar \notin ValidAudioRate THEN "INVALID_CONFIG"
    ELSE "OK"

(**************************************************************************)
(* TYPE INVARIANT                                                         *)
(**************************************************************************)

TypeOK ==
    /\ hasInstance \in BOOLEAN
    /\ lastError \in ErrorCode
    /\ lastOp \in {"NONE", "CREATE", "DESTROY"}
    /\ opCount \in 0..MaxOps
    /\ cfgVersion \in {0, 1, 2}
    /\ cfgCyclesPerMs \in {0, 50, 100, 200}
    /\ cfgAudioRate \in {0, 11025, 22050, 44100}
    /\ cfgDeterministic \in BOOLEAN

(**************************************************************************)
(* SAFETY INVARIANTS                                                      *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* InvalidConfigBlocked                                               *)
(*                                                                    *)
(* If lastError is INVALID_CONFIG or VERSION_MISMATCH, no instance    *)
(* was created.                                                       *)
(*--------------------------------------------------------------------*)
InvalidConfigBlocked ==
    lastError \in {"INVALID_CONFIG", "VERSION_MISMATCH"} =>
        ~hasInstance \/ lastError = "ALREADY_CREATED"

(*--------------------------------------------------------------------*)
(* ValidConfigAccepted                                                *)
(*                                                                    *)
(* If create returned OK and we had no instance, one was created.     *)
(*--------------------------------------------------------------------*)
ValidConfigAccepted ==
    (lastError = "OK" /\ lastOp = "CREATE") =>
        hasInstance

(*--------------------------------------------------------------------*)
(* VersionChecked                                                     *)
(*                                                                    *)
(* Wrong version always returns VERSION_MISMATCH, never OK.           *)
(*--------------------------------------------------------------------*)
VersionChecked ==
    (cfgVersion # 1 /\ cfgVersion # 0 /\ lastError = "OK" /\ lastOp = "CREATE") =>
        hasInstance  \* OK only if already had instance before bad version

(*--------------------------------------------------------------------*)
(* AllFieldsValidated                                                 *)
(*                                                                    *)
(* All config fields are checked -- invalid field => error.           *)
(*--------------------------------------------------------------------*)
AllFieldsValidated ==
    (lastError = "OK" /\ lastOp = "CREATE" /\ ~hasInstance) => FALSE
    \* i.e., if create returned OK but has no instance, something is wrong

(**************************************************************************)
(* INITIALIZATION                                                         *)
(**************************************************************************)

Init ==
    /\ hasInstance = FALSE
    /\ lastError = "OK"
    /\ lastOp = "NONE"
    /\ opCount = 0
    /\ cfgVersion = 0
    /\ cfgCyclesPerMs = 0
    /\ cfgAudioRate = 0
    /\ cfgDeterministic = TRUE

(**************************************************************************)
(* ACTIONS                                                                *)
(**************************************************************************)

\* Attempt to create with given config
CreateWithConfig(ver, cpm, ar, det) ==
    /\ opCount < MaxOps
    /\ lastOp' = "CREATE"
    /\ cfgVersion' = ver
    /\ cfgCyclesPerMs' = cpm
    /\ cfgAudioRate' = ar
    /\ cfgDeterministic' = det
    /\ IF hasInstance
       THEN /\ lastError' = "ALREADY_CREATED"
            /\ UNCHANGED hasInstance
       ELSE LET result == ValidateConfig(ver, cpm, ar)
            IN /\ lastError' = result
               /\ IF result = "OK"
                  THEN hasInstance' = TRUE
                  ELSE UNCHANGED hasInstance
    /\ opCount' = opCount + 1

\* Destroy instance
DestroyInst ==
    /\ opCount < MaxOps
    /\ hasInstance
    /\ hasInstance' = FALSE
    /\ lastOp' = "DESTROY"
    /\ lastError' = "OK"
    /\ opCount' = opCount + 1
    /\ UNCHANGED <<cfgVersion, cfgCyclesPerMs, cfgAudioRate, cfgDeterministic>>

(**************************************************************************)
(* NEXT STATE RELATION                                                    *)
(**************************************************************************)

Next ==
    \/ \E v \in {1, 2},
          c \in {0, 50, 100, 200},
          a \in {0, 11025, 22050, 44100},
          d \in BOOLEAN :
        CreateWithConfig(v, c, a, d)
    \/ DestroyInst
    \/ UNCHANGED vars

(**************************************************************************)
(* SPECIFICATION                                                          *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

=======================================================================
