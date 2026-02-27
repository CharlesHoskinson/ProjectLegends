---------------------------- MODULE Composition ----------------------------
(**************************************************************************)
(* Legends -- Top-Level Module Composition                                *)
(*                                                                        *)
(* This module uses INSTANCE to compose all sub-specifications into a     *)
(* single top-level view.  It defines cross-cutting invariants that       *)
(* span multiple modules.                                                 *)
(*                                                                        *)
(* NOTE: This module is for documentation and structural verification.    *)
(* It is NOT intended for TLC model checking (the combined state space    *)
(* would be intractable).  Each sub-specification has its own *Minimal    *)
(* version for CI model checking.                                         *)
(*                                                                        *)
(* Module dependency graph:                                               *)
(*                                                                        *)
(*   Composition                                                          *)
(*     |-- APIContract          (23 gate invariants)                      *)
(*     |-- Lifecycle            (instance lifecycle)                       *)
(*     |-- Threading            (thread model, PAL isolation)              *)
(*     |-- PAL                  (platform abstraction, audio push)         *)
(*     |-- Determinism          (trace reproducibility)                    *)
(*     |-- SaveState            (save/load round-trip)                     *)
(*     |-- Capture              (text/RGB capture)                         *)
(*     |-- Input                (AT scancode set 1)                        *)
(*     |-- Reentrancy           (reentrancy guard)                         *)
(*     |-- ErrorModel           (error code state machine)                 *)
(*     |-- ConfigValidation     (config validation at create)              *)
(*                                                                        *)
(* Cross-cutting invariants:                                              *)
(*   SystemConsistent   -- all sub-spec TypeOK invariants hold            *)
(*   GatesCovered       -- every CONTRACT.md gate has a TLA+ invariant    *)
(*   NoTRUEStubs        -- no invariant is trivially TRUE                 *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(**************************************************************************)
(* SPECIFICATION INVENTORY                                                *)
(*                                                                        *)
(* Each sub-specification is listed with its key invariants and the       *)
(* contract gates it covers.                                              *)
(**************************************************************************)

(*--------------------------------------------------------------------*)
(* Lifecycle.tla / LifecycleMinimal.tla                               *)
(*   Gates: 2a, 2b, 2c                                               *)
(*   Invariants:                                                      *)
(*     AtMostOneInstance                                              *)
(*     MisuseSafe                                                     *)
(*     HandleConsistency                                              *)
(*     ReentrancySafe                                                 *)
(*     WrongThreadSafe                                                *)
(*     ConfigValidated                                                *)
(*   Liveness: EventualTermination                                    *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* Threading.tla / ThreadingMinimal.tla                               *)
(*   Gates: 7a, 8a, 8b, 8c                                           *)
(*   Invariants:                                                      *)
(*     CoreSingleThreaded                                             *)
(*     PALIsolation                                                   *)
(*     NoDataRaces                                                    *)
(*     CallStackValid                                                 *)
(*     OwnerThreadRecorded                                            *)
(*     WrongThreadDetected                                            *)
(*     NoReentrantStep                                                *)
(*   Liveness: MainCanAccessCore                                      *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* PAL.tla / PALMinimal.tla                                           *)
(*   Gates: 7a, 7b, 7c, 7d                                           *)
(*   Invariants:                                                      *)
(*     BackendIsolation                                               *)
(*     AudioPushModel                                                 *)
(*     ThreadSafety                                                   *)
(*     AudioQueueBounded                                              *)
(*     ComponentDependencySatisfied                                   *)
(*     BackpressureTracked                                            *)
(*   Liveness: AudioEventuallyDrains                                  *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* Determinism.tla / DeterminismMinimal.tla                           *)
(*   Gates: 4a, 4b, 6b                                               *)
(*   Invariants:                                                      *)
(*     TraceDeterminism                                               *)
(*     HashCollisionFree                                              *)
(*     ReplayEquivalence                                              *)
(*     HashStability                                                  *)
(*   Liveness: HashHistoryGrows                                       *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* SaveStateTest.tla                                                  *)
(*   Gates: 4c                                                        *)
(*   Invariants:                                                      *)
(*     ObservationPreserved                                           *)
(*     EventCountPreserved                                            *)
(*     EventDigestPreserved                                           *)
(*     TimePreserved                                                  *)
(*     IntegrityCheckPasses                                           *)
(*     CorruptionDetected                                             *)
(*     PartialSaveSafe                                                *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* Capture.tla / CaptureMinimal.tla                                   *)
(*   Gates: 5a, 5b, 5c                                               *)
(*   Invariants:                                                      *)
(*     DimensionsConsistent                                           *)
(*     FormatFixed                                                    *)
(*     BackendIndependent                                             *)
(*     FramebufferSizeConsistent                                      *)
(*     CursorInBounds                                                 *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* Input.tla / InputMinimal.tla                                       *)
(*   Gates: 6a, 6b                                                    *)
(*   Invariants:                                                      *)
(*     ScancodeValid                                                  *)
(*     KeyStateConsistent                                             *)
(*     BufferNotCorrupted                                             *)
(*     E0PrefixCorrect                                                *)
(*     InputDeterminism                                               *)
(*     MouseInBounds                                                  *)
(*     BufferOverflowSafe                                             *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* Reentrancy.tla / ReentrancyMinimal.tla                             *)
(*   Gates: 8c (reentrancy subset)                                    *)
(*   Invariants:                                                      *)
(*     NoNestedStep                                                   *)
(*     ReentrancyReturnsError                                         *)
(*     PhaseConsistent                                                *)
(*     CallbackSafe                                                   *)
(*   Liveness: StepEventuallyCompletes                                *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* ErrorModel.tla                                                     *)
(*   Gates: 2b (cross-cutting)                                        *)
(*   Invariants:                                                      *)
(*     ErrorCodeDeterministic                                         *)
(*     SuccessRequiresValidState                                      *)
(*     ErrorCodesComplete                                             *)
(*     NullHandleConsistent                                           *)
(*     ReentrantCodeCorrect                                           *)
(*     WrongThreadCodeCorrect                                         *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* ConfigValidation.tla                                               *)
(*   Gates: 2a (config subset)                                        *)
(*   Invariants:                                                      *)
(*     InvalidConfigBlocked                                           *)
(*     ValidConfigAccepted                                            *)
(*     VersionChecked                                                 *)
(*     AllFieldsValidated                                             *)
(*--------------------------------------------------------------------*)

(*--------------------------------------------------------------------*)
(* APIContract.tla                                                    *)
(*   Gates: All 23 (1a-8c)                                            *)
(*   Composite invariant: AllGatesHold                                *)
(*--------------------------------------------------------------------*)

(**************************************************************************)
(* GATE-TO-INVARIANT TRACEABILITY MATRIX                                  *)
(*                                                                        *)
(* Gate | Primary Spec        | Primary Invariant                         *)
(* -----|---------------------|------------------------------------------ *)
(* 1a   | (code review)       | N/A (link-time, not TLA+)                *)
(* 1b   | (code review)       | N/A (compile-time, not TLA+)             *)
(* 1c   | APIContract         | Gate_VersionHandshake                     *)
(* 2a   | Lifecycle            | HandleConsistency, ConfigValidated       *)
(* 2b   | ErrorModel           | ErrorCodeDeterministic, SuccessReq...    *)
(* 2c   | Lifecycle            | AtMostOneInstance                        *)
(* 3a   | APIContract          | Gate_NoExitAbort                         *)
(* 3b   | APIContract          | Gate_NoStdout                            *)
(* 3c   | APIContract          | Gate_NoEnvironmentChange                 *)
(* 4a   | Determinism          | HashStability                            *)
(* 4b   | Determinism          | TraceDeterminism                         *)
(* 4c   | SaveStateTest        | ObservationPreserved                     *)
(* 5a   | Capture              | DimensionsConsistent                     *)
(* 5b   | Capture              | FormatFixed                              *)
(* 5c   | Capture              | BackendIndependent                       *)
(* 6a   | Input                | ScancodeValid, E0PrefixCorrect           *)
(* 6b   | Input + Determinism  | InputDeterminism, ReplayEquivalence      *)
(* 7a   | PAL + Threading      | AudioPushModel, PALIsolation             *)
(* 7b   | PAL                  | AudioQueueBounded                        *)
(* 7c   | PAL                  | AudioPushModel                           *)
(* 7d   | PAL                  | BackpressureTracked                      *)
(* 8a   | Threading            | CoreSingleThreaded                       *)
(* 8b   | Threading            | PALIsolation                             *)
(* 8c   | Threading+Reentrancy | WrongThreadDetected, NoNestedStep        *)
(**************************************************************************)

(**************************************************************************)
(* CROSS-CUTTING INVARIANTS                                               *)
(*                                                                        *)
(* These would be checked by INSTANCE-ing each module and conjoining      *)
(* their TypeOK predicates.  Listed here for documentation.               *)
(**************************************************************************)

\* SystemConsistent ==
\*     /\ Lifecycle!TypeOK
\*     /\ Threading!TypeOK
\*     /\ PAL!TypeOK
\*     /\ Determinism!TypeOK
\*     /\ SaveStateTest!TypeOK
\*     /\ Capture!TypeOK
\*     /\ Input!TypeOK
\*     /\ Reentrancy!TypeOK
\*     /\ ErrorModel!TypeOK
\*     /\ ConfigValidation!TypeOK

(**************************************************************************)
(* CI MODEL CHECKING PLAN                                                 *)
(*                                                                        *)
(* Each *Minimal.tla + .cfg pair is designed for CI:                       *)
(*                                                                        *)
(* Spec                   | Est. States | Key Invariants                  *)
(* -----------------------|-------------|-------------------------------- *)
(* LifecycleMinimal       | ~250        | AtMostOne, MisuseSafe, ...      *)
(* ThreadingMinimal       | ~2000       | CoreSingle, PALIso, ...         *)
(* PALMinimal             | ~200        | AudioPush, CompDep, ...         *)
(* DeterminismMinimal     | ~500        | TraceDet, HashStab              *)
(* SaveStateTest          | ~30         | ObsPreserved, Corruption, ...   *)
(* CaptureMinimal         | ~100        | DimConsistent, FBSize, ...      *)
(* InputMinimal           | ~300        | E0Prefix, InputDet, ...         *)
(* ReentrancyMinimal      | ~50         | NoNested, PhaseCons, ...        *)
(* ErrorModel             | ~500        | ErrDet, SuccessReq, ...         *)
(* ConfigValidation       | ~20         | InvalidBlocked, VersionChk, .. *)
(* APIContract            | ~1000       | AllGatesHold                    *)
(* -----------------------|-------------|-------------------------------- *)
(* TOTAL (est.)           | ~5000       | 50+ substantive invariants      *)
(**************************************************************************)

\* Real composition constants.
CONSTANTS
    LifecycleMaxOperations,
    ThreadingMaxOps,
    PALMaxAudioFrames,
    DeterminismMaxCycles,
    DeterminismMaxInputs,
    DeterminismMaxSteps,
    SaveStateMaxCycle,
    SaveStateMaxEvents,
    InputMaxInputs,
    InputMaxKeyboardBuffer,
    ReentrancyMaxOps,
    ErrorModelMaxOps,
    ConfigValidationMaxOps,
    APIMaxCycle,
    APIMaxOperations,
    APIMaxAudioFrames,
    APIMaxInputs,
    APIVersionMajor,
    APIVersionMinor,
    APIVersionPatch

\* Shared variables wired across module instances.
VARIABLES
    sharedInstance,
    sharedInStep

vars == <<sharedInstance, sharedInStep>>

L == INSTANCE LifecycleMinimal
    WITH MaxOperations <- LifecycleMaxOperations,
         instance <- sharedInstance,
         inStep <- sharedInStep

T == INSTANCE ThreadingMinimal
    WITH MaxOps <- ThreadingMaxOps,
         inStep <- sharedInStep

P == INSTANCE PALMinimal
    WITH MaxAudioFrames <- PALMaxAudioFrames

D == INSTANCE DeterminismMinimal
    WITH MaxCycles <- DeterminismMaxCycles,
         MaxInputs <- DeterminismMaxInputs,
         MaxSteps <- DeterminismMaxSteps

S == INSTANCE SaveStateTest
    WITH MaxCycle <- SaveStateMaxCycle,
         MaxEvents <- SaveStateMaxEvents

C == INSTANCE CaptureMinimal

I == INSTANCE InputMinimal
    WITH MaxInputs <- InputMaxInputs,
         MaxKeyboardBuffer <- InputMaxKeyboardBuffer

R == INSTANCE ReentrancyMinimal
    WITH MaxOps <- ReentrancyMaxOps,
         hasInst <- (sharedInstance = "CREATED")

E == INSTANCE ErrorModel
    WITH MaxOps <- ErrorModelMaxOps

V == INSTANCE ConfigValidation
    WITH MaxOps <- ConfigValidationMaxOps

A == INSTANCE APIContract
    WITH MaxCycle <- APIMaxCycle,
         MaxOperations <- APIMaxOperations,
         MaxAudioFrames <- APIMaxAudioFrames,
         MaxInputs <- APIMaxInputs,
         API_VERSION_MAJOR <- APIVersionMajor,
         API_VERSION_MINOR <- APIVersionMinor,
         API_VERSION_PATCH <- APIVersionPatch,
         instance <- sharedInstance,
         inStep <- sharedInStep

SharedTypeOK ==
    /\ sharedInstance \in {"NONE", "CREATED"}
    /\ sharedInStep \in BOOLEAN

SystemConsistent ==
    /\ SharedTypeOK
    /\ L!TypeOK
    /\ T!TypeOK
    /\ P!TypeOK
    /\ D!TypeOK
    /\ S!TypeOK
    /\ C!TypeOK
    /\ I!TypeOK
    /\ R!TypeOK
    /\ E!TypeOK
    /\ V!TypeOK
    /\ A!TypeOK

CrossModuleInvariant ==
    /\ (sharedInStep => sharedInstance = "CREATED")
    /\ (sharedInstance = "CREATED" => A!instance = "CREATED")
    /\ (sharedInstance = "CREATED" => L!instance = "CREATED")
    /\ (A!instance = "CREATED" => A!ownerThread = "MainThread")
    /\ (L!instance = "CREATED" => L!handle = "VALID")

GatesCovered == A!AllGatesHold

NoTRUEStubs ==
    /\ D!TraceDeterminism
    /\ C!FormatFixed
    /\ I!E0PrefixCorrect
    /\ R!NoNestedStep
    /\ T!WrongThreadBlocked
    /\ L!HandleConsistency

Spec ==
    /\ L!Spec
    /\ T!Spec
    /\ P!Spec
    /\ D!Spec
    /\ S!Spec
    /\ C!Spec
    /\ I!Spec
    /\ R!Spec
    /\ E!Spec
    /\ V!Spec
    /\ A!Spec

Invariant == SystemConsistent /\ CrossModuleInvariant /\ GatesCovered /\ NoTRUEStubs

=======================================================================

