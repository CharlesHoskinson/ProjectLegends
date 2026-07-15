<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Charles Hoskinson and Contributors
-->

# ProjectLegends Go Headless Nucleus — Behavioral Contract

Date: 2026-07-15
Status: draft for sponsor and clean-room admission review
Contract version: 1
License: Apache-2.0

## 1. Purpose

This document is the normative milestone-one contract for the independent Go
implementation. It defines observable behavior without prescribing internal
algorithms or copying a legacy ABI. The implementation is conforming only when
it satisfies this contract and every admitted conformance vector.

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL are interpreted as described by RFC 2119 and
RFC 8174 when written in uppercase.

Bracketed identifiers in headings are immutable requirement-group IDs. Every
normative statement under such a heading belongs to that group until the next
identified heading. Tests MAY use a more specific exchange-catalog child ID,
but every child ID maps to exactly one group and is never reassigned.

## 2. Scope

The headless nucleus provides:

- explicit creation, reset, close, and use-after-close behavior;
- deterministic integer-cycle stepping;
- a bounded timestamped input queue;
- canonical text and RGBA capture surfaces;
- canonical versioned snapshots with atomic load;
- a stable SHA-256 observable-state hash;
- typed, stable error codes and capability discovery;
- a scripted execution core for contract validation.

It does not claim x86, PC, BIOS, DOS, game, audio, network, or legacy
ProjectLegends compatibility.

## 3. Public Go package

The public package name is **legends**. The implementation repository chooses
its module path once; module-path changes do not alter this package contract.

The public package MUST compile with CGO_ENABLED=0. Its exported API MUST NOT
expose a type from an internal package; the package MAY delegate to private
implementation packages.

### 3.1 Constants [HN-LIM-001]

~~~go
package legends

const ContractVersion uint16 = 1

const (
    MinMemoryBytes uint32 = 64 * 1024
    MaxMemoryBytes uint32 = 16 * 1024 * 1024
    MemoryAlignment uint32 = 4096

    MaxTextColumns uint16 = 160
    MaxTextRows    uint16 = 100
    MaxFrameWidth  uint32 = 4096
    MaxFrameHeight uint32 = 4096
    MaxFramePixels uint64 = 16 * 1024 * 1024

    MaxInputBatchBytes   uint64 = 1 * 1024 * 1024
    MaxPendingInputBytes uint64 = 4 * 1024 * 1024
    MaxProgramBytes      uint64 = 1 * 1024 * 1024
    MaxSnapshotBytes     uint64 = 96 * 1024 * 1024
)
~~~

Numeric limits are part of contract version 1. Implementations MAY use lower
private allocation thresholds only when New rejects the configuration with
ErrResourceLimit; a conforming release MUST support every configuration used by
the admitted milestone-one vectors.

### 3.2 Configuration [HN-CFG-001]

~~~go
type Config struct {
    ContractVersion uint16
    MemoryBytes     uint32
    ClockHz         uint64
    MaxPendingInput uint32
    TextColumns     uint16
    TextRows        uint16
    FrameWidth      uint32
    FrameHeight     uint32
    Seed            [32]byte
    Program         []byte
}
~~~

Validation rules:

1. ContractVersion MUST equal 1.
2. MemoryBytes MUST be within MinMemoryBytes and MaxMemoryBytes inclusive and
   divisible by MemoryAlignment.
3. ClockHz MUST be between 1 and 1,000,000,000 inclusive.
4. MaxPendingInput MUST be between 1 and 65,536 inclusive.
5. TextColumns and TextRows MUST be nonzero and no greater than their published
   maxima.
6. FrameWidth and FrameHeight MUST be nonzero and no greater than their
   published maxima.
7. FrameWidth multiplied by FrameHeight MUST NOT exceed MaxFramePixels. The
   multiplication MUST be overflow-checked before allocation.
8. Seed is always significant, including the all-zero value.
9. Program MUST be a nonempty canonical M1 scripted-core program no larger
   than MaxProgramBytes. New copies Program before returning.
10. New MUST validate the complete configuration before allocating the configured
   machine memory.

Contract version 1 performs no defaulting or scalar normalization: the validated
scalar fields and Program bytes returned by Config are byte-for-byte equal to
the values supplied to New.

The machine deep-copies Config, including Program, during creation. Later caller
mutations to the Config value or Program backing array have no effect. Config()
also returns a fresh Program copy; callers never receive an alias to machine
state.

### 3.3 Errors [HN-ERR-001]

~~~go
type ErrorCode uint16

const (
    ErrInvalidArgument ErrorCode = iota + 1
    ErrUnsupportedVersion
    ErrClosed
    ErrConcurrentCall
    ErrCycleOverflow
    ErrInputInPast
    ErrInputOrder
    ErrQueueFull
    ErrInvalidUTF8
    ErrSnapshotMagic
    ErrSnapshotVersion
    ErrSnapshotBounds
    ErrSnapshotIntegrity
    ErrSnapshotSection
    ErrSnapshotConfig
    ErrResourceLimit
    ErrInternal
)

type Error struct {
    Code ErrorCode
    Op   string
}

func (e *Error) Error() string
func (e *Error) Is(target error) bool
~~~

Requirements:

- Callers MUST be able to obtain the stable ErrorCode with errors.As.
- Error.Is compares ErrorCode values and ignores Op. A target *Error whose Code
  is zero does not match.
- Error strings and Op values are diagnostic and are not conformance data.
- An operation returning an error MUST document whether it mutated state.
- Unless this specification explicitly says otherwise, an errored operation
  MUST leave observable state unchanged.
- Panics MUST NOT cross the public package boundary for invalid external input.
- ErrInternal is reserved for violated implementation invariants and MUST leave
  the machine either unchanged or safely closable.

Public validation maps to codes as follows:

| Condition | ErrorCode |
|---|---|
| nil receiver or malformed ordinary argument | ErrInvalidArgument |
| unsupported contract or snapshot version | ErrUnsupportedVersion or ErrSnapshotVersion, respectively |
| zero step budget | ErrInvalidArgument |
| cycle addition overflow | ErrCycleOverflow |
| input timestamp before CurrentCycle | ErrInputInPast |
| non-increasing or previously accepted input pair | ErrInputOrder |
| pending input count or bytes would exceed its limit | ErrQueueFull |
| malformed UTF-8 text input | ErrInvalidUTF8 |
| invalid program, capture coordinate, code point, color, or reserved value | ErrInvalidArgument |
| snapshot magic, bounds, checksum, section structure, or machine-configuration mismatch | the corresponding ErrSnapshotMagic, ErrSnapshotBounds, ErrSnapshotIntegrity, ErrSnapshotSection, or ErrSnapshotConfig |
| supported input whose allocation exceeds a published non-queue resource limit | ErrResourceLimit |

Except for idempotent Close, receiver state is checked in this order: nil,
closed, conflicting concurrent call, then operation-specific arguments. Within
an input batch, checks occur in event order after batch byte size and capacity
are overflow-checked. Load checks outer bounds before integrity, integrity
before section decoding, and structure before decoded values. Conformance does
not depend on which of two malformed decoded values is reported first.

### 3.4 Lifecycle API [HN-LC-001]

~~~go
type Machine struct {
    // Opaque outside package legends.
}

func New(cfg Config) (*Machine, error)
func (m *Machine) Config() Config
func (m *Machine) Reset() error
func (m *Machine) Close() error
~~~

Lifecycle rules:

1. New returns either a non-nil active Machine and nil error, or nil and a
   typed error.
2. Config on an active machine returns the normalized configuration by value,
   with a freshly allocated Program copy.
3. Reset atomically restores the post-New state using the original Config.
4. Reset does not change the Config or release machine resources.
5. Close releases resources and is idempotent.
6. Config after Close returns the last normalized configuration.
7. Except for Config, HasCapability, and idempotent Close, every method after
   Close returns ErrClosed and does not mutate state.
8. A nil Machine receiver returns ErrInvalidArgument where the signature
   permits an error and MUST NOT panic. Config on a nil receiver returns the
   zero Config value.
9. A Machine value MUST NOT be copied after first use. Public documentation
   states this restriction.

### 3.5 Initial and reset state [HN-INIT-001]

After New and after every successful Reset:

- CurrentCycle and frame generation are zero;
- machine memory contains MemoryBytes zero bytes;
- no scripted record has been applied and the core is active;
- the pending input queue and last-accepted-input marker are empty;
- the processed-input digest has its initial value from section 6.3;
- every text cell has all fields zero and the cursor is hidden at column and
  row zero; and
- every RGBA pixel is `(0, 0, 0, 255)`.

Records at AtCycle zero are not applied by New or Reset. They are applied at
the starting boundary of the next successful Step.

## 4. Concurrency contract [HN-CON-001]

A valid deterministic trace invokes mutating Machine methods sequentially.

All public methods MUST nevertheless be data-race free when callers violate
that rule. When a call overlaps another operation:

- at most one mutating operation may proceed;
- a competing mutating operation MUST return ErrConcurrentCall without state
  mutation;
- read/capture operations MAY either return a coherent pre-operation or
  post-operation snapshot, or return ErrConcurrentCall;
- Config and HasCapability, whose signatures have no error result, MUST return
  a coherent pre-operation or post-operation value and MUST NOT block
  indefinitely;
- no method may block indefinitely waiting for a caller-visible callback;
- Close MUST be safe to race with other calls and may cause them to return
  ErrClosed or ErrConcurrentCall.

Which overlapping caller wins is outside deterministic conformance. The
resulting machine state MUST always correspond to a valid serialization of the
successfully completed calls.

## 5. Cycle stepping

### 5.1 Types and API [HN-ST-API-001]

~~~go
type StepBudget struct {
    Cycles uint64
}

type StepResult struct {
    StartCycle    uint64
    EndCycle      uint64
    ExecutedCycles uint64
    ProcessedInput uint32
    Halted         bool
}

func (m *Machine) Step(budget StepBudget) (StepResult, error)
func (m *Machine) CurrentCycle() (uint64, error)
~~~

### 5.2 Semantics [HN-ST-001]

1. Cycles MUST be greater than zero.
2. StartCycle is the cycle before execution.
3. The requested end is StartCycle plus Cycles. Overflow returns
   ErrCycleOverflow without state mutation.
4. CurrentCycle identifies an execution boundary. At the start of Step, the
   machine processes any not-yet-processed inputs and scripted records at
   StartCycle. For each unit of remaining budget, an active core executes one
   cycle, increments CurrentCycle by one, then processes inputs and scripted
   records at the new boundary. This makes both StartCycle and the requested
   end eligible boundaries without executing an extra cycle.
5. At a boundary, inputs are processed first in Sequence order, followed by
   scripted records in file order. A scripted record is applied at most once.
6. The execution core runs until it consumes the budget, a Halt record makes
   it halted, or it returns an internal fault.
7. EndCycle equals StartCycle plus ExecutedCycles.
8. EndCycle MUST NOT exceed the requested end.
9. A halted core executes zero further cycles. Only Reset or loading a snapshot
   of a non-halted state can make it active again.
10. ProcessedInput counts every input committed during this call, including
    events at StartCycle and EndCycle.
11. Step MUST NOT inspect wall-clock time or sleep.
12. The same initial snapshot, input trace, and step-budget sequence MUST
    produce identical StepResult values and state hashes.

The M1 scripted core defines execution actions in admitted vectors. It exists to
validate orchestration and is not an undocumented instruction set.

### 5.3 M1 scripted-core program [HN-PGM-001]

Program is a canonical binary test program. It is not a PC instruction set and
is removed from production compatibility claims.

All integers are unsigned little-endian. The program begins with:

| Size | Field |
|---:|---|
| 8 | ASCII magic PLGOPRG1 |
| 2 | format version, value 1 |
| 2 | flags, value 0 |
| 4 | record count |

Each record contains an AtCycle uint64, opcode uint8, payload length uint32,
then the payload. Records are in nondecreasing AtCycle order. Records at equal
cycles retain file order. Unknown opcodes, nonzero flags, invalid payload
lengths, invalid values, or trailing bytes return ErrInvalidArgument from New.

Version 1 opcodes are:

| Opcode | Name | Payload |
|---:|---|---|
| 1 | TextCell | column uint16, row uint16, code point uint32, foreground uint32, background uint32, attributes uint16 |
| 2 | Cursor | column uint16, row uint16, visible uint8 |
| 3 | FillRGBA | x uint32, y uint32, width uint32, height uint32, red uint8, green uint8, blue uint8, alpha uint8 |
| 4 | XorMemory | offset uint32, length uint32, value uint8 |
| 5 | Halt | no payload |

Exact payload lengths are 18 bytes for TextCell, 5 for Cursor, 20 for FillRGBA,
9 for XorMemory, and 0 for Halt. TextCell coordinates MUST be in bounds; its
code point is zero or a Unicode scalar value; both colors have a zero high byte;
and M1 Attributes MUST be zero. Cursor visibility is zero or one; a visible
cursor is in bounds and a hidden cursor has zero coordinates. FillRGBA width
and height are nonzero, checked addition keeps the rectangle inside the frame,
and alpha is 255. XorMemory length is nonzero and its checked range lies inside
machine memory.

Each record is applied atomically at its AtCycle boundary. All record ranges
are validated by New against Config, so a Program error is never first
discovered during Step. TextCell, Cursor, and FillRGBA update the named capture
state; XorMemory XORs every byte in its range; Halt leaves data unchanged and
makes the core halted after all records at that boundary have been applied.

## 6. Input

### 6.1 Types and API [HN-IN-API-001]

~~~go
type InputKind uint8

const (
    InputKeyDown InputKind = iota + 1
    InputKeyUp
    InputText
    InputMouseMove
    InputMouseButtonDown
    InputMouseButtonUp
)

type InputEvent struct {
    AtCycle uint64
    Sequence uint64
    Kind     InputKind
    Code     uint32
    X        int32
    Y        int32
    Text     string
}

func (m *Machine) QueueInput(events []InputEvent) error
func (m *Machine) PendingInput() (uint32, error)
~~~

### 6.2 Validation and ordering [HN-IN-001]

QueueInput validates and copies the entire batch before mutation.

Input pairs sort lexicographically by unsigned AtCycle and then unsigned
Sequence.

- AtCycle MUST be at least CurrentCycle.
- The pair AtCycle, Sequence MUST be strictly increasing within the supplied
  batch.
- The first pair MUST sort after the greatest pair accepted since New, Reset,
  or the loaded snapshot, including events already processed. The machine
  persists this last-accepted marker independently of the pending queue.
- Kind MUST be a published InputKind.
- Text MUST be empty for non-text events.
- InputText requires valid, nonempty UTF-8.
- Code MUST be nonzero for key and button events.
- Code MUST be zero for text and mouse-move events.
- MouseMove uses X and Y as signed relative deltas; the other event kinds
  require X and Y to be zero.
- Each canonical event occupies 37 fixed bytes plus len(Text). The complete
  batch MUST NOT exceed MaxInputBatchBytes.
- The resulting queue length MUST NOT exceed Config.MaxPendingInput.
- The resulting queue's canonical event bytes MUST NOT exceed
  MaxPendingInputBytes.

Any validation failure rejects the complete batch without mutation. The queue
MUST preserve byte-exact Text values; Unicode normalization is not performed.
An empty batch is valid and does not change the last-accepted marker.

### 6.3 Processed-input commitment [HN-IN-002]

The scripted M1 core does not pretend to implement a keyboard or mouse device.
Instead, it commits processed inputs into observable state so ordering,
timestamping, save/load, reset, and determinism remain testable.

The initial processed-input digest is:

~~~text
SHA-256(ASCII "PLGO-INPUT-v1" || byte 0x00)
~~~

For every event processed by Step, in processing order, the machine replaces
the digest with:

~~~text
SHA-256(
    ASCII "PLGO-INPUT-v1" || byte 0x00 ||
    previous 32-byte digest ||
    canonical event bytes
)
~~~

Canonical event bytes are, in order, little-endian AtCycle uint64, Sequence
uint64, Kind uint8, Code uint32, X int32 encoded as its two's-complement uint32
bit pattern, Y encoded the same way, Text byte length uint64, and the unmodified
UTF-8 Text bytes. The digest update happens immediately before scripted-core
records at the event's cycle. Reset restores the initial digest. No other M1
machine behavior is synthesized from an input event.

## 7. Capture surfaces

### 7.1 Text [HN-TXT-001]

~~~go
type TextCell struct {
    CodePoint uint32
    Foreground uint32
    Background uint32
    Attributes uint16
}

type Cursor struct {
    Column  uint16
    Row     uint16
    Visible bool
}

type TextFrame struct {
    Generation uint64
    Columns    uint16
    Rows       uint16
    Cells      []TextCell
    Cursor     Cursor
}

func (m *Machine) CaptureText() (TextFrame, error)
~~~

Text rules:

- Cells is row-major and has exactly Columns multiplied by Rows entries.
- CodePoint is zero for an empty cell or a valid Unicode scalar value.
- Foreground and Background use canonical non-premultiplied sRGB encoded as
  0x00RRGGBB.
- Unassigned Attributes bits MUST be zero.
- A hidden cursor has Column and Row equal to zero.
- CaptureText returns an owned copy. Caller mutation cannot affect the machine.

### 7.2 RGBA [HN-RGBA-001]

~~~go
type RGBAFrame struct {
    Generation uint64
    Width      uint32
    Height     uint32
    Pixels     []byte
}

func (m *Machine) CaptureRGBA() (RGBAFrame, error)
func (m *Machine) FrameGeneration() (uint64, error)
~~~

RGBA rules:

- Pixels is row-major RGBA8, non-premultiplied sRGB.
- Its length is exactly Width multiplied by Height multiplied by four.
- Alpha is 255 for the M1 scripted core.
- CaptureRGBA returns an owned copy.
- TextFrame.Generation, RGBAFrame.Generation, and FrameGeneration return the
  same shared generation value for a coherent machine state.
- Generation begins at zero. After all scripted records at one cycle boundary
  are applied, it increments exactly once when the resulting text cells,
  cursor, or RGBA pixels differ from their values immediately before that
  boundary. Boundaries with no final capture change do not increment it. This
  rule is independent of how boundaries are grouped into Step calls.
- Reset restores generation zero. Load restores the generation encoded in the
  snapshot exactly; neither operation applies the Step increment rule.
- Generation does not change when capture methods are called.
- Generation overflow returns ErrResourceLimit before committing the operation
  that would overflow.

## 8. Snapshots

### 8.1 API [HN-SNAP-API-001]

~~~go
func (m *Machine) Save() ([]byte, error)
func (m *Machine) Load(snapshot []byte) error
~~~

Save returns an owned canonical encoding. Load copies or consumes all required
data before returning; later caller mutation of snapshot has no effect.

### 8.2 Binary format [HN-SNAP-001]

All integer fields are unsigned little-endian. No field uses Go struct memory,
platform padding, native int, pointers, floats, maps, gob, or JSON.

The 64-byte header is:

| Offset | Size | Field |
|---:|---:|---|
| 0 | 8 | ASCII magic PLGOSNAP |
| 8 | 2 | format version, value 1 |
| 10 | 2 | flags, value 0 |
| 12 | 4 | header length, value 64 |
| 16 | 8 | total file length |
| 24 | 8 | payload length |
| 32 | 4 | section count |
| 36 | 4 | reserved, zero |
| 40 | 4 | CRC-32/ISO-HDLC of the complete payload |
| 44 | 20 | reserved, zero |

Total file length MUST equal the actual byte length and 64 plus payload length.
The CRC is the IEEE reflected CRC-32 used by Go's crc32.ChecksumIEEE: reflected
polynomial `0xEDB88320`, initial value `0xFFFFFFFF`, and final XOR
`0xFFFFFFFF`.

The payload is a sequence of sections in strictly increasing section-ID order.
Each section begins with:

| Size | Field |
|---:|---|
| 4 | section ID |
| 2 | section version |
| 2 | flags |
| 8 | body length |
| 4 | CRC-32/ISO-HDLC of body |
| 4 | reserved, zero |

M1 section IDs are:

1. normalized configuration;
2. lifecycle, cycle, and processed-input-digest state;
3. scripted execution-core state;
4. pending input queue;
5. text surface and cursor;
6. RGBA surface and generation.

Every M1 section is required, has version 1 and flags zero, and occurs exactly
once. No bytes appear between sections or after the final section.

Variable arrays use a uint64 element count followed by canonical elements.
Strings use a uint64 byte length followed by unmodified UTF-8 bytes. Booleans
use one byte with value zero or one. Reserved bytes and unassigned bits are
zero.

The version 1 section bodies have these exact field orders and no padding:

1. **Configuration:** ContractVersion uint16, MemoryBytes uint32, ClockHz
   uint64, MaxPendingInput uint32, TextColumns uint16, TextRows uint16,
   FrameWidth uint32, FrameHeight uint32, the 32 Seed bytes, Program length
   uint64, then Program bytes.
2. **Scheduler:** CurrentCycle uint64, the 32-byte processed-input digest, a
   one-byte last-accepted-marker-present boolean, and, when present, the last
   accepted AtCycle uint64 and Sequence uint64.
3. **Scripted core:** next-record index uint64, halted boolean, memory length
   uint64, then the complete machine memory bytes. The index is at most the
   program record count; records before it have AtCycle no greater than
   CurrentCycle, and records after it have AtCycle no less than CurrentCycle.
4. **Pending input:** event count uint64 followed by events in strict pair
   order, each using the canonical 37-byte fixed encoding and Text bytes from
   section 6.3. Every event has AtCycle at least CurrentCycle. The count and
   encoded-byte total obey both pending-input limits. When events exist, the
   last-accepted marker is present and does not sort before the final event.
5. **Text:** cell count uint64 followed by row-major cells. Each cell is
   CodePoint uint32, Foreground uint32, Background uint32, and Attributes
   uint16. The count equals TextColumns multiplied by TextRows. Cursor Column
   uint16, Row uint16, and visible boolean follow the final cell.
6. **RGBA:** shared generation uint64, pixel-byte length uint64, then row-major
   RGBA bytes. Length equals FrameWidth multiplied by FrameHeight multiplied by
   four, and every alpha byte is 255.

Save is valid only for an active machine, so closed state has no snapshot
encoding. The configuration body in Load MUST be byte-identical to the target
machine's original validated Config encoding; Load never replaces Config or
the Config used by Reset.

### 8.3 Load validation [HN-SNAP-002]

Load MUST:

1. reject input shorter than the header or longer than MaxSnapshotBytes before
   reading any field;
2. validate magic, version, flags, reserved fields, lengths, and overflow;
3. enforce implementation resource limits before allocation;
4. verify the payload CRC and each section CRC;
5. reject missing, duplicate, out-of-order, unknown, or trailing sections;
6. validate every decoded value and cross-section invariant against the public
   contract, including exact configuration equality;
7. construct a complete staged machine state;
8. commit the staged state atomically only after all checks pass.

Any failure returns a specific snapshot ErrorCode and leaves the previous
machine state and state hash unchanged.

Saving the same state twice MUST produce byte-identical snapshots. Loading a
canonical snapshot and immediately saving MUST reproduce identical bytes.

## 9. Observable-state hash [HN-HASH-001]

~~~go
type StateHash [32]byte

func (m *Machine) StateHash() (StateHash, error)
~~~

The state hash is:

~~~text
SHA-256(
    ASCII "PLGO-STATE-v1" ||
    byte 0x00 ||
    canonical bodies of snapshot sections 1 through 6
)
~~~

Snapshot headers, section framing, CRC fields, diagnostic strings, allocation
capacity, lock state, and host metadata are excluded.

The hash MUST be stable across:

- repeated calls;
- save followed by load;
- supported operating systems;
- amd64 and arm64;
- current and minimum-supported Go toolchains;
- different process IDs, paths, locales, time zones, and GOMAXPROCS values.

## 10. Capabilities [HN-CAP-001]

~~~go
type Capability uint16

const (
    CapabilityCycleStep Capability = iota + 1
    CapabilityTimestampedInput
    CapabilityTextCapture
    CapabilityRGBACapture
    CapabilityCanonicalSnapshot
    CapabilityStateHash
    CapabilityScriptedCore
)

func (m *Machine) HasCapability(cap Capability) bool
~~~

Every M1 capability above returns true on an active or closed M1 Machine.
Unknown values and a nil Machine receiver return false. Capability discovery
does not mutate state.

## 11. Determinism requirements [HN-DET-001]

For normalized configuration C, initial state S, ordered input trace I, and
step schedule B:

~~~text
Run(C, S, I, B) -> ordered results, captures, snapshot, state hash
~~~

Every conforming execution MUST produce the same observable result tuple.

The implementation MUST:

- sort any internal collection before canonical encoding;
- avoid map iteration in state transitions unless keys are explicitly ordered;
- derive all pseudo-random values from Config.Seed through a documented
  versioned generator;
- exclude wall time, monotonic time, goroutine identity, and scheduler order;
- use integer arithmetic with specified overflow behavior;
- test at GOMAXPROCS values 1, 2, and the host default.

The M1 scripted core performs no pseudo-random transition. Seed is nevertheless
part of configuration, snapshots, and StateHash so a future contract cannot
silently introduce an unversioned generator.

## 12. Security and resource behavior [HN-SEC-001]

- Snapshot, input, and configuration decoders treat all inputs as hostile.
- Lengths are validated before conversion to int or allocation.
- Allocation totals use checked uint64 arithmetic.
- A rejected operation does not retain caller-controlled buffers.
- Public methods do not start unbounded goroutines.
- Close terminates all machine-owned goroutines before returning.
- M1 uses no file, network, process, environment-variable, or device access in
  core packages.
- Diagnostic errors do not include secrets, absolute paths, or snapshot bytes.

## 13. Required conformance families [HN-COV-001]

The mandatory evidence set for contract version 1 MUST cover:

1. valid and invalid configuration boundaries;
2. lifecycle, idempotent Close, and use after close;
3. zero, normal, halted, and overflowing step budgets;
4. input ordering, batch atomicity, UTF-8, queue limits, and cycle boundaries;
5. text and RGBA layout, owned-copy behavior, and generation changes;
6. snapshot byte stability, round trip, corruption, truncation, duplicate
   section, reordering, oversized length, and atomic rejection;
7. state-hash stability and sensitivity;
8. deterministic replay across processes, platforms, architectures, Go
   versions, and GOMAXPROCS values;
9. overlapping public calls under the race detector;
10. fuzz regression seeds for every decoder failure found.

Items 1 through 8 require exchange vectors. Item 9 is covered by public-API
contract fixtures under the race detector because winner selection is
intentionally nondeterministic. Item 10 is covered by implementation-side
minimized seeds after provenance review. The vector layout and gate policy are
defined by the linked conformance-vector and quality-gate specifications.

## 14. Contract evolution [HN-EVO-001]

- Published constants, error codes, snapshot version 1, and section meanings
  are immutable.
- Additive Go methods require a minor exchange release and new capability.
- Changed semantics require a new ContractVersion.
- Snapshot changes require a new snapshot format version.
- Readers reject unknown required sections. A later format may define an
  optional-section flag, but version 1 defines none.
- Deprecation does not remove a behavior from an existing contract version.
- A contract release is consumable only by its immutable exchange digest.
