## ADDED Requirements

### Requirement: Complete PIC serialization
Both PIC controllers SHALL be fully serialized with all 18 fields from `PicController` (pic_types.h), plus `irq_delay_ns`, `srv_lag`, `enable_slave_pic`, `enable_pc_xt_nmi_mask`. Total ~140 bytes replacing the current 24-byte partial.

#### Scenario: PIC round-trip preserves all fields
- **WHEN** PIC state is saved and loaded
- **THEN** all 18 fields per controller SHALL match the original values

### Requirement: Mixer state serialization
`EngineStateMixer` SHALL serialize freq, blocksize, mastervol[2], recordvol[2], samples fields, and enabled/nosound/swapstereo/mute flags. ~80 bytes.

#### Scenario: Mixer round-trip
- **WHEN** mixer state with non-default values is saved and loaded
- **THEN** all mixer fields SHALL match the original

### Requirement: VGA config serialization
`EngineStateVga` SHALL serialize width, height, bpp, mode, svga_chip, refresh, render flags, DAC/VESA flags. ~64 bytes. Opaque hw pointer (~20KB) SHALL be excluded.

#### Scenario: VGA round-trip
- **WHEN** VGA config is saved and loaded
- **THEN** all serialized VGA fields SHALL match and the opaque pointer SHALL be re-initialized to defaults

### Requirement: DOS kernel serialization
`EngineStateDos` SHALL serialize kernel state, psp/dta, version, current_drive, verify, country, codepage. ~24 bytes.

#### Scenario: DOS kernel round-trip
- **WHEN** DOS kernel state is saved and loaded
- **THEN** all DOS fields SHALL match the original

### Requirement: Endianness handling
All engine-layer serialization SHALL use explicit little-endian encoding via `wire_format.h` helpers (`write_u32_le`/`read_u32_le`). No `memcpy`-based struct serialization.

#### Scenario: Cross-platform state file
- **WHEN** state is saved on a big-endian platform and loaded on little-endian
- **THEN** all fields SHALL decode correctly

### Requirement: V4 format with forward compatibility
State format SHALL be bumped to V4 with 3 reserved header slots for mixer/vga/dos offsets and a `section_count` field.

#### Scenario: V4 header parsed
- **WHEN** a V4 state file is loaded
- **THEN** section offsets SHALL be read from header and sections located by offset

### Requirement: V3 backward compatibility
Loading a V3 state file SHALL succeed. New sections (mixer, VGA, DOS, full PIC) SHALL be initialized to defaults.

#### Scenario: V3 file loads in V4 code
- **WHEN** a V3 state file is loaded by V4 code
- **THEN** existing sections SHALL load correctly and new sections SHALL have default values

### Requirement: All 9 subsystems round-trip tested
Round-trip tests SHALL cover all 9 subsystems with field-by-field assertions.

#### Scenario: Full round-trip
- **WHEN** complete engine state is saved and loaded
- **THEN** every field in all 9 subsystems SHALL match the original
