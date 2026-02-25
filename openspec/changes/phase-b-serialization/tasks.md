## 1. PIC Serialization

- [x] 1.1 Define `EngineStatePicController` struct with all 18 fields from `PicController` (pic_types.h)
- [x] 1.2 Serialize both PIC controllers (~70 bytes each)
- [x] 1.3 Add `irq_delay_ns`, `srv_lag`, `enable_slave_pic`, `enable_pc_xt_nmi_mask` to state
- [x] 1.4 Add PIC round-trip test with field-by-field assertions

## 2. Mixer Serialization

- [x] 2.1 Define `EngineStateMixer` struct (freq, blocksize, mastervol[2], recordvol[2], samples, flags)
- [x] 2.2 Implement serialize/deserialize for mixer (~36 bytes)
- [x] 2.3 Add mixer round-trip test

## 3. VGA Serialization

- [x] 3.1 Define `EngineStateVga` struct (width, height, bpp, mode, svga_chip, refresh, render/DAC/VESA flags)
- [x] 3.2 Implement serialize/deserialize for VGA config (~32 bytes, excluding opaque hw pointer)
- [ ] 3.3 Add VGA round-trip test

## 4. DOS Kernel Serialization

- [x] 4.1 Define `EngineStateDos` struct (kernel state, psp/dta, version, current_drive, verify, country, codepage)
- [x] 4.2 Implement serialize/deserialize for DOS kernel (~20 bytes)
- [ ] 4.3 Add DOS kernel round-trip test

## 5. Wire Format

- [x] 5.1 Create `engine/include/dosbox/wire_format.h` with `write_u32_le`/`read_u32_le`/`write_u16_le`/`read_u16_le`
- [x] 5.2 Replace all memcpy-based serialization in engine layer with wire format helpers
- [x] 5.3 Add endianness unit test (encode on native, decode, verify match)

## 6. Format Versioning

- [x] 6.1 Bump to V4 in header
- [x] 6.2 Use reserved header slots for mixer/vga/dos section offsets
- [x] 6.3 Add `section_count` field for forward compatibility
- [x] 6.4 Update `ENGINE_STATE_SIZE` to 680 bytes

## 7. Backward Compatibility

- [x] 7.1 Initialize new sections to defaults when loading V3 state files
- [ ] 7.2 Add V3 backward compatibility test (load V3 file, verify defaults for new sections)

## 8. Remaining Work

- [ ] 8.1 Serialize CPU GPRs (EAX-EDI, segment registers) — not yet in V4
- [ ] 8.2 Evaluate RAM content serialization approach
- [ ] 8.3 Full round-trip test covering all 9 subsystems with field-by-field assertions
- [ ] 8.4 All existing save/load tests pass with V4
- [ ] 8.5 No sanitizer failures
