## 1. PIC Serialization

- [ ] 1.1 Define `EngineStatePicController` struct with all 18 fields from `PicController` (pic_types.h)
- [ ] 1.2 Serialize both PIC controllers (~70 bytes each)
- [ ] 1.3 Add `irq_delay_ns`, `srv_lag`, `enable_slave_pic`, `enable_pc_xt_nmi_mask` to state
- [ ] 1.4 Add PIC round-trip test with field-by-field assertions

## 2. Mixer Serialization

- [ ] 2.1 Define `EngineStateMixer` struct (freq, blocksize, mastervol[2], recordvol[2], samples, flags)
- [ ] 2.2 Implement serialize/deserialize for mixer (~80 bytes)
- [ ] 2.3 Add mixer round-trip test

## 3. VGA Serialization

- [ ] 3.1 Define `EngineStateVga` struct (width, height, bpp, mode, svga_chip, refresh, render/DAC/VESA flags)
- [ ] 3.2 Implement serialize/deserialize for VGA config (~64 bytes, excluding opaque hw pointer)
- [ ] 3.3 Add VGA round-trip test

## 4. DOS Kernel Serialization

- [ ] 4.1 Define `EngineStateDos` struct (kernel state, psp/dta, version, current_drive, verify, country, codepage)
- [ ] 4.2 Implement serialize/deserialize for DOS kernel (~24 bytes)
- [ ] 4.3 Add DOS kernel round-trip test

## 5. Wire Format

- [ ] 5.1 Create `engine/include/dosbox/wire_format.h` with `write_u32_le`/`read_u32_le`/`write_u16_le`/`read_u16_le`
- [ ] 5.2 Replace all memcpy-based serialization in engine layer with wire format helpers
- [ ] 5.3 Add endianness unit test (encode on native, decode, verify match)

## 6. Format Versioning

- [ ] 6.1 Bump to V4 in header
- [ ] 6.2 Use 3 reserved header slots for mixer/vga/dos section offsets
- [ ] 6.3 Add `section_count` field for forward compatibility
- [ ] 6.4 Update `ENGINE_STATE_SIZE` to ~828 bytes

## 7. Backward Compatibility

- [ ] 7.1 Initialize new sections to defaults when loading V3 state files
- [ ] 7.2 Add V3 backward compatibility test (load V3 file, verify defaults for new sections)

## 8. Verification

- [ ] 8.1 Full round-trip test covering all 9 subsystems with field-by-field assertions
- [ ] 8.2 All existing save/load tests pass
- [ ] 8.3 No sanitizer failures
