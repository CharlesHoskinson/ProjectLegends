## Why

Engine-layer V3 serialization covers 5 of 9 subsystems. Mixer, VGA, DOS kernel, and full PIC state are not serialized. Save/load loses half the machine state, making deterministic replay impossible. No endianness handling means cross-platform state files are broken.

## What Changes

- Complete PIC serialization (18 fields per controller, replacing 24-byte partial)
- Add mixer state serialization (~80 bytes)
- Add VGA config serialization (~64 bytes)
- Add DOS kernel serialization (~24 bytes)
- Add endianness handling via `wire_format.h` helpers
- Bump to V4 with section offsets and forward compatibility
- V3 backward compatibility (defaults for new sections)
- Round-trip tests for all 9 subsystems

## Capabilities

### New Capabilities
- `state-serialization`: Complete save/load coverage for all determinism-relevant machine state

### Modified Capabilities

(none)

## Impact

- `engine/include/dosbox/engine_state.h` -- new section structs
- `engine/src/misc/dosbox_library.cpp` -- serialize/deserialize new sections
- `engine/include/dosbox/wire_format.h` -- new file for endianness helpers
- ENGINE_STATE_SIZE grows from ~544 to ~828 bytes
- Header uses 3 reserved slots for new section offsets
