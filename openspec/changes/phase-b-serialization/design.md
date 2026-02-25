## Status: ~60% COMPLETE

V4 format implemented (680 bytes, 8 subsystems). Wire format, PIC/Mixer/VGA/DOS structs, section_count, V3 backward compat all done. Remaining: CPU GPR serialization, RAM contents, round-trip tests for VGA/DOS/V3 compat, full integration test. See AUDIT.md finding H1 for gaps.

## Context

Engine-layer V4 now covers 8 subsystems (timing, full PIC, keyboard, CPU cycles, memory, mixer, VGA config, DOS kernel). Legends-layer adds DMA, events, input, and frame state. Wire format helpers provide portable LE encoding. CPU GPRs (EAX-EDI, segment registers) and RAM contents are not yet serialized.

## Goals / Non-Goals

**Goals:**
- Serialize all 9 determinism-relevant subsystems
- Add endianness handling for cross-platform state files
- Maintain V3 backward compatibility
- Achieve ~828 bytes engine state (up from ~544)
- Field-by-field round-trip tests for every subsystem

**Non-Goals:**
- Serializing opaque hardware pointers (VGA hw ~20KB)
- Compression or encryption of state data
- Legends-layer serialization changes (already handles DMA, events, input, frame)

## Decisions

**New section structs:** Add `EngineStatePicController` (18 fields, ~70 bytes each, two controllers), `EngineStateMixer` (~80 bytes), `EngineStateVga` (~64 bytes), `EngineStateDos` (~24 bytes) to `engine_state.h`.

**Wire format helpers:** Create `engine/include/dosbox/wire_format.h` with `write_u32_le`/`read_u32_le`/`write_u16_le`/`read_u16_le`. Port the pattern from legends-layer. Replace all `memcpy`-based struct serialization in the engine layer.

**Header slot allocation:** Use 3 of the reserved header slots for mixer/vga/dos section offsets. Add `section_count` to the header for forward compatibility (future readers can skip unknown sections by offset).

**V3 backward compatibility:** When `version == 3`, read existing 5 sections normally. Initialize mixer/VGA/DOS/full-PIC to defaults. No migration step needed -- defaults represent "no audio, text mode, default DOS" which is the V3 implicit state.

**Exclude VGA opaque pointer:** The `VGA_Type_t* hw` pointer is ~20KB of hardware register state that changes rapidly. Serializing it would massively increase state size and is not needed for config-level determinism. Mark as future work if pixel-perfect restore is needed.

## Risks / Trade-offs

- [~828 bytes is larger but still small] → Acceptable; state snapshots are infrequent
- [Wire format helpers add code] → One-time cost; eliminates an entire class of cross-platform bugs
- [VGA hw pointer excluded] → Graphics mode restore may show visual glitch on first frame after load; acceptable for now

## Key Files

| File | Role |
|------|------|
| `engine/include/dosbox/engine_state.h` | New section struct definitions |
| `engine/src/misc/dosbox_library.cpp` | Serialize/deserialize new sections |
| `engine/include/dosbox/wire_format.h` | New endianness helpers |
| `engine/include/dosbox/dosbox_context.h` | Field inventory reference |
| `engine/include/dosbox/pic_types.h` | PicController field list |
