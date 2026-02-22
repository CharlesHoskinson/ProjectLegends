## 1. COM Test Binaries

- [ ] 1.1 Assemble `counter.com` (increment memory N times, HLT) and check into `tests/fixtures/`
- [ ] 1.2 Assemble `graphics.com` (Mode 13h, draw pattern, HLT) and check into `tests/fixtures/`
- [ ] 1.3 Assemble `input.com` (wait for keystroke, echo, HLT) and check into `tests/fixtures/`
- [ ] 1.4 Add disassembly comments alongside each binary

## 2. Short-Cycle Correctness

- [ ] 2.1 Test: load `counter.com`, run 1K cycles, verify memory value at 0x8000

## 3. 1M-Cycle Determinism

- [ ] 3.1 Test: two instances, same `counter.com`, 1M cycles, state hashes match

## 4. Save/Load Midpoint

- [ ] 4.1 Test: instance A runs 1M straight; instance B saves at 500K, loads, runs 500K more; hashes match

## 5. Graphics Mode

- [ ] 5.1 Test: two instances run `graphics.com` in Mode 13h, framebuffer contents match

## 6. Input Replay

- [ ] 6.1 Test: inject keys at cycles 100K, 200K, 300K on two instances; final hashes match

## 7. Nightly Soak

- [ ] 7.1 Create nightly CI workflow (schedule-triggered)
- [ ] 7.2 Run 1M-cycle determinism test x10 with different COM programs
- [ ] 7.3 Configure failure notification

## 8. Verification

- [ ] 8.1 All determinism tests pass
- [ ] 8.2 Save/load midpoint produces identical hash
- [ ] 8.3 Graphics mode round-trips
- [ ] 8.4 Input replay is deterministic
