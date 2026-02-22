## Why

Existing determinism tests run <200K cycles in text mode within a single process. The roadmap goal is deterministic replay for 1M+ cycles in text and graphics modes. Without proof at scale, the replay product (Sprint 4) has no foundation.

## What Changes

- Create minimal COM test binaries (counter, graphics, input)
- Prove 1K-cycle correctness (memory value verification)
- Prove 1M-cycle determinism (two instances, identical hashes)
- Prove save/load midpoint equivalence (500K + 500K = 1M straight)
- Prove graphics mode (Mode 13h) determinism with framebuffer verification
- Prove input replay determinism (inject keys at specific cycles)
- Add nightly soak test (1M cycles x10 with different COM programs)

## Capabilities

### New Capabilities
- `determinism-proof`: Prove deterministic replay for 1M+ cycles in text and graphics modes

### Modified Capabilities

(none)

## Impact

- `tests/fixtures/` -- minimal COM binaries (counter.com, graphics.com, input.com)
- `tests/` -- 6+ new determinism test cases
- CI -- nightly soak test job
- Prerequisite for Sprint 4 (Deterministic Replay as Product)
