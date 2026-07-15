# R1 ASan / UBSan / fuzz triage log

Tasks 3.1–3.3 of `openspec/changes/ci-stabilize-mandatory-lanes`.

## Method

Reproduce on Linux with the same flags CI uses:

```bash
# ASan (mirrors asan preset / address matrix leg)
cmake --preset asan && cmake --build --preset asan && ctest --preset asan

# UBSan — CI splits legs; approximate with CMAKE_CXX_FLAGS=-fsanitize=undefined
# Fuzz smoke
cmake -B build-fuzz -G Ninja -DCMAKE_C_COMPILER=clang-18 \
  -DCMAKE_CXX_COMPILER=clang++-18 -DCMAKE_BUILD_TYPE=Release \
  -DENABLE_FUZZING=ON -DENABLE_ASAN=ON -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON
cmake --build build-fuzz --target fuzz-all generate_fuzz_corpus
# then the 30s smoke commands from .github/workflows/ci.yml
```

## Status

| Lane | Local / CI evidence | Disposition |
|------|---------------------|-------------|
| address | Pending first enforced dispatch after R1 wiring | Fix root cause or `DISABLED_` + issue (no assertion deletion) |
| undefined | Pending first enforced dispatch | Same |
| fuzz | Pending first enforced dispatch | Attach reproducers to issues; fix crashes in smoke window |

This file is updated when each root cause is identified. Do not mark R1 complete
until CI shows green for address, undefined, thread, and fuzz on a PR or dispatch.
