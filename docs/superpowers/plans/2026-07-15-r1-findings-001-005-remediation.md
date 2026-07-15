# R1 Audit Findings 001–005 Remediation — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make ProjectLegends PR #46 R1-mandatory lanes green for the five High findings from the Codex audit: ASan (001), UBSan (002), TSan skip gap (003), fuzz build (004), and Windows IPC (005) — without muting gates, deleting assertions, or widening suppressions.

**Architecture:** Work finding-by-finding in dependency order: close the small verified fixes first (003, 004, 002) with CI proof; then Windows IPC (005) so the MSVC baseline is green; then ASan (001) as the largest investigation, starting from a single-root hypothesis (exception/allocator boundary) before any quarantine. Each finding ends with a named CI job URL as acceptance evidence.

**Tech Stack:** C++23, CMake/Ninja, GoogleTest, libFuzzer+ASan, Clang ASan/UBSan/TSan on Ubuntu, MSVC on windows-latest, GitHub Actions, tracked issues #45/#47/#48.

## Global Constraints

- Branch: `ci/r1-stabilize-mandatory-lanes` (or a worktree off its tip). Base evidence SHA of the audit: `ba8cc8a`; remediation commits may already include partial fixes at HEAD — **re-verify**, do not re-land blindly.
- Acceptance contract: `docs/superpowers/reviews/2026-07-15-codex-r1-ci-stabilize-mandatory-lanes-audit.md` FINDING-001..005 and `openspec/changes/ci-stabilize-mandatory-lanes/design.md` D1/D6.
- **No** `allow_failure`, `continue-on-error`, or `|| true` on R1 gate steps.
- **No** assertion deletion or global disable of ASan allocator-mismatch detection.
- Quarantine only via issue-linked `DISABLED_` / `GTEST_SKIP` with exit criterion (demotion rule in `CONTRIBUTING.md`).
- Commits: conventional subjects; author per repo convention; no force-push to shared branch without owner OK.
- Prefer root-cause fix over skip; temporary TSan skip for intentional races is already allowed under #45 only.

---

## File Structure

| Path | Responsibility |
|------|----------------|
| `tests/unit/test_thread_safety.cpp` | TSan intentional-race skips (FINDING-003) |
| `tests/fuzz/CMakeLists.txt` | `fuzz_config_parser` deps (FINDING-004) |
| `engine/include/dosbox/error_model.h`, `logging.h` | C name APIs take `int` (FINDING-002) |
| `engine/src/misc/error_model.cpp`, `logging.cpp` | Name lookup implementation |
| `engine/tests/unit/test_dosbox_error_model.cpp`, `test_dosbox_logging.cpp` | Unknown-code tests without invalid enum loads |
| `src/legends_ipc/` control channel + `tests/unit/test_ipc_control_channel.cpp` | Windows HandshakeAck race/timeout (FINDING-005) |
| `engine/src/misc/dosbox_context.cpp`, exception/FFI wrappers | ASan leaks + alloc mismatch roots (FINDING-001) |
| `tests/unit/*` FfiSafeCall / GuestMemory suites | ASan reproducers and regression tests |
| `docs/ci/r1-asan-fuzz-triage.md` | Living triage log for 001 |
| `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md` | Checkbox honesty after each green job |

---

## Status at plan authoring (HEAD may already contain partial fixes)

| Finding | Wiring / fix landed? | Still needs |
|---------|----------------------|-------------|
| 003 TSan ConcurrentDestroyAttempts | Yes — `LEGENDS_SKIP_INTENTIONAL_WRONG_THREAD()` present | Green `thread Sanitizer` CI job URL |
| 004 fuzz gsl-lite link | Yes — `gsl::gsl-lite-v1` on `fuzz_config_parser` | Green `Fuzz Testing` job (build + 30s smokes) |
| 002 UBSan int name APIs | Yes — `dosbox_*_name(int)` + test updates | Green `undefined Sanitizer` CI job URL |
| 005 Windows IPC HandshakeAck | No (issue #48 only) | Root cause + green `Windows (MSVC)` |
| 001 ASan cascade | No (issue #47 only) | Cluster analysis + fix/quarantine + green `address Sanitizer` |

---

## Task 1: FINDING-003 — Prove TSan skip for ConcurrentDestroyAttempts

**Files:**
- Modify (if missing): `tests/unit/test_thread_safety.cpp` — `ConcurrentDestroyAttempts` body must start with the skip macro
- Modify: `docs/ci/r1-tsan-triage.md` — Family C inventory
- Test: CI job `thread Sanitizer` on the PR

**Interfaces:**
- Consumes: `LEGENDS_SKIP_INTENTIONAL_WRONG_THREAD()` / `LEGENDS_TSAN_BUILD` from Task setup in `CMakeLists.txt` (~line 817)
- Produces: TSan lane green for intentional-race suite; non-TSan still runs the test

- [ ] **Step 1: Confirm the skip is present (red-test if absent)**

Open `tests/unit/test_thread_safety.cpp` and ensure this exact pattern exists:

```cpp
TEST_F(ThreadSafetyTest, ConcurrentDestroyAttempts) {
    // Intentional multi-thread destroy races; excluded under TSan (issue #45).
    LEGENDS_SKIP_INTENTIONAL_WRONG_THREAD();
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);
    // ... rest unchanged
}
```

If the macro call is missing, add it as the first statement in the test body (after the opening brace). Do **not** add a TSan suppression for `legends_destroy`.

- [ ] **Step 2: Grep inventory — every intentional concurrent-destroy / wrong-thread test**

```bash
rg -n "WrongThread|ConcurrentDestroy|wrong_thread|WRONG_THREAD" tests/unit/test_thread_safety.cpp tests/unit/test_contract_gates.cpp
```

Expected: every test that intentionally calls `legends_*` from a non-owner thread has `LEGENDS_SKIP_INTENTIONAL_WRONG_THREAD()` as first executable statement (or documents why not).

- [ ] **Step 3: Local non-TSan proof (if a headless build exists)**

```bash
# Windows MSVC or Linux Ninja headless unit tests — non-TSan
ctest --test-dir build -R ConcurrentDestroyAttempts --output-on-failure
```

Expected: **PASS** (skip must not apply without `LEGENDS_TSAN_BUILD`).

- [ ] **Step 4: CI acceptance**

Push if needed; wait for `thread Sanitizer` on PR #46.

Expected: job **SUCCESS**, 0 failed tests, `TSAN_OPTIONS` still contains absolute `suppressions=$GITHUB_WORKSPACE/tsan-suppressions.txt`, symbolizer present.

Record job URL in `tasks.md` next to 1.4 / 1.5.

- [ ] **Step 5: Commit only if Step 1 required a code change**

```bash
git add tests/unit/test_thread_safety.cpp docs/ci/r1-tsan-triage.md
git commit -m "test(tsan): skip ConcurrentDestroyAttempts under TSan (#45, FINDING-003)"
```

---

## Task 2: FINDING-004 — Prove fuzz_config_parser builds and smoke runs

**Files:**
- Modify (if missing): `tests/fuzz/CMakeLists.txt` — `fuzz_config_parser` links
- Test: CI job `Fuzz Testing`

**Interfaces:**
- Consumes: `gsl::gsl-lite-v1` from `cmake/dependencies.cmake` FetchContent
- Produces: all five fuzz targets build; 30s smoke commands exit 0

- [ ] **Step 1: Confirm CMake link**

`tests/fuzz/CMakeLists.txt` for `fuzz_config_parser` must include:

```cmake
target_link_libraries(fuzz_config_parser PRIVATE
    legends_core
    gsl::gsl-lite-v1
)
```

If missing, add it. Do not change `legends_core` PUBLIC deps just for fuzz.

- [ ] **Step 2: Local configure/build (Linux with clang+libc++ preferred)**

```bash
cmake -B build-fuzz -G Ninja \
  -DCMAKE_C_COMPILER=clang-18 \
  -DCMAKE_CXX_COMPILER=clang++-18 \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_CXX_FLAGS="-stdlib=libc++" \
  -DCMAKE_EXE_LINKER_FLAGS="-stdlib=libc++" \
  -DENABLE_FUZZING=ON -DENABLE_ASAN=ON \
  -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON
cmake --build build-fuzz --target fuzz-all generate_fuzz_corpus
```

Expected: **no** `gsl-lite/gsl-lite.hpp: file not found`; all targets link.

- [ ] **Step 3: Local smoke (subset)**

```bash
./build-fuzz/tests/fuzz/generate_fuzz_corpus build-fuzz/tests/fuzz/corpus
./build-fuzz/tests/fuzz/fuzz_config_parser build-fuzz/tests/fuzz/corpus/config \
  -max_len=8192 -max_total_time=10
```

Expected: exit 0 (or only corpus-related benign stats).

- [ ] **Step 4: CI acceptance**

`Fuzz Testing` job SUCCESS for PR head: configure → `fuzz-all` → generate corpus → all five 30s smokes.

- [ ] **Step 5: Commit if CMake changed**

```bash
git add tests/fuzz/CMakeLists.txt
git commit -m "build(fuzz): link gsl-lite into fuzz_config_parser (FINDING-004)"
```

If smoke crashes on a target, **stop** this task, open an issue with reproducer path under `tests/fuzz/`, and only then quarantine with issue link — do not mark 004 done on build-only.

---

## Task 3: FINDING-002 — Prove UBSan green for name APIs

**Files:**
- Modify (if missing): `engine/include/dosbox/error_model.h`, `logging.h`
- Modify: `engine/src/misc/error_model.cpp`, `logging.cpp`
- Modify: `engine/tests/unit/test_dosbox_error_model.cpp`, `test_dosbox_logging.cpp`
- Test: CI `undefined Sanitizer`

**Interfaces:**
- Produces: `const char* dosbox_error_code_name(int code);` and `const char* dosbox_log_level_name(int level);`
- C++ wrappers pass `static_cast<int>(enum)` only for **valid** enum values; unknown-value tests call C API with raw `int`

- [ ] **Step 1: Confirm API and tests (implement if HEAD still has enum-typed C API)**

Header signatures must be:

```c
const char* dosbox_error_code_name(int code);
const char* dosbox_log_level_name(int level);
```

Implementation switches on `int` with a `default:` returning `"ERR_UNKNOWN"` / `"UNKNOWN"`.

Tests must **not** do `static_cast<dosbox_error_code>(99999)` into a function that takes the enum type. Preferred:

```cpp
EXPECT_STREQ(dosbox_error_code_name(99999), "ERR_UNKNOWN");
EXPECT_STREQ(dosbox_log_level_name(99), "UNKNOWN");
```

- [ ] **Step 2: Search for other invalid enum loads of the same pattern**

```bash
rg -n "static_cast<\s*dosbox_(error_code|log_level)\s*>\s*\(\s*[0-9]" engine/ tests/
```

Expected: no remaining casts of out-of-range literals into those enums for name-API tests. Fix any hits the same way.

- [ ] **Step 3: CI acceptance**

`undefined Sanitizer` SUCCESS, 0 failed tests (or only pre-existing unrelated fails documented — goal is 0).

- [ ] **Step 4: Commit if code changed**

```bash
git add engine/include/dosbox/error_model.h engine/include/dosbox/logging.h \
  engine/src/misc/error_model.cpp engine/src/misc/logging.cpp \
  engine/tests/unit/test_dosbox_error_model.cpp engine/tests/unit/test_dosbox_logging.cpp
git commit -m "fix(engine): name APIs take int to avoid UBSan invalid-enum (FINDING-002)"
```

---

## Task 4: FINDING-005 — Windows IPC BidirectionalSendRecv / HandshakeAck

**Files:**
- Modify: `src/legends_ipc/` control channel implementation (locate via `rg create_server|connect_client|recv\(` under `src/legends_ipc` and `include/legends_ipc`)
- Modify: `tests/unit/test_ipc_control_channel.cpp:36-71`
- Issue: https://github.com/CharlesHoskinson/ProjectLegends/issues/48
- Test: CI `Windows (MSVC)` and optional local MSVC ctest

**Interfaces:**
- Consumes: `ControlChannel::create_server`, `connect_client`, `send`, `recv` (timeouts in ms)
- Produces: deterministic Handshake → HandshakeAck round-trip on Windows named pipes

### Hypothesis order (try in order; stop at first confirmed)

1. **Race:** client `connect` + `send` before server `recv` is ready; 50ms sleep is flaky under CI load.
2. **Half-duplex / pipe mode:** server sends Ack before client enters `recv`; message dropped.
3. **Payload size / framing:** 12-byte vs 16-byte payload mismatch silently fails decode.
4. **Lifetime:** process exit of server thread before client finishes recv.

- [ ] **Step 1: Write a stricter failing regression (still red on current bug)**

In `tests/unit/test_ipc_control_channel.cpp`, add a sibling test that removes the fixed sleep and uses readiness synchronization:

```cpp
TEST(IpcControlChannelTest, BidirectionalSendRecv_Barrier) {
    auto name = cc_name("cc_bidir_barrier");
    std::atomic<bool> server_ready{false};

    std::thread server_thread([&]() {
        auto server = ControlChannel::create_server(name, 10000);
        ASSERT_TRUE(server.has_value());
        server_ready.store(true, std::memory_order_release);

        auto msg = server->recv(5000);
        ASSERT_TRUE(msg.has_value()) << "server did not receive Handshake";
        EXPECT_EQ(msg->header.msg_type, MsgType::Handshake);

        std::array<uint8_t, 12> payload{};
        auto r = server->send(MsgType::HandshakeAck, 1, payload);
        ASSERT_TRUE(r.has_value()) << "server failed to send HandshakeAck";
    });

    // Wait until server is accepting (not a fixed sleep).
    for (int i = 0; i < 200 && !server_ready.load(std::memory_order_acquire); ++i) {
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }
    ASSERT_TRUE(server_ready.load()) << "server never became ready";

    auto client = ControlChannel::connect_client(name, 10000);
    ASSERT_TRUE(client.has_value());

    std::array<uint8_t, 16> payload{};
    ASSERT_TRUE(client->send(MsgType::Handshake, 1, payload).has_value());

    auto msg = client->recv(5000);
    ASSERT_TRUE(msg.has_value()) << "client did not receive HandshakeAck";
    EXPECT_EQ(msg->header.msg_type, MsgType::HandshakeAck);

    server_thread.join();
}
```

- [ ] **Step 2: Run on Windows**

```powershell
cmake -B build -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON
cmake --build build --config Release
ctest --test-dir build -C Release -R IpcControlChannelTest --output-on-failure --repeat until-fail:20
```

Expected initially: original and/or barrier test may FAIL; capture whether failure rate is 100% or flaky.

- [ ] **Step 3: Root-cause in ControlChannel**

Read implementation of `create_server` / `connect_client` / `send` / `recv` (Windows named-pipe path). Fix the **smallest** correct change, e.g.:

- Server thread signals ready only after `ConnectNamedPipe` (or equivalent) is armed.
- Client `recv` uses the same framing as server `send` for HandshakeAck.
- Do not shrink timeouts globally to hide races; increase only if documented as CI load margin with a comment + issue #48.

- [ ] **Step 4: Green local stress**

```powershell
ctest --test-dir build -C Release -R IpcControlChannelTest --output-on-failure --repeat until-fail:50
```

Expected: all PASS 50/50.

- [ ] **Step 5: Update original test if needed**

Replace the 50ms sleep in `BidirectionalSendRecv` with the same readiness pattern as the barrier test (keep one test, or keep both if barrier is the stress form). Prefer one clear test over duplicates.

- [ ] **Step 6: CI acceptance**

`Windows (MSVC)` SUCCESS; comment job URL on #48; close #48 only when green.

- [ ] **Step 7: Commit**

```bash
git add tests/unit/test_ipc_control_channel.cpp src/legends_ipc/
git commit -m "fix(ipc): reliable HandshakeAck on Windows named pipes (#48, FINDING-005)"
```

**Quarantine path (last resort only):** If after 1 day of investigation the failure is intermittent and root cause is environmental, `DISABLED_` the single test with comment `// issue #48` and a dated exit criterion — never delete the assertion. Prefer fix.

---

## Task 5: FINDING-001 — ASan cascade (cluster, fix, prove)

**Files:**
- Modify: `engine/src/misc/dosbox_context.cpp` (move ctor/assign ~1114+, ownership of `memory.base`)
- Modify: exception/FFI boundary as identified (search `FfiSafeCall`, `safe_call`, catch blocks under `engine/` and `src/legends/`)
- Modify: `docs/ci/r1-asan-fuzz-triage.md` — replace placeholders with concrete roots
- Issue: https://github.com/CharlesHoskinson/ProjectLegends/issues/47
- Test: CI `address Sanitizer`; local `ctest --preset asan` if available

**Interfaces:**
- Produces: ASan job exit 0 (or only issue-linked quarantines with counts documented)

### Phase A — Cluster (no code fixes yet)

- [ ] **Step 1: Download failing ASan log**

```bash
gh run view 29423831242 --log-failed > /tmp/asan-fail.log
# or latest address Sanitizer job on current PR head
rg -n "ERROR: AddressSanitizer|SUMMARY: AddressSanitizer|FAILED" /tmp/asan-fail.log | head -80
```

Build a table in `docs/ci/r1-asan-fuzz-triage.md`:

| Cluster | Example test | ASan kind | Suspected file |
|---------|--------------|-----------|----------------|
| C1 | `FfiSafeCallTest.Catches*` | alloc-dealloc-mismatch | exception / new vs free |
| C2 | `GuestMemoryTest.*OutOfBounds*` | mismatch or use-after | guest memory throw path |
| C3 | `DOSBoxContextTest.MoveConstruction` | direct leak ~16MB | `dosbox_context` move |

- [ ] **Step 2: Hypothesis gate**

If ≥150 failures share `alloc-dealloc-mismatch` on the same stack frame (exception object, `std::string`, or a C `malloc` free), treat as **one root**. Do not open 191 issues.

### Phase B — Fix cluster C3 (context move leaks) first

- [ ] **Step 3: Write/extend a leak-focused unit test**

```cpp
TEST(DOSBoxContextLeak, MoveConstructionDoesNotLeakGuestRam) {
    // Arrange: context with allocated guest RAM (use existing factory if any)
    // Act: move-construct and destroy both sides
    // Assert: under ASan, process exits clean; under normal build, no double-free
}
```

Place next to existing context tests (search `MoveConstruction` in `engine/tests` or `tests/unit`).

- [ ] **Step 4: Fix move ctor/assign**

In `dosbox_context.cpp` move operations: ensure `other.memory.base = nullptr` after transfer; no double-`delete[]`; match `new[]` with `delete[]`.

- [ ] **Step 5: Run ASan on the two move tests only**

```bash
ctest --test-dir build-asan -R "DOSBoxContextTest.Move" --output-on-failure
```

Expected: PASS under ASan.

### Phase C — Fix cluster C1/C2 (exception / FFI)

- [ ] **Step 6: Reproduce one FfiSafeCall test under ASan**

```bash
ctest --test-dir build-asan -R "FfiSafeCallTest.CatchesStdException" --output-on-failure
```

Read the ASan stack: note whether free is from `free` vs `operator delete` on a `new` object.

- [ ] **Step 7: Minimal fix**

Common patterns (apply only if stacks confirm):

1. Exception thrown across C boundary without matching runtime — catch and convert to error code **before** leaving `extern "C"`.
2. Object allocated with `new` freed with `free` (or reverse) in error path.
3. Mixing libc++/libstdc++ in one binary (should already be consistent under CI ASan clang+libc++).

- [ ] **Step 8: Expand to full ASan suite**

```bash
ctest --test-dir build-asan --output-on-failure
```

Expected: 0 fails. If a small residue remains (<10 tests) with independent roots, file sub-issues under #47 and either fix or `DISABLED_` with issue link.

### Phase D — CI + bookkeeping

- [ ] **Step 9: CI acceptance**

`address Sanitizer` SUCCESS on PR head. Paste URL into #47 and `tasks.md` 3.1/3.2.

- [ ] **Step 10: Update triage doc**

Replace “pending first dispatch” language in `docs/ci/r1-asan-fuzz-triage.md` with the cluster table and resolution SHAs.

- [ ] **Step 11: Commits (suggested split)**

```bash
git commit -m "fix(engine): DOSBoxContext move ownership under ASan (#47, FINDING-001 C3)"
git commit -m "fix(engine): FFI/exception allocator boundary under ASan (#47, FINDING-001 C1)"
git commit -m "docs(ci): ASan triage table for R1 FINDING-001"
```

---

## Task 6: Integration gate for findings 001–005

**Files:**
- Modify: `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md`
- Modify: `docs/superpowers/reviews/.r1-audit-complete` only if re-stamping (optional; prefer leave Codex artifact immutable)

- [ ] **Step 1: Collect five job URLs on the same PR head SHA**

| Finding | Job name | Required conclusion |
|---------|----------|---------------------|
| 003 | `thread Sanitizer` | SUCCESS |
| 004 | `Fuzz Testing` | SUCCESS |
| 002 | `undefined Sanitizer` | SUCCESS |
| 005 | `Windows (MSVC)` | SUCCESS |
| 001 | `address Sanitizer` | SUCCESS |

```bash
gh pr checks 46
git rev-parse HEAD
```

- [ ] **Step 2: Update tasks.md**

Check 1.4/1.5 (TSan), 3.x (ASan/UBSan/fuzz), and note Windows baseline outside OpenSpec tasks if needed. Uncheck anything still red.

- [ ] **Step 3: PR comment**

```bash
gh pr comment 46 --body "$(cat <<'EOF'
## Remediation status — FINDING-001..005

| Finding | Status | Evidence |
|---------|--------|----------|
| 001 ASan | ... | job URL |
| 002 UBSan | ... | job URL |
| 003 TSan skip | ... | job URL |
| 004 Fuzz | ... | job URL |
| 005 Windows IPC | ... | job URL |

R1 full exit still also needs dependency-scan dispatch green (FINDING-006+) and task 5.2.
EOF
)"
```

- [ ] **Step 4: Final commit**

```bash
git add openspec/changes/ci-stabilize-mandatory-lanes/tasks.md docs/ci/r1-asan-fuzz-triage.md
git commit -m "docs(r1): record CI evidence for FINDING-001..005 remediation"
```

---

## Self-review (writing-plans checklist)

| Spec item | Task |
|-----------|------|
| FINDING-001 ASan | Task 5 |
| FINDING-002 UBSan | Task 3 |
| FINDING-003 TSan skip | Task 1 |
| FINDING-004 Fuzz gsl-lite | Task 2 |
| FINDING-005 Windows IPC | Task 4 |
| End-to-end proof | Task 6 |
| No mute / no assertion delete | Global Constraints |
| Issue links #45/#47/#48 | Tasks 1, 4, 5 |

Placeholder scan: none intentional. Partial “if already fixed” steps are verification gates, not TBDs.

---

## Execution order (DAG)

```text
Task 1 (003) ──┐
Task 2 (004) ──┼──► Task 6 (integration evidence)
Task 3 (002) ──┤
Task 4 (005) ──┤
Task 5 (001) ──┘   ← longest; can start after Task 1–3 land if parallelized
```

Tasks 1–3 are mostly verify-or-tiny-fix and may finish same day. Task 4 is medium. Task 5 is multi-day XL.

---

## Out of scope (do not expand this plan)

- FINDING-006+ dependency-scan / SBOM completeness (separate plan; partial pin already on branch)
- R2 branch protection ruleset
- Expanding TSan suppressions for new races
- macOS / SDL3 optional jobs
