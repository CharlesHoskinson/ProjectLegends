# R1 TSan race-family triage

Prepared for `openspec/changes/ci-stabilize-mandatory-lanes` tasks 1.1–1.2.
Evidence sources: CI design comments (`.github/workflows/ci.yml` pre-R1),
audit-wiki Verification Lanes entity, source reads at HEAD on branch
`ci/r1-stabilize-mandatory-lanes`.

Local full TSan ctest was not run on Windows (TSan requires Linux clang+libc++
instrumentation). Families below are the design-named set; the first enforced
CI `thread` job is the live evidence that refines or removes entries.

## Family A — engine / embed global state

| Field | Value |
|-------|--------|
| Symbols | `g_active_instance` (and related engine/mixer globals called out as REQ-TH-004) |
| Source | `src/legends/legends_embed_api.cpp:68` (`std::atomic<legends_instance*>`) |
| Stack sample (historical CI comment) | TSan reports naming `g_active_instance` during create/destroy or step races |
| Issue | https://github.com/CharlesHoskinson/ProjectLegends/issues/38 |
| Suppression | `race:g_active_instance` in `tsan-suppressions.txt` |
| Exit | Clean enforced TSan run without this report → delete entry + close #38 |

## Family B — CrashBreadcrumb ring buffer

| Field | Value |
|-------|--------|
| Symbols | `CrashBreadcrumb::add`, concurrent `readInto` |
| Source | `src/app/crash_breadcrumb.cpp:33-52` (relaxed `fetch_add` then non-atomic slot writes) |
| Stack sample | Writer: `CrashBreadcrumb::add` → slot field stores; Reader: `readInto` → slot field loads without matching atomics on payload |
| Issue | https://github.com/CharlesHoskinson/ProjectLegends/issues/39 |
| Suppression | `race:CrashBreadcrumb::add`, `race:legends::CrashBreadcrumb::add` |
| Exit | Seqlock/per-slot sequence or documented permanent suppression reviewed each audit |

## Family C — intentional wrong-thread contract tests

| Field | Value |
|-------|--------|
| Tests | `tests/unit/test_thread_safety.cpp` (`*FromWrongThread*`), `tests/unit/test_contract_gates.cpp` (`ContractGate_Threading.WrongThreadReturnsError`) |
| Behavior | Spawn secondary thread, call `legends_*`, expect `LEGENDS_ERR_WRONG_THREAD` |
| Stack sample | Worker thread enters `legends_step_*` / capture while owner thread holds the instance |
| Issue | https://github.com/CharlesHoskinson/ProjectLegends/issues/45 |
| Handling | **Not suppressed** — gated with `GTEST_SKIP` under `LEGENDS_TSAN_BUILD` so non-TSan lanes still run them |
| Exit | Reject path TSan-clean or dedicated `tsan-excluded` CTest label |

## MSan (not a race family)

Retired from the sanitizer matrix. Re-entry: https://github.com/CharlesHoskinson/ProjectLegends/issues/40
