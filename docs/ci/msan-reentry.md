# MSan re-entry checklist (#40) — P4 parked

MSan is **retired** from the mandatory CI matrix (`sanitizer: [address, undefined, thread]` only).
`.github/workflows/ci.yml` comments forbid re-adding `"memory"` without this checklist.
Stock Ubuntu libc++ is not MSan-instrumented; binaries crash at startup and the lane verifies nothing.

## Exit criterion (re-add the matrix leg only when all are true)

1. **Instrumented standard library** available on the CI image:
   - Either MSan-instrumented libc++ shipped by the distro/toolchain, or
   - A documented, version-pinned recipe to build instrumented libc++ in CI
     (cacheable, <10 min cold, <2 min warm).
2. **Hermetic configure** succeeds with:
   `-fsanitize=memory -fno-omit-frame-pointer` and the instrumented stdlib
   (no dual-stdlib link with uninstrumented libstdc++).
3. **Smoke**: `legends` unit test binary starts and runs ≥1 test under MSan
   without intercepting/crashing in the C++ runtime.
4. **Scope decision** recorded: engine-only vs full app; third-party
   interceptors (SDL, etc.) listed as suppressions or out-of-scope.
5. **Issue #40** closed in the same PR that re-adds the matrix entry.

## Non-goals

- Do not re-add `allow_failure` to silence startup crashes.
- Do not claim MSan coverage from ASan/UBSan green.

## Related

- R1 design: OpenSpec `ci-stabilize-mandatory-lanes`
- CI thesis R1 MSan retirement
