## Design

Create `docs/architecture/abi_parity_contracts.json` with one entry per public `legends_*` API that needs explicit ABI edge-case coverage. Each entry should describe which cases are required and where the evidence lives.

Suggested shape:

```json
{
  "legends_capture_text": {
    "cases": ["null_handle", "null_required_out", "query_fill", "undersized_buffer"],
    "evidence": ["tests/unit/test_proxy_api.cpp", "tests/unit/test_legends_embed.cpp"]
  }
}
```

Create `scripts/check_abi_parity_contracts.py` as a dependency-free validator. It should:

- Parse `include/legends/legends_embed.h` for exported `LEGENDS_API` names.
- Load the ABI contract manifest.
- Verify every listed API is exported.
- Verify every listed evidence file exists.
- Verify each required case has at least one evidence token or named test reference.
- Fail on unknown case names.

The checker does not need to infer semantic correctness from C++; it should prevent silent coverage drift and make omissions explicit.

## Required Case Names

- `null_handle`
- `null_required_out`
- `query_fill`
- `undersized_buffer`
- `default_initialized_output`
- `direct_proxy_return_parity`
- `not_applicable`

`not_applicable` must include a reason.

## CI

Wire the checker into `.github/workflows/sprint2-checks.yml` only if it runs quickly and has no external dependencies.
