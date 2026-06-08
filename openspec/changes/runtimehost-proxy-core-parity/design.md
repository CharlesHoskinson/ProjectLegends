## Design

Use the existing `legends_ipc::msg` message pattern. Add missing structs in `include/legends_ipc/messages.h`, serialization in `src/legends_ipc/messages.cpp`, proxy calls in `src/legends_proxy/proxy_api.cpp`, and dispatcher cases in `src/engine_host/engine_dispatcher.cpp`.

### Variable Payload Rules

- Fixed response headers must include `error_code` and byte/count metadata before any payload bytes.
- Payload length fields must be `uint32_t` on the wire and must be range-checked before allocating or copying.
- Proxy code must preserve public two-call semantics:
  - Query call with null output buffer returns required count/length/size.
  - Fill call with too-small output buffer returns `LEGENDS_ERR_BUFFER_TOO_SMALL` and writes the required count/length/size.
  - Fill call with sufficient buffer copies exactly the returned payload.

### API Notes

- `GetConfigResp` should copy scalar `legends_config_t` fields. Pointer fields such as `config_path` and `working_dir` cannot safely cross process boundaries; proxy responses should set them to `nullptr` unless explicit owned string payload support is added.
- `CaptureTextResp` should carry `legends_text_info_t`, required cell count, and optional serialized `legends_text_cell_t` payload.
- `SaveStateResp` should carry required/written byte count and optional state bytes. The proxy may always request the full state from the engine host, then apply the caller's buffer semantics locally.
- `LoadStateReq` should carry the state byte payload after a fixed header.
- `VerifyDeterminismReq/Resp` should carry `test_cycles` and `is_deterministic`.
- `GetLastErrorResp` should carry required string length including the null terminator and optional UTF-8 bytes.

### Tests

Add serialization round-trips to `tests/unit/test_ipc_messages.cpp`. Add dispatcher tests in `tests/unit/test_engine_dispatcher.cpp` that create an engine, dispatch each new request, and validate response type plus representative output. Add proxy-level tests only if the existing test harness can exercise `ProxyConnection` without a live external host; otherwise document that coverage is dispatcher/message-level.
