## Design

Use one request/response pair per public API where semantics differ. Do not alias extended keyboard input to the normal key request: `legends_key_event_ext` must use `KeyEventExtReq` so E0 semantics can reach the direct implementation.

### String Command Messages

For `text_input`, MIDI paths, printer path, IPX server, and capability names:

- Encode string length as `uint32_t`.
- Reject truncated payloads during deserialization.
- Treat null C strings in proxy entry points the same way direct C ABI does.
- Do not pass `std::string_view::data()` directly to C ABI without a null-terminated owning `std::string`.

### Query Messages

For `printer_is_active`, `ipx_is_connected`, `is_pc98_mode`, and `has_capability`, responses should include `error_code` and the integer output value.

### MIDI Audio Capture

`legends_capture_midi_audio` follows the same local two-call pattern as audio capture:

- Null buffer queries available sample count.
- Sufficient buffer copies returned samples.
- Too-small buffer returns `LEGENDS_ERR_BUFFER_TOO_SMALL` if the engine reports more samples than fit.

### Truthful Exclusions

Do not promote callback, video capture, or TTF APIs unless this sprint implements their direct and proxy behavior end to end. Update notes to explain why they remain missing or partial.
