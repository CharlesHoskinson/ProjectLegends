## ADDED Requirements

### Requirement: Correct SaveStateHeader size in README
README SHALL state that `SaveStateHeader` is 64 bytes (matching `static_assert` in code), not 96 bytes.

#### Scenario: README matches code
- **WHEN** README.md mentions SaveStateHeader size
- **THEN** it SHALL say 64 bytes

### Requirement: All API functions documented
README SHALL document all 22 public API functions. The 7 currently missing functions SHALL be added: `legends_get_api_version`, `legends_get_config`, `legends_key_event_ext`, `legends_is_frame_dirty`, `legends_get_cursor`, `legends_get_last_error`, `legends_set_log_callback`.

#### Scenario: Function count matches
- **WHEN** README.md API section is counted
- **THEN** 22 functions SHALL be documented
