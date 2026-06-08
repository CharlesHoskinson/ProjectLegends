## ADDED Requirements

### Requirement: Device Command Proxy Parity
Proxy mode SHALL support command-style APIs that already have direct C ABI implementations for input, MIDI, printer, IPX, Glide, PC-98, and capability queries.

#### Scenario: Command reaches engine host
- **GIVEN** an IPC proxy client and engine host are connected
- **WHEN** a supported command-style API is invoked
- **THEN** the proxy SHALL serialize the request
- **AND** the dispatcher SHALL call the matching direct `legends_*` implementation
- **AND** the returned public error code SHALL match the dispatcher result

### Requirement: Extended Keyboard Semantics
`legends_key_event_ext` SHALL have a distinct IPC path from `legends_key_event`.

#### Scenario: Extended key event
- **GIVEN** a caller injects an E0-prefixed key via `legends_key_event_ext`
- **WHEN** proxy mode forwards the request
- **THEN** the IPC message type SHALL be `KeyEventExtReq`
- **AND** the dispatcher SHALL call `legends_key_event_ext`

### Requirement: Truthful Unsupported APIs
APIs not implemented end to end SHALL remain marked as unsupported, proxy-missing, or proxy-partial.

#### Scenario: Deferred callback and video APIs
- **GIVEN** callbacks require asynchronous delivery or video capture remains app-owned/stubbed
- **WHEN** this sprint updates capability documentation
- **THEN** those APIs SHALL NOT be marked `proxy-supported` unless their proxy, dispatcher, tests, and direct behavior are implemented
