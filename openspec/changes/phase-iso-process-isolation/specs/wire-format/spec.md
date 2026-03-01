# Wire Format Specification

Requirement: REQ-ISO-003, REQ-ISO-004

## REQ-ISO-003: MIT Wire Serialization

### Scenario: Little-endian byte-shift serialization is MIT-licensed

Given the `legends_ipc::wire` namespace in `include/legends_ipc/wire_format.h`
And the file carries SPDX-License-Identifier: MIT
When any unsigned or signed integer is written using `write_*_le()` helpers
Then the bytes are stored in little-endian order using byte shifts
And the code has no dependency on GPL-licensed source

### Scenario: Wire format round-trip correctness

Given a buffer of sufficient size
When a value is written with `write_u{8,16,32,64}_le()` and read with `read_u{8,16,32,64}_le()`
Then the original value is recovered exactly
And this holds for zero, max, and arbitrary values

### Scenario: Signed integer round-trip

Given a negative integer value
When written with `write_i{16,32,64}_le()` and read with `read_i{16,32,64}_le()`
Then the original signed value is recovered exactly

## REQ-ISO-004: Message Framing Protocol

### Scenario: 10-byte message header

Given a `MessageHeader` struct
When serialized to a buffer
Then exactly 10 bytes are written: msg_type(2 LE) + payload_size(4 LE) + sequence_id(4 LE)

### Scenario: Message codec framing

Given a `MessageCodec` instance
When `encode()` is called with a message type, sequence ID, and payload
Then the result is a contiguous buffer of header + payload bytes
And `feed()` + `try_decode()` recovers the original message

### Scenario: Multi-message stream decoding

Given a stream containing multiple encoded messages
When fed to a `MessageCodec`
Then `try_decode()` returns messages in FIFO order
And each message has the correct type, sequence ID, and payload

### Scenario: Partial read handling

Given an incomplete message in the codec buffer
When `try_decode()` is called
Then it returns `IpcError::BufferTooSmall`
And no data is consumed
And feeding the remaining bytes allows successful decode
