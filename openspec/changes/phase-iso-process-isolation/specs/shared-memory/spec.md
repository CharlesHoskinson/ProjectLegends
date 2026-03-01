# Shared Memory Specification

Requirements: REQ-ISO-007, REQ-ISO-008

## REQ-ISO-007: Framebuffer Shared Memory

### Scenario: Double-buffered framebuffer

Given a `FramebufferShm` instance created with max dimensions
When the writer calls `begin_write()`, fills pixels, and calls `end_write(w, h)`
Then the active buffer flips atomically
And `read_if_new()` returns the new frame data with correct dimensions

### Scenario: Double-buffer isolation

Given a frame has been written and flipped
When the writer begins writing to the next buffer
Then the reader still sees the previous (active) buffer unchanged

### Scenario: Stale frame detection

Given the reader has already consumed the latest frame
When `read_if_new(last_index)` is called with the current frame index
Then it returns `std::nullopt` (no new data)

## REQ-ISO-008: Audio Ring Buffer

### Scenario: Lock-free SPSC push/pop

Given an `AudioRingBuffer` created with a given capacity
When the producer pushes interleaved S16LE stereo samples
And the consumer pops into a buffer
Then the samples are recovered in FIFO order with correct channel interleaving

### Scenario: Overflow wraps around

Given the ring buffer is full
When additional frames are pushed
Then the oldest frames are overwritten
And the consumer can still pop the most recent frames

### Scenario: Concurrent SPSC correctness

Given a producer thread pushing 100K frames
And a consumer thread popping concurrently
Then all frames are eventually consumed without data corruption
