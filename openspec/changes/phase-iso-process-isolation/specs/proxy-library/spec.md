# Proxy Library Specification

Requirements: REQ-ISO-010, REQ-ISO-011

## REQ-ISO-010: Proxy Implements legends_embed.h

### Scenario: Function signature matching

Given `legends_proxy` library
When built with `LEGENDS_USE_IPC=ON`
Then it exports every symbol from `legends_embed.h`
And the linker resolves all references from the application shell

### Scenario: IPC forwarding

Given a connected `ProxyConnection`
When any `legends_*()` function is called through the proxy
Then the proxy serializes the request, sends it over the control channel
And deserializes the response from the engine host

### Scenario: Not-connected returns error

Given `ProxyConnection` is not connected
When any `legends_*()` function is called
Then it returns `LEGENDS_ERR_NOT_INITIALIZED` immediately

## REQ-ISO-011: Backend Switch

### Scenario: CMake backend selection

Given `LEGENDS_USE_IPC=ON`
When the application shell is built
Then it links `legends_proxy` + `legends_pal` (MIT)
And does NOT link `legends_core` or `aibox_core` (GPL)

Given `LEGENDS_USE_IPC=OFF` (or unset)
When the application shell is built
Then it links `legends_core` + `legends_pal` (monolithic)
