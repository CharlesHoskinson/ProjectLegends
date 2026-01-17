# Phase 4: Service Interfaces for Cross-Module Communication

## Objective

Formalize the contract between legends_core and aibox_core via explicit service interfaces. This enables:
- Clear documentation of the cross-module API
- Dependency injection for testing
- Future multi-instance support (V2 contract)

## Current State

The integration point already exists in a single file:
- `src/legends/legends_embed_api.cpp` includes `dosbox/dosbox_library.h`

This phase formalizes this pattern without breaking existing code.

## Deliverables

### 4.1 Create Service Interface Header

**File:** `engine/include/dosbox/engine_services.h`

```cpp
/**
 * @file engine_services.h
 * @brief Service interfaces for cross-module communication
 *
 * This header defines the formal contract between legends_core and aibox_core.
 * All cross-module calls SHOULD go through these interfaces.
 *
 * Benefits:
 * - Explicit documentation of the integration surface
 * - Enables dependency injection for testing
 * - Prepares for V2 multi-instance contract
 *
 * @note This header re-exports dosbox_library.h functions as typed aliases.
 *       Direct use of dosbox_library.h is still valid for backwards compatibility.
 */

#ifndef DOSBOX_ENGINE_SERVICES_H
#define DOSBOX_ENGINE_SERVICES_H

#include "dosbox_library.h"
#include "dosbox_context.h"
#include "engine_state.h"
#include "error_mapping.h"

#ifdef __cplusplus

namespace engine_services {

//-----------------------------------------------------------------------------
// Function type aliases
// These match the signatures in dosbox_library.h
//-----------------------------------------------------------------------------

/// Create a new DOSBox context
using create_fn = decltype(&dosbox_lib_create);

/// Destroy a DOSBox context
using destroy_fn = decltype(&dosbox_lib_destroy);

/// Step execution by milliseconds
using step_ms_fn = decltype(&dosbox_lib_step_ms);

/// Step execution by CPU cycles
using step_cycles_fn = decltype(&dosbox_lib_step_cycles);

/// Save state to buffer
using save_state_fn = decltype(&dosbox_lib_save_state);

/// Load state from buffer
using load_state_fn = decltype(&dosbox_lib_load_state);

/// Get state hash for determinism verification
using state_hash_fn = decltype(&dosbox_lib_state_hash);

/// Inject keyboard input
using inject_key_fn = decltype(&dosbox_lib_inject_key);

/// Inject mouse input
using inject_mouse_fn = decltype(&dosbox_lib_inject_mouse);

/// Get framebuffer
using get_framebuffer_fn = decltype(&dosbox_lib_get_framebuffer);

/// Get audio buffer
using get_audio_fn = decltype(&dosbox_lib_get_audio);

//-----------------------------------------------------------------------------
// Service Table
//
// A struct holding pointers to all engine functions.
// Default values point to the real implementation.
// Tests can swap in mocks.
//-----------------------------------------------------------------------------

/**
 * @brief Table of engine service function pointers
 *
 * Example usage:
 * @code
 * // Production code uses defaults
 * engine_services::ServiceTable services;
 * auto ctx = services.create(config);
 *
 * // Test code can inject mocks
 * engine_services::ServiceTable mock_services{
 *     .create = &mock_create,
 *     .destroy = &mock_destroy,
 *     // ... etc
 * };
 * @endcode
 */
struct ServiceTable {
    create_fn create = &dosbox_lib_create;
    destroy_fn destroy = &dosbox_lib_destroy;
    step_ms_fn step_ms = &dosbox_lib_step_ms;
    step_cycles_fn step_cycles = &dosbox_lib_step_cycles;
    save_state_fn save_state = &dosbox_lib_save_state;
    load_state_fn load_state = &dosbox_lib_load_state;
    state_hash_fn state_hash = &dosbox_lib_state_hash;
    inject_key_fn inject_key = &dosbox_lib_inject_key;
    inject_mouse_fn inject_mouse = &dosbox_lib_inject_mouse;
    get_framebuffer_fn get_framebuffer = &dosbox_lib_get_framebuffer;
    get_audio_fn get_audio = &dosbox_lib_get_audio;
};

//-----------------------------------------------------------------------------
// Global service accessor
//
// For production code, use default_services().
// For tests, create a local ServiceTable with mocks.
//-----------------------------------------------------------------------------

/**
 * @brief Get the default service table (production implementation)
 * @return Reference to static ServiceTable with real functions
 */
inline const ServiceTable& default_services() {
    static const ServiceTable instance;
    return instance;
}

} // namespace engine_services

#endif /* __cplusplus */

#endif /* DOSBOX_ENGINE_SERVICES_H */
```

### 4.2 Update legends_embed_api.cpp (Optional)

This step is optional - existing code continues to work. However, for documentation purposes, we can add a comment:

```cpp
// src/legends/legends_embed_api.cpp

// Cross-module integration uses engine services.
// See engine/include/dosbox/engine_services.h for the formal contract.
#include "dosbox/dosbox_library.h"  // Direct include still supported
// OR: #include "dosbox/engine_services.h"  // Service table approach

// Example of service table usage (optional refactoring):
#if 0  // Enable for dependency injection support
namespace {
    const engine_services::ServiceTable& services() {
        return engine_services::default_services();
    }
}

// Then use: services().step_cycles(ctx, cycles);
// Instead of: dosbox_lib_step_cycles(ctx, cycles);
#endif
```

### 4.3 Create Service Interface Documentation

**Add to:** `ARCHITECTURE.md`

```markdown
## Cross-Module Service Interfaces

### Engine Services (dosbox/engine_services.h)

The formal contract between `legends_core` and `aibox_core` is defined in
`engine/include/dosbox/engine_services.h`. This header:

1. Re-exports `dosbox_library.h` functions as typed aliases
2. Provides a `ServiceTable` struct for dependency injection
3. Documents the complete integration surface

**Production Usage:**
```cpp
#include "dosbox/engine_services.h"

auto ctx = dosbox_lib_create(config);  // Direct call (preferred)
// OR
auto ctx = engine_services::default_services().create(config);  // Via table
```

**Test Usage (Mocking):**
```cpp
#include "dosbox/engine_services.h"

// Create mock service table
engine_services::ServiceTable mocks{
    .create = [](auto) { return mock_context; },
    .step_cycles = [](auto, auto) { return mock_result; },
    // ...
};

// Pass mocks to code under test
my_function(mocks);
```

### Service Categories

| Category | Functions | Purpose |
|----------|-----------|---------|
| Lifecycle | create, destroy | Context management |
| Execution | step_ms, step_cycles | Emulation stepping |
| State | save_state, load_state, state_hash | Persistence |
| Input | inject_key, inject_mouse | User input |
| Output | get_framebuffer, get_audio | A/V access |
```

## Implementation Steps

| Step | Action | Files |
|------|--------|-------|
| 4.1.1 | Create engine_services.h | engine/include/dosbox/engine_services.h |
| 4.2.1 | Add comment to legends_embed_api.cpp | src/legends/legends_embed_api.cpp |
| 4.3.1 | Add Service Interfaces section | ARCHITECTURE.md |
| 4.4.1 | Verify header compiles standalone | Build test |

## Test Plan

### Unit Tests

```cpp
// tests/unit/test_engine_services.cpp

#include "dosbox/engine_services.h"
#include <gtest/gtest.h>

TEST(EngineServices, DefaultServicesPointToRealFunctions) {
    const auto& services = engine_services::default_services();

    // Verify function pointers are not null
    EXPECT_NE(services.create, nullptr);
    EXPECT_NE(services.destroy, nullptr);
    EXPECT_NE(services.step_cycles, nullptr);
    EXPECT_NE(services.save_state, nullptr);
    EXPECT_NE(services.load_state, nullptr);
}

TEST(EngineServices, ServiceTableCanBeCustomized) {
    // Mock function
    static bool create_called = false;
    auto mock_create = [](void*) -> void* {
        create_called = true;
        return nullptr;
    };

    engine_services::ServiceTable mocks{
        .create = mock_create,
    };

    mocks.create(nullptr);
    EXPECT_TRUE(create_called);
}

TEST(EngineServices, FunctionSignaturesMatch) {
    // These will fail at compile time if signatures don't match
    engine_services::create_fn fn1 = &dosbox_lib_create;
    engine_services::step_cycles_fn fn2 = &dosbox_lib_step_cycles;

    EXPECT_NE(fn1, nullptr);
    EXPECT_NE(fn2, nullptr);
}
```

### Integration Tests

```cpp
// tests/integration/test_service_injection.cpp

#include "dosbox/engine_services.h"
#include <gtest/gtest.h>

class MockableComponent {
public:
    explicit MockableComponent(const engine_services::ServiceTable& svc)
        : services_(svc) {}

    void* create(void* config) {
        return services_.create(config);
    }

private:
    const engine_services::ServiceTable& services_;
};

TEST(ServiceInjection, CanInjectMockServices) {
    static int call_count = 0;

    engine_services::ServiceTable mocks{
        .create = [](void*) -> void* {
            ++call_count;
            return reinterpret_cast<void*>(0xDEAD);
        },
    };

    MockableComponent component(mocks);
    void* result = component.create(nullptr);

    EXPECT_EQ(call_count, 1);
    EXPECT_EQ(result, reinterpret_cast<void*>(0xDEAD));
}
```

### Manual Verification

| Test | Command | Expected Result |
|------|---------|-----------------|
| Header compiles | Include in test file, build | No errors |
| Default services work | Call default_services() | Returns valid table |
| Type aliases match | Assign function to alias | Compiles |
| Documentation accurate | Review ARCHITECTURE.md | Matches implementation |

### Acceptance Criteria

- [ ] `engine/include/dosbox/engine_services.h` exists
- [ ] Header is self-contained (compiles with just its own includes)
- [ ] All dosbox_library.h functions have corresponding aliases
- [ ] ServiceTable default values point to real functions
- [ ] Unit tests pass
- [ ] ARCHITECTURE.md updated with Service Interfaces section

## Rollback Plan

If issues arise:
1. Delete engine/include/dosbox/engine_services.h
2. Remove test file tests/unit/test_engine_services.cpp
3. Revert ARCHITECTURE.md changes

**Git commands:**
```bash
git rm engine/include/dosbox/engine_services.h
git rm tests/unit/test_engine_services.cpp
git checkout HEAD -- ARCHITECTURE.md
```

No build impact - this phase is additive and optional.

## Future Work (V2 Contract)

When implementing multi-instance support (V2), the ServiceTable pattern enables:

1. **Per-instance services:** Each instance can have its own ServiceTable
2. **Isolation testing:** Test instances in parallel with different mocks
3. **Plugin architecture:** Replace engine functions at runtime
