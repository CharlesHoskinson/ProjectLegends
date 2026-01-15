# ─────────────────────────────────────────────────────────────────────────────
# AIBox Determinism Test Suite (PR #23)
# ─────────────────────────────────────────────────────────────────────────────
#
# Tests for verifying deterministic execution:
# - State hash consistency
# - Replay determinism
# - Save/load round-trip
# - Golden trace verification
#

add_executable(aibox_determinism_tests
    test_determinism.cpp
)

target_include_directories(aibox_determinism_tests PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_SOURCE_DIR}/include
)

target_link_libraries(aibox_determinism_tests PRIVATE
    aibox_core
    GTest::gtest
    GTest::gtest_main
)

# Enable library mode for tests
target_compile_definitions(aibox_determinism_tests PRIVATE
    AIBOX_LIBRARY_MODE=1
)

# Discover tests with "determinism" label
gtest_discover_tests(aibox_determinism_tests
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    PROPERTIES
        LABELS "determinism"
        TIMEOUT 120  # Longer timeout for determinism tests
)

# Custom target to run only determinism tests
add_custom_target(test-determinism
    COMMAND ${CMAKE_CTEST_COMMAND} -L determinism --output-on-failure
    DEPENDS aibox_determinism_tests
    COMMENT "Running determinism tests"
)
