# ─────────────────────────────────────────────────────────────────────────────
# AIBox Test Configuration
# ─────────────────────────────────────────────────────────────────────────────

# ─────────────────────────────────────────────────────────────────────────────
# Test Fixtures Library
# ─────────────────────────────────────────────────────────────────────────────

add_library(aibox_test_fixtures INTERFACE)
target_include_directories(aibox_test_fixtures INTERFACE
    ${CMAKE_CURRENT_SOURCE_DIR}/fixtures
    ${CMAKE_SOURCE_DIR}/include
)
target_link_libraries(aibox_test_fixtures INTERFACE
    GTest::gtest
    GTest::gmock
)

# ─────────────────────────────────────────────────────────────────────────────
# Unit Tests
# ─────────────────────────────────────────────────────────────────────────────

add_executable(aibox_unit_tests
    # DOSBox-X Library Mode (PR #2-17: Error Model, Logging, Safe Call, State Hash, Handle, Context, Timing, CPU, Mixer, VGA, PIC/KB/Input, Platform, Headless, TimingInt)
    unit/test_dosbox_error_model.cpp
    unit/test_dosbox_logging.cpp
    unit/test_dosbox_safe_call.cpp
    unit/test_dosbox_state_hash.cpp
    unit/test_dosbox_instance_handle.cpp
    unit/test_dosbox_context.cpp
    unit/test_dosbox_timing.cpp
    unit/test_dosbox_cpu.cpp
    unit/test_dosbox_mixer.cpp
    unit/test_dosbox_vga.cpp
    unit/test_dosbox_pic_keyboard_input.cpp
    unit/test_platform_interfaces.cpp
    unit/test_headless_backend.cpp
    unit/test_timing_integration.cpp
    unit/test_display_integration.cpp
    unit/test_input_integration.cpp
    unit/test_audio_integration.cpp
    # PR #22: DOSBox-X Embeddable Library API
    unit/test_dosbox_library.cpp
    # Phase 1: Foundation
    unit/test_error.cpp
    unit/test_result.cpp
    unit/test_exceptions.cpp
    unit/test_ffi.cpp
    # Phase 2: Memory Safety
    unit/test_span.cpp
    unit/test_memory.cpp
    unit/test_io_port.cpp
    unit/test_dma.cpp
    # Phase 3: Global State Encapsulation
    unit/test_cpu_context.cpp
    unit/test_machine_context.cpp
    unit/test_compat_shim.cpp
    # Phase 4: Modern C++ Patterns
    unit/test_function_ref.cpp
    unit/test_callback_registry.cpp
    unit/test_enums.cpp
    unit/test_builder.cpp
    unit/test_optional_utils.cpp
    # Phase 5: Interface Improvements
    unit/test_events.cpp
    unit/test_handle_registry.cpp
    unit/test_event_bus.cpp
    # Phase 6: LLM-Optimized I/O
    unit/test_llm_frame.cpp
    unit/test_llm_actions.cpp
    unit/test_llm_serializer.cpp
    unit/test_llm_diff.cpp
    # Phase 7: Vision Model Integration
    unit/test_vision_framebuffer.cpp
    unit/test_vision_capture.cpp
    unit/test_vision_overlay.cpp
    unit/test_vision_annotations.cpp
    # Sprint 2: Instance Reality
    unit/test_dma_migration.cpp
    unit/test_dos_migration.cpp
    unit/test_pic_migration.cpp
    unit/test_vga_migration.cpp
    unit/test_memory_migration.cpp
    unit/test_keyboard_migration.cpp
)

target_link_libraries(aibox_unit_tests PRIVATE
    aibox_core
    aibox_test_fixtures
    GTest::gtest_main
)

# Enable library mode for tests
target_compile_definitions(aibox_unit_tests PRIVATE AIBOX_LIBRARY_MODE=1)

# Discover tests for CTest
gtest_discover_tests(aibox_unit_tests
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    PROPERTIES
        LABELS "unit"
)

# ─────────────────────────────────────────────────────────────────────────────
# Integration Tests (placeholder for future phases)
# ─────────────────────────────────────────────────────────────────────────────

# add_executable(aibox_integration_tests
#     integration/test_lifecycle.cpp
# )
#
# target_link_libraries(aibox_integration_tests PRIVATE
#     aibox_core
#     aibox_test_fixtures
#     GTest::gtest_main
# )
#
# gtest_discover_tests(aibox_integration_tests
#     WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
#     PROPERTIES
#         LABELS "integration"
#         TIMEOUT 60
# )

# ─────────────────────────────────────────────────────────────────────────────
# Determinism Tests (PR #23)
# ─────────────────────────────────────────────────────────────────────────────

add_subdirectory(determinism)

# ─────────────────────────────────────────────────────────────────────────────
# Custom Test Targets
# ─────────────────────────────────────────────────────────────────────────────

# Run only unit tests
add_custom_target(test-unit
    COMMAND ${CMAKE_CTEST_COMMAND} -L unit --output-on-failure
    DEPENDS aibox_unit_tests
    COMMENT "Running unit tests"
)

# Run all tests
add_custom_target(test-all
    COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
    DEPENDS aibox_unit_tests aibox_determinism_tests
    COMMENT "Running all tests"
)
