# ─────────────────────────────────────────────────────────────────────────────
# Fuzz Testing with libFuzzer
# ─────────────────────────────────────────────────────────────────────────────
#
# Usage:
#   cmake -B build -DENABLE_FUZZING=ON -DCMAKE_CXX_COMPILER=clang++
#   cmake --build build --target fuzz_legends_load_state
#   ./build/tests/fuzz/fuzz_legends_load_state corpus/ -max_len=8192
#
# With sanitizers (recommended):
#   cmake -B build -DENABLE_FUZZING=ON -DENABLE_ASAN=ON -DCMAKE_CXX_COMPILER=clang++
#
# Corpus generator (works with any compiler):
#   cmake -B build -DENABLE_FUZZING=ON  # Just to include this subdirectory
#   cmake --build build --target generate_fuzz_corpus
#   ./build/tests/fuzz/generate_fuzz_corpus corpus/
#
# ─────────────────────────────────────────────────────────────────────────────

# ─────────────────────────────────────────────────────────────────────────────
# Corpus generator (works with any compiler - no libFuzzer required)
# ─────────────────────────────────────────────────────────────────────────────

add_executable(generate_fuzz_corpus
    generate_corpus.cpp
)

target_link_libraries(generate_fuzz_corpus PRIVATE
    legends_core
    aibox_core
)

target_compile_definitions(generate_fuzz_corpus PRIVATE
    AIBOX_LIBRARY_MODE=1
    AIBOX_HEADLESS=1
)

# Create corpus directory in build tree
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/corpus)

# Copy seed corpus if it exists
if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/corpus)
    file(COPY ${CMAKE_CURRENT_SOURCE_DIR}/corpus
         DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
endif()

# Convenience target to generate corpus
add_custom_target(generate-corpus
    COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/corpus
    COMMAND $<TARGET_FILE:generate_fuzz_corpus> ${CMAKE_CURRENT_BINARY_DIR}/corpus
    DEPENDS generate_fuzz_corpus
    COMMENT "Generating seed corpus for fuzzing"
)

# ─────────────────────────────────────────────────────────────────────────────
# Fuzz targets (require Clang with libFuzzer)
# ─────────────────────────────────────────────────────────────────────────────

if(NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(STATUS "Fuzz targets disabled (requires Clang compiler for libFuzzer)")
    message(STATUS "  Corpus generator is still available: generate_fuzz_corpus")
    return()
endif()

message(STATUS "Fuzzing enabled with libFuzzer")

# ─────────────────────────────────────────────────────────────────────────────
# Common fuzzer settings
# ─────────────────────────────────────────────────────────────────────────────

set(FUZZ_COMPILE_OPTIONS
    -fsanitize=fuzzer
    -fno-omit-frame-pointer
)

set(FUZZ_LINK_OPTIONS
    -fsanitize=fuzzer
)

# Add sanitizers if requested
if(ENABLE_ASAN)
    list(APPEND FUZZ_COMPILE_OPTIONS -fsanitize=address)
    list(APPEND FUZZ_LINK_OPTIONS -fsanitize=address)
    message(STATUS "  AddressSanitizer enabled")
endif()

if(ENABLE_UBSAN)
    list(APPEND FUZZ_COMPILE_OPTIONS -fsanitize=undefined)
    list(APPEND FUZZ_LINK_OPTIONS -fsanitize=undefined)
    message(STATUS "  UndefinedBehaviorSanitizer enabled")
endif()

if(ENABLE_MSAN)
    list(APPEND FUZZ_COMPILE_OPTIONS -fsanitize=memory)
    list(APPEND FUZZ_LINK_OPTIONS -fsanitize=memory)
    message(STATUS "  MemorySanitizer enabled")
endif()

# ─────────────────────────────────────────────────────────────────────────────
# Fuzz target: legends_load_state
# ─────────────────────────────────────────────────────────────────────────────

add_executable(fuzz_legends_load_state
    fuzz_legends_load_state.cpp
)

target_link_libraries(fuzz_legends_load_state PRIVATE
    legends_core
    aibox_core
)

target_compile_options(fuzz_legends_load_state PRIVATE
    ${FUZZ_COMPILE_OPTIONS}
)

target_link_options(fuzz_legends_load_state PRIVATE
    ${FUZZ_LINK_OPTIONS}
)

target_compile_definitions(fuzz_legends_load_state PRIVATE
    AIBOX_LIBRARY_MODE=1
    AIBOX_HEADLESS=1
)

# ─────────────────────────────────────────────────────────────────────────────
# Fuzz target: dosbox_lib_load_state (engine level)
# ─────────────────────────────────────────────────────────────────────────────

add_executable(fuzz_engine_load_state
    fuzz_engine_load_state.cpp
)

target_link_libraries(fuzz_engine_load_state PRIVATE
    aibox_core
)

target_include_directories(fuzz_engine_load_state PRIVATE
    ${CMAKE_SOURCE_DIR}/engine/include
)

target_compile_options(fuzz_engine_load_state PRIVATE
    ${FUZZ_COMPILE_OPTIONS}
)

target_link_options(fuzz_engine_load_state PRIVATE
    ${FUZZ_LINK_OPTIONS}
)

target_compile_definitions(fuzz_engine_load_state PRIVATE
    AIBOX_LIBRARY_MODE=1
    AIBOX_HEADLESS=1
)

# ─────────────────────────────────────────────────────────────────────────────
# Convenience targets
# ─────────────────────────────────────────────────────────────────────────────

add_custom_target(fuzz-all
    DEPENDS fuzz_legends_load_state fuzz_engine_load_state
    COMMENT "Building all fuzz targets"
)

# Run fuzzers (short run for CI)
add_custom_target(fuzz-quick
    COMMAND $<TARGET_FILE:fuzz_legends_load_state>
            ${CMAKE_CURRENT_BINARY_DIR}/corpus
            -max_len=8192
            -max_total_time=60
    DEPENDS fuzz_legends_load_state
    COMMENT "Running quick fuzz test (60 seconds)"
)
