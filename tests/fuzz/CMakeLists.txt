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

target_include_directories(generate_fuzz_corpus PRIVATE
    ${CMAKE_SOURCE_DIR}/engine/include
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
    if(WIN32)
        list(APPEND FUZZ_COMPILE_OPTIONS
            -D_DISABLE_STRING_ANNOTATION
            -D_DISABLE_VECTOR_ANNOTATION
            -D_DISABLE_OPTIONAL_ANNOTATION
        )
    endif()
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

# When the project builds against libc++, the prebuilt libFuzzer runtime
# still references libstdc++ internals (iostreams, __throw_* helpers). The
# driver appends the runtime archive after every user library, where nothing
# can resolve those references, so link the archive explicitly and follow it
# with libstdc++. FUZZER_RUNTIME_LIBS is empty in plain-libstdc++ builds.
set(FUZZER_RUNTIME_LIBS "")
if(CMAKE_CXX_FLAGS MATCHES "-stdlib=libc\\+\\+")
    if(NOT CMAKE_SYSTEM_PROCESSOR)
        set(_fuzzer_rt_arch "x86_64")
    else()
        set(_fuzzer_rt_arch "${CMAKE_SYSTEM_PROCESSOR}")
    endif()
    execute_process(
        COMMAND ${CMAKE_CXX_COMPILER} -print-file-name=libclang_rt.fuzzer-${_fuzzer_rt_arch}.a
        OUTPUT_VARIABLE LIBFUZZER_RT
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    # Absolute path: under -stdlib=libc++ a plain -lstdc++ is not honored at
    # its command-line position, so pass the shared object verbatim.
    find_library(LIBSTDCXX_SHARED NAMES stdc++ libstdc++.so.6
        PATHS /usr/lib/x86_64-linux-gnu /usr/lib64 /usr/lib)
    if(NOT LIBSTDCXX_SHARED)
        file(GLOB _libstdcxx_candidates /usr/lib/x86_64-linux-gnu/libstdc++.so.6*)
        if(_libstdcxx_candidates)
            list(GET _libstdcxx_candidates 0 LIBSTDCXX_SHARED)
        endif()
    endif()
    if(EXISTS "${LIBFUZZER_RT}" AND LIBSTDCXX_SHARED)
        list(REMOVE_ITEM FUZZ_LINK_OPTIONS -fsanitize=fuzzer)
        list(PREPEND FUZZ_LINK_OPTIONS -fsanitize=fuzzer-no-link)
        set(FUZZER_RUNTIME_LIBS "${LIBFUZZER_RT}" "${LIBSTDCXX_SHARED}")
        message(STATUS "  libc++ build: linking libFuzzer runtime explicitly + ${LIBSTDCXX_SHARED}")
    else()
        message(WARNING "  libc++ build but libFuzzer runtime/libstdc++ not found (${LIBFUZZER_RT} / ${LIBSTDCXX_SHARED}); relying on driver link")
    endif()
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
    ${FUZZER_RUNTIME_LIBS}
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
    ${FUZZER_RUNTIME_LIBS}
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
# Fuzz target: V5 RAM blob with CRC-aware mutator
# ─────────────────────────────────────────────────────────────────────────────

add_executable(fuzz_engine_memory_blob
    fuzz_engine_memory_blob.cpp
)

target_link_libraries(fuzz_engine_memory_blob PRIVATE
    aibox_core
    ${FUZZER_RUNTIME_LIBS}
)

target_include_directories(fuzz_engine_memory_blob PRIVATE
    ${CMAKE_SOURCE_DIR}/engine/include
)

target_compile_options(fuzz_engine_memory_blob PRIVATE
    ${FUZZ_COMPILE_OPTIONS}
)

target_link_options(fuzz_engine_memory_blob PRIVATE
    ${FUZZ_LINK_OPTIONS}
)

target_compile_definitions(fuzz_engine_memory_blob PRIVATE
    AIBOX_LIBRARY_MODE=1
    AIBOX_HEADLESS=1
)

# ─────────────────────────────────────────────────────────────────────────────
# Fuzz target: input injection (legends API level)
# ─────────────────────────────────────────────────────────────────────────────

add_executable(fuzz_input_injection
    fuzz_input_injection.cpp
)

target_link_libraries(fuzz_input_injection PRIVATE
    legends_core
    legends_pal
    aibox_core
    ${FUZZER_RUNTIME_LIBS}
)

target_compile_options(fuzz_input_injection PRIVATE
    ${FUZZ_COMPILE_OPTIONS}
)

target_link_options(fuzz_input_injection PRIVATE
    ${FUZZ_LINK_OPTIONS}
)

target_compile_definitions(fuzz_input_injection PRIVATE
    AIBOX_LIBRARY_MODE=1
    AIBOX_HEADLESS=1
)

# ─────────────────────────────────────────────────────────────────────────────
# Fuzz target: config parser (legends app level)
# ─────────────────────────────────────────────────────────────────────────────

add_executable(fuzz_config_parser
    fuzz_config_parser.cpp
    ${CMAKE_SOURCE_DIR}/src/app/config_parser.cpp
    ${CMAKE_SOURCE_DIR}/src/app/platform_dirs.cpp
)

target_link_libraries(fuzz_config_parser PRIVATE
    legends_core
    # config_parser.cpp is recompiled directly into this target, so it needs
    # gsl-lite itself — the dep is deliberately PRIVATE to legends_core and
    # does not propagate.
    gsl::gsl-lite-v1
    ${FUZZER_RUNTIME_LIBS}
)

target_include_directories(fuzz_config_parser PRIVATE
    ${CMAKE_SOURCE_DIR}/src
)

target_compile_options(fuzz_config_parser PRIVATE
    ${FUZZ_COMPILE_OPTIONS}
)

target_link_options(fuzz_config_parser PRIVATE
    ${FUZZ_LINK_OPTIONS}
)

target_compile_definitions(fuzz_config_parser PRIVATE
    AIBOX_LIBRARY_MODE=1
    AIBOX_HEADLESS=1
    # Match legends_core's gsl-lite v1 contract configuration (CMakeLists.txt
    # legends_core block) so the recompiled TU behaves identically.
    gsl_CONFIG_DEFAULTS_VERSION=1
    gsl_FEATURE_GSL_COMPATIBILITY_MODE=0
    gsl_FEATURE_STRING_SPAN=0
    gsl_FEATURE_BYTE=0
    gsl_CONFIG_NOT_NULL_EXPLICIT_CTOR=1
    gsl_CONFIG_TRANSPARENT_NOT_NULL=1
    gsl_CONFIG_CONTRACT_CHECKING_ON
    gsl_CONFIG_UNENFORCED_CONTRACTS_ELIDE
    $<$<BOOL:${LEGENDS_LIBRARY_MODE}>:gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1>
    $<$<NOT:$<BOOL:${LEGENDS_LIBRARY_MODE}>>:gsl_CONFIG_CONTRACT_VIOLATION_TERMINATES=1>
)

# ─────────────────────────────────────────────────────────────────────────────
# Convenience targets
# ─────────────────────────────────────────────────────────────────────────────

add_custom_target(fuzz-all
    DEPENDS fuzz_legends_load_state fuzz_engine_load_state fuzz_engine_memory_blob fuzz_input_injection fuzz_config_parser
    COMMENT "Building all fuzz targets"
)

# Run fuzzers (short run for CI)
add_custom_target(fuzz-quick
    COMMAND $<TARGET_FILE:fuzz_engine_memory_blob>
            ${CMAKE_CURRENT_BINARY_DIR}/corpus/engine_memory_blob
            -max_len=1048576
            -max_total_time=60
    COMMAND $<TARGET_FILE:fuzz_legends_load_state>
            ${CMAKE_CURRENT_BINARY_DIR}/corpus
            -max_len=8192
            -max_total_time=60
    DEPENDS fuzz_engine_memory_blob fuzz_legends_load_state generate-corpus
    COMMENT "Running quick fuzz test (60 seconds)"
)
