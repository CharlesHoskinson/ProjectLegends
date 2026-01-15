/**
 * @file test_legends_abi.c
 * @brief Pure C ABI verification tests for legends_embed.h
 *
 * This file MUST compile as pure C (C11) to verify the header
 * is usable from C code. Run with: gcc -std=c11 -c test_legends_abi.c
 *
 * These tests verify:
 * 1. Header compiles as pure C
 * 2. Struct sizes and layouts are stable
 * 3. Version handshake works
 * 4. Single-instance enforcement
 * 5. Null pointer handling
 */

#include "legends/legends_embed.h"
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* =========================================================================
 * ABI SIZE ASSERTIONS
 *
 * These catch ABI-breaking changes. If any of these fail, it means the
 * struct layout changed and may break existing binaries.
 * ========================================================================= */

static void test_abi_sizes(void) {
    printf("Testing ABI sizes...\n");

    /* Fixed-size structs (platform-independent) */
    assert(sizeof(legends_text_cell_t) == 2);
    assert(sizeof(legends_text_info_t) == 8);
    assert(sizeof(legends_step_result_t) == 24);

    /* legends_config_t size depends on pointer size and alignment.
     * After deterministic + _pad3 we're at offset 36. Pointers need
     * 8-byte alignment on 64-bit, so there's 4 bytes of padding.
     * Layout on 64-bit: 36 + 4(pad) + 8(config_path) + 8(working_dir) + 64(_reserved) = 120
     * Layout on 32-bit: 36 + 4(config_path) + 4(working_dir) + 64(_reserved) = 108 */
#if defined(__LP64__) || defined(_WIN64) || defined(__x86_64__) || defined(__aarch64__)
    /* 64-bit platforms: pointers are 8 bytes with alignment padding */
    assert(sizeof(legends_config_t) == 120);
#else
    /* 32-bit platforms: pointers are 4 bytes, no padding needed */
    assert(sizeof(legends_config_t) == 108);
#endif

    printf("  All size assertions passed.\n");
}

/* =========================================================================
 * FIELD OFFSET ASSERTIONS
 *
 * Verify critical field offsets are stable.
 * ========================================================================= */

static void test_field_offsets(void) {
    printf("Testing field offsets...\n");

    /* legends_text_cell_t */
    assert(offsetof(legends_text_cell_t, character) == 0);
    assert(offsetof(legends_text_cell_t, attribute) == 1);

    /* legends_text_info_t */
    assert(offsetof(legends_text_info_t, columns) == 0);
    assert(offsetof(legends_text_info_t, rows) == 1);
    assert(offsetof(legends_text_info_t, active_page) == 2);
    assert(offsetof(legends_text_info_t, cursor_x) == 3);
    assert(offsetof(legends_text_info_t, cursor_y) == 4);
    assert(offsetof(legends_text_info_t, cursor_visible) == 5);

    /* legends_step_result_t */
    assert(offsetof(legends_step_result_t, cycles_executed) == 0);
    assert(offsetof(legends_step_result_t, emu_time_us) == 8);
    assert(offsetof(legends_step_result_t, stop_reason) == 16);
    assert(offsetof(legends_step_result_t, events_processed) == 20);

    /* legends_config_t - first fields should be at known offsets */
    assert(offsetof(legends_config_t, struct_size) == 0);
    assert(offsetof(legends_config_t, api_version) == 4);
    assert(offsetof(legends_config_t, memory_kb) == 8);
    assert(offsetof(legends_config_t, xms_kb) == 12);
    assert(offsetof(legends_config_t, ems_kb) == 16);
    assert(offsetof(legends_config_t, cpu_cycles) == 20);
    assert(offsetof(legends_config_t, cpu_type) == 24);
    assert(offsetof(legends_config_t, machine_type) == 28);
    assert(offsetof(legends_config_t, deterministic) == 32);

    /* Pointer fields have platform-dependent offsets due to alignment */
#if defined(__LP64__) || defined(_WIN64) || defined(__x86_64__) || defined(__aarch64__)
    assert(offsetof(legends_config_t, config_path) == 40);  /* 4 bytes padding after deterministic+_pad3 */
    assert(offsetof(legends_config_t, working_dir) == 48);
    assert(offsetof(legends_config_t, _reserved) == 56);
#else
    assert(offsetof(legends_config_t, config_path) == 36);
    assert(offsetof(legends_config_t, working_dir) == 40);
    assert(offsetof(legends_config_t, _reserved) == 44);
#endif

    printf("  All offset assertions passed.\n");
}

/* =========================================================================
 * VERSION CONSTANTS
 * ========================================================================= */

static void test_version_constants(void) {
    printf("Testing version constants...\n");

    /* Verify version macros are defined and reasonable */
    assert(LEGENDS_API_VERSION_MAJOR == 1);
    assert(LEGENDS_API_VERSION_MINOR == 0);
    assert(LEGENDS_API_VERSION_PATCH == 0);

    /* Verify packed version */
    uint32_t expected = (1 << 16) | (0 << 8) | 0;
    assert(LEGENDS_API_VERSION == expected);

    printf("  Version constants verified: %u.%u.%u\n",
           LEGENDS_API_VERSION_MAJOR,
           LEGENDS_API_VERSION_MINOR,
           LEGENDS_API_VERSION_PATCH);
}

/* =========================================================================
 * ERROR CODE CONSTANTS
 * ========================================================================= */

static void test_error_codes(void) {
    printf("Testing error codes...\n");

    /* LEGENDS_OK must be 0 */
    assert(LEGENDS_OK == 0);

    /* All error codes must be negative (or at least non-zero) */
    assert(LEGENDS_ERR_NULL_HANDLE != 0);
    assert(LEGENDS_ERR_NULL_POINTER != 0);
    assert(LEGENDS_ERR_ALREADY_CREATED != 0);
    assert(LEGENDS_ERR_NOT_INITIALIZED != 0);
    assert(LEGENDS_ERR_REENTRANT_CALL != 0);
    assert(LEGENDS_ERR_BUFFER_TOO_SMALL != 0);
    assert(LEGENDS_ERR_INVALID_CONFIG != 0);
    assert(LEGENDS_ERR_INVALID_STATE != 0);
    assert(LEGENDS_ERR_VERSION_MISMATCH != 0);
    assert(LEGENDS_ERR_IO_FAILED != 0);
    assert(LEGENDS_ERR_OUT_OF_MEMORY != 0);
    assert(LEGENDS_ERR_NOT_SUPPORTED != 0);
    assert(LEGENDS_ERR_INTERNAL != 0);

    /* All error codes must be distinct */
    legends_error_t codes[] = {
        LEGENDS_OK,
        LEGENDS_ERR_NULL_HANDLE,
        LEGENDS_ERR_NULL_POINTER,
        LEGENDS_ERR_ALREADY_CREATED,
        LEGENDS_ERR_NOT_INITIALIZED,
        LEGENDS_ERR_REENTRANT_CALL,
        LEGENDS_ERR_BUFFER_TOO_SMALL,
        LEGENDS_ERR_INVALID_CONFIG,
        LEGENDS_ERR_INVALID_STATE,
        LEGENDS_ERR_VERSION_MISMATCH,
        LEGENDS_ERR_IO_FAILED,
        LEGENDS_ERR_OUT_OF_MEMORY,
        LEGENDS_ERR_NOT_SUPPORTED,
        LEGENDS_ERR_INTERNAL
    };
    size_t num_codes = sizeof(codes) / sizeof(codes[0]);

    for (size_t i = 0; i < num_codes; i++) {
        for (size_t j = i + 1; j < num_codes; j++) {
            assert(codes[i] != codes[j]);
        }
    }

    printf("  All %zu error codes are distinct.\n", num_codes);
}

/* =========================================================================
 * STOP REASON CONSTANTS
 * ========================================================================= */

static void test_stop_reasons(void) {
    printf("Testing stop reason constants...\n");

    /* LEGENDS_STOP_COMPLETED must be 0 */
    assert(LEGENDS_STOP_COMPLETED == 0);

    /* All stop reasons must be distinct */
    assert(LEGENDS_STOP_COMPLETED != LEGENDS_STOP_HALT);
    assert(LEGENDS_STOP_COMPLETED != LEGENDS_STOP_BREAKPOINT);
    assert(LEGENDS_STOP_COMPLETED != LEGENDS_STOP_ERROR);
    assert(LEGENDS_STOP_HALT != LEGENDS_STOP_BREAKPOINT);
    assert(LEGENDS_STOP_HALT != LEGENDS_STOP_ERROR);
    assert(LEGENDS_STOP_BREAKPOINT != LEGENDS_STOP_ERROR);

    printf("  Stop reason constants verified.\n");
}

/* =========================================================================
 * CONFIG INITIALIZER
 * ========================================================================= */

static void test_config_initializer(void) {
    printf("Testing config initializer...\n");

    legends_config_t config = LEGENDS_CONFIG_INIT;

    assert(config.struct_size == sizeof(legends_config_t));
    assert(config.api_version == LEGENDS_API_VERSION);
    assert(config.memory_kb == 640);
    assert(config.xms_kb == 0);
    assert(config.ems_kb == 0);
    assert(config.cpu_cycles == 0);
    assert(config.cpu_type == 0);
    assert(config.machine_type == 0);
    assert(config.deterministic == 1);
    assert(config.config_path == NULL);
    assert(config.working_dir == NULL);

    printf("  Config initializer sets correct defaults.\n");
}

/* =========================================================================
 * VERSION HANDSHAKE API
 * ========================================================================= */

static void test_version_handshake(void) {
    printf("Testing version handshake API...\n");

    uint32_t major, minor, patch;
    legends_error_t err;

    /* Normal call should succeed */
    err = legends_get_api_version(&major, &minor, &patch);
    assert(err == LEGENDS_OK);
    assert(major == LEGENDS_API_VERSION_MAJOR);
    assert(minor == LEGENDS_API_VERSION_MINOR);
    assert(patch == LEGENDS_API_VERSION_PATCH);

    /* Null pointer handling */
    err = legends_get_api_version(NULL, &minor, &patch);
    assert(err == LEGENDS_ERR_NULL_POINTER);

    err = legends_get_api_version(&major, NULL, &patch);
    assert(err == LEGENDS_ERR_NULL_POINTER);

    err = legends_get_api_version(&major, &minor, NULL);
    assert(err == LEGENDS_ERR_NULL_POINTER);

    printf("  Version handshake works correctly.\n");
}

/* =========================================================================
 * INSTANCE LIFECYCLE
 * ========================================================================= */

static void test_instance_lifecycle(void) {
    printf("Testing instance lifecycle...\n");

    legends_handle handle = NULL;
    legends_error_t err;

    /* Create with NULL config (defaults) */
    err = legends_create(NULL, &handle);
    assert(err == LEGENDS_OK);
    assert(handle != NULL);

    /* Second create should fail (single instance) */
    legends_handle handle2 = NULL;
    err = legends_create(NULL, &handle2);
    assert(err == LEGENDS_ERR_ALREADY_CREATED);
    assert(handle2 == NULL);

    /* Destroy */
    err = legends_destroy(handle);
    assert(err == LEGENDS_OK);

    /* Can create again after destroy */
    err = legends_create(NULL, &handle);
    assert(err == LEGENDS_OK);
    assert(handle != NULL);

    /* Clean up */
    legends_destroy(handle);

    printf("  Instance lifecycle works correctly.\n");
}

/* =========================================================================
 * NULL HANDLE/POINTER REJECTION
 * ========================================================================= */

static void test_null_handle_rejection(void) {
    printf("Testing null handle rejection...\n");

    legends_error_t err;

    /* Create null check */
    err = legends_create(NULL, NULL);
    assert(err == LEGENDS_ERR_NULL_POINTER);

    /* Functions that require handle */
    err = legends_reset(NULL);
    assert(err == LEGENDS_ERR_NULL_HANDLE);

    legends_config_t config;
    err = legends_get_config(NULL, &config);
    assert(err == LEGENDS_ERR_NULL_HANDLE);

    err = legends_step_ms(NULL, 100, NULL);
    assert(err == LEGENDS_ERR_NULL_HANDLE);

    err = legends_step_cycles(NULL, 1000, NULL);
    assert(err == LEGENDS_ERR_NULL_HANDLE);

    /* Destroy null is OK (no-op) */
    err = legends_destroy(NULL);
    assert(err == LEGENDS_OK);

    printf("  Null handle rejection works correctly.\n");
}

/* =========================================================================
 * CONFIG VALIDATION
 * ========================================================================= */

static void test_config_validation(void) {
    printf("Testing config validation...\n");

    legends_handle handle = NULL;
    legends_error_t err;

    /* Wrong struct_size should be rejected */
    legends_config_t bad_config = LEGENDS_CONFIG_INIT;
    bad_config.struct_size = sizeof(legends_config_t) - 1;  /* Wrong size */
    err = legends_create(&bad_config, &handle);
    assert(err == LEGENDS_ERR_INVALID_CONFIG);
    assert(handle == NULL);

    /* Wrong api_version should be rejected */
    bad_config = (legends_config_t)LEGENDS_CONFIG_INIT;
    bad_config.api_version = LEGENDS_API_VERSION + 1;  /* Wrong version */
    err = legends_create(&bad_config, &handle);
    assert(err == LEGENDS_ERR_VERSION_MISMATCH);
    assert(handle == NULL);

    /* Valid config should work */
    legends_config_t good_config = LEGENDS_CONFIG_INIT;
    err = legends_create(&good_config, &handle);
    assert(err == LEGENDS_OK);
    assert(handle != NULL);

    legends_destroy(handle);

    printf("  Config validation works correctly.\n");
}

/* =========================================================================
 * STUB FUNCTIONS RETURN NOT_SUPPORTED
 * ========================================================================= */

/* =========================================================================
 * PHASE 2: STEPPING API TESTS
 * ========================================================================= */

static void test_stepping_api(void) {
    printf("Testing stepping API (Phase 2)...\n");

    legends_handle handle = NULL;
    legends_error_t err;

    /* Create instance for testing */
    err = legends_create(NULL, &handle);
    assert(err == LEGENDS_OK);

    /* Step functions should work now */
    legends_step_result_t result;
    err = legends_step_ms(handle, 100, &result);
    assert(err == LEGENDS_OK);
    assert(result.cycles_executed > 0);
    assert(result.stop_reason == LEGENDS_STOP_COMPLETED);
    printf("    step_ms(100): cycles=%llu, time=%llu us\n",
           (unsigned long long)result.cycles_executed,
           (unsigned long long)result.emu_time_us);

    err = legends_step_cycles(handle, 10000, &result);
    assert(err == LEGENDS_OK);
    assert(result.cycles_executed == 10000);  /* Should be exact */
    printf("    step_cycles(10000): cycles=%llu\n",
           (unsigned long long)result.cycles_executed);

    /* Timing queries should work */
    uint64_t time_us;
    err = legends_get_emu_time(handle, &time_us);
    assert(err == LEGENDS_OK);
    assert(time_us > 0);  /* We've stepped, so time > 0 */
    printf("    emu_time: %llu us\n", (unsigned long long)time_us);

    uint64_t cycles;
    err = legends_get_total_cycles(handle, &cycles);
    assert(err == LEGENDS_OK);
    assert(cycles > 0);  /* We've stepped, so cycles > 0 */
    printf("    total_cycles: %llu\n", (unsigned long long)cycles);

    /* Reset should work and clear counters */
    err = legends_reset(handle);
    assert(err == LEGENDS_OK);

    err = legends_get_emu_time(handle, &time_us);
    assert(err == LEGENDS_OK);
    assert(time_us == 0);  /* Reset clears time */

    err = legends_get_total_cycles(handle, &cycles);
    assert(err == LEGENDS_OK);
    assert(cycles == 0);  /* Reset clears cycles */

    /* Get config should work */
    legends_config_t config;
    err = legends_get_config(handle, &config);
    assert(err == LEGENDS_OK);
    assert(config.memory_kb == 640);  /* Default */
    assert(config.deterministic == 1);  /* Default */

    /* Clean up */
    legends_destroy(handle);

    printf("  Stepping API tests passed.\n");
}

/* =========================================================================
 * PHASE 3: FRAME CAPTURE API TESTS
 * ========================================================================= */

static void test_frame_capture_api(void) {
    printf("Testing frame capture API (Phase 3)...\n");

    legends_handle handle = NULL;
    legends_error_t err;

    /* Create instance for testing */
    err = legends_create(NULL, &handle);
    assert(err == LEGENDS_OK);

    /* Text capture - query size */
    size_t text_count;
    legends_text_info_t info;
    err = legends_capture_text(handle, NULL, 0, &text_count, &info);
    assert(err == LEGENDS_OK);
    assert(text_count == 80 * 25);  /* Default 80x25 text mode */
    assert(info.columns == 80);
    assert(info.rows == 25);
    assert(info.cursor_visible == 1);
    printf("    capture_text query: %zu cells, %dx%d, cursor at (%d,%d)\n",
           text_count, info.columns, info.rows, info.cursor_x, info.cursor_y);

    /* Text capture - fill buffer */
    legends_text_cell_t* cells = (legends_text_cell_t*)malloc(
        text_count * sizeof(legends_text_cell_t));
    assert(cells != NULL);

    err = legends_capture_text(handle, cells, text_count, &text_count, NULL);
    assert(err == LEGENDS_OK);
    /* First character should be 'C' from "C:\>" prompt */
    assert(cells[0].character == 'C');
    assert(cells[0].attribute == 0x07);  /* Light gray on black */
    printf("    capture_text fill: first char='%c' attr=0x%02X\n",
           cells[0].character, cells[0].attribute);
    free(cells);

    /* RGB capture - query size */
    size_t rgb_size;
    uint16_t width, height;
    err = legends_capture_rgb(handle, NULL, 0, &rgb_size, &width, &height);
    assert(err == LEGENDS_OK);
    /* Text mode: 80*8 x 25*16 = 640x400 */
    assert(width == 640);
    assert(height == 400);
    assert(rgb_size == (size_t)width * height * 3);  /* RGB24 */
    printf("    capture_rgb query: %zu bytes, %dx%d\n", rgb_size, width, height);

    /* RGB capture - fill buffer */
    uint8_t* rgb_buffer = (uint8_t*)malloc(rgb_size);
    assert(rgb_buffer != NULL);

    err = legends_capture_rgb(handle, rgb_buffer, rgb_size, &rgb_size, NULL, NULL);
    assert(err == LEGENDS_OK);
    /* Buffer should have non-zero values (text content) */
    int has_nonzero = 0;
    for (size_t i = 0; i < rgb_size && !has_nonzero; ++i) {
        if (rgb_buffer[i] != 0) has_nonzero = 1;
    }
    assert(has_nonzero);
    printf("    capture_rgb fill: OK (has non-zero content)\n");
    free(rgb_buffer);

    /* Dirty tracking */
    int dirty;
    err = legends_is_frame_dirty(handle, &dirty);
    assert(err == LEGENDS_OK);
    assert(dirty == 0);  /* Should be clean after capture */
    printf("    is_frame_dirty: %d (0 after capture)\n", dirty);

    /* Reset sets dirty again */
    legends_reset(handle);
    err = legends_is_frame_dirty(handle, &dirty);
    assert(err == LEGENDS_OK);
    assert(dirty == 1);  /* Dirty after reset */
    printf("    is_frame_dirty: %d (1 after reset)\n", dirty);

    /* Cursor query */
    uint8_t cursor_x, cursor_y;
    int cursor_visible;
    err = legends_get_cursor(handle, &cursor_x, &cursor_y, &cursor_visible);
    assert(err == LEGENDS_OK);
    assert(cursor_x == 4);  /* After "C:\>" prompt */
    assert(cursor_y == 0);
    assert(cursor_visible == 1);
    printf("    get_cursor: (%d,%d) visible=%d\n", cursor_x, cursor_y, cursor_visible);

    /* Clean up */
    legends_destroy(handle);

    printf("  Frame capture API tests passed.\n");
}

/* =========================================================================
 * PHASE 4: INPUT INJECTION API TESTS
 * ========================================================================= */

static void test_input_api(void) {
    printf("Testing input API (Phase 4)...\n");

    legends_handle handle = NULL;
    legends_error_t err;

    /* Create instance for testing */
    err = legends_create(NULL, &handle);
    assert(err == LEGENDS_OK);

    /* Key event - press and release 'A' (scancode 0x1E) */
    err = legends_key_event(handle, 0x1E, 1);  /* Press */
    assert(err == LEGENDS_OK);
    err = legends_key_event(handle, 0x1E, 0);  /* Release */
    assert(err == LEGENDS_OK);
    printf("    key_event: OK (press/release 'A')\n");

    /* Extended key event - Right Arrow (E0 + 0x4D) */
    err = legends_key_event_ext(handle, 0x4D, 1);  /* Press */
    assert(err == LEGENDS_OK);
    err = legends_key_event_ext(handle, 0x4D, 0);  /* Release */
    assert(err == LEGENDS_OK);
    printf("    key_event_ext: OK (Right Arrow)\n");

    /* Text input */
    err = legends_text_input(handle, "Hello World");
    assert(err == LEGENDS_OK);
    printf("    text_input: OK (\"Hello World\")\n");

    /* Text input with shift chars */
    err = legends_text_input(handle, "ABC!@#");
    assert(err == LEGENDS_OK);
    printf("    text_input: OK (shift chars)\n");

    /* Text input with newline */
    err = legends_text_input(handle, "DIR\n");
    assert(err == LEGENDS_OK);
    printf("    text_input: OK (newline)\n");

    /* Text input null rejection */
    err = legends_text_input(handle, NULL);
    assert(err == LEGENDS_ERR_NULL_POINTER);
    printf("    text_input: OK (rejects NULL)\n");

    /* Mouse event */
    err = legends_mouse_event(handle, 10, 5, 0);  /* Move, no buttons */
    assert(err == LEGENDS_OK);
    printf("    mouse_event: OK (move 10,5)\n");

    /* Mouse with buttons */
    err = legends_mouse_event(handle, 0, 0, 1);  /* Left button */
    assert(err == LEGENDS_OK);
    err = legends_mouse_event(handle, 0, 0, 2);  /* Right button */
    assert(err == LEGENDS_OK);
    err = legends_mouse_event(handle, 0, 0, 4);  /* Middle button */
    assert(err == LEGENDS_OK);
    printf("    mouse_event: OK (buttons)\n");

    /* Mouse negative movement */
    err = legends_mouse_event(handle, -20, -15, 0);
    assert(err == LEGENDS_OK);
    printf("    mouse_event: OK (negative movement)\n");

    /* Verify input sets dirty flag */
    {
        /* Clear dirty flag first */
        size_t count;
        legends_capture_text(handle, NULL, 0, &count, NULL);
        legends_text_cell_t* cells = (legends_text_cell_t*)malloc(
            count * sizeof(legends_text_cell_t));
        legends_capture_text(handle, cells, count, &count, NULL);
        free(cells);

        int dirty;
        legends_is_frame_dirty(handle, &dirty);
        assert(dirty == 0);

        /* Key event should set dirty */
        legends_key_event(handle, 0x1E, 1);
        legends_is_frame_dirty(handle, &dirty);
        assert(dirty == 1);
        printf("    dirty flag: OK (set after key event)\n");
    }

    /* Reset clears input state */
    legends_reset(handle);
    err = legends_key_event(handle, 0x1E, 1);  /* Should still work */
    assert(err == LEGENDS_OK);
    printf("    reset: OK (input works after reset)\n");

    /* Clean up */
    legends_destroy(handle);

    printf("  Input API tests passed.\n");
}

/* =========================================================================
 * PHASE 5: SAVE-STATE DETERMINISM API TESTS
 * Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
 * ========================================================================= */

static void test_save_state_api(void) {
    printf("Testing save-state API (Phase 5)...\n");

    legends_handle handle = NULL;
    legends_error_t err;

    /* Create instance for testing */
    err = legends_create(NULL, &handle);
    assert(err == LEGENDS_OK);

    /* Save state - query size */
    size_t state_size;
    err = legends_save_state(handle, NULL, 0, &state_size);
    assert(err == LEGENDS_OK);
    assert(state_size > 0);
    printf("    save_state query: %zu bytes\n", state_size);

    /* Save state - fill buffer */
    uint8_t* buffer = (uint8_t*)malloc(state_size);
    assert(buffer != NULL);

    err = legends_save_state(handle, buffer, state_size, &state_size);
    assert(err == LEGENDS_OK);

    /* Check magic number (DBXS = 0x53584244) */
    uint32_t magic;
    memcpy(&magic, buffer, sizeof(magic));
    assert(magic == 0x53584244);
    printf("    save_state fill: OK (magic=0x%08X)\n", magic);

    /* Get state hash */
    uint8_t hash1[32];
    err = legends_get_state_hash(handle, hash1);
    assert(err == LEGENDS_OK);
    printf("    get_state_hash: OK\n");

    /* Step some cycles to change state */
    legends_step_cycles(handle, 10000, NULL);

    /* Get new hash - should be different */
    uint8_t hash2[32];
    err = legends_get_state_hash(handle, hash2);
    assert(err == LEGENDS_OK);
    assert(memcmp(hash1, hash2, 32) != 0);
    printf("    hash changes after step: OK\n");

    /* Load saved state */
    err = legends_load_state(handle, buffer, state_size);
    assert(err == LEGENDS_OK);
    printf("    load_state: OK\n");

    /* Hash should match original after load */
    uint8_t hash3[32];
    err = legends_get_state_hash(handle, hash3);
    assert(err == LEGENDS_OK);
    assert(memcmp(hash1, hash3, 32) == 0);
    printf("    hash matches after load: OK (TLA+ round-trip invariant)\n");

    /* Verify determinism */
    int is_det;
    err = legends_verify_determinism(handle, 5000, &is_det);
    assert(err == LEGENDS_OK);
    assert(is_det == 1);
    printf("    verify_determinism: OK (is_deterministic=%d)\n", is_det);

    /* Test error cases */
    uint8_t invalid_buffer[256];
    memset(invalid_buffer, 0, sizeof(invalid_buffer));
    err = legends_load_state(handle, invalid_buffer, sizeof(invalid_buffer));
    assert(err == LEGENDS_ERR_INVALID_STATE);
    printf("    load_state rejects invalid: OK\n");

    free(buffer);

    /* Clean up */
    legends_destroy(handle);

    printf("  Save-state API tests passed.\n");
}

/* =========================================================================
 * PHASE 6: LOG CALLBACK API TESTS
 * ========================================================================= */

/* Test context for log callback */
static int g_log_call_count = 0;
static int g_last_log_level = -1;
static char g_last_log_message[256] = {0};

static void test_log_callback(int level, const char* message, void* userdata) {
    (void)userdata;
    g_log_call_count++;
    g_last_log_level = level;
    if (message) {
        strncpy(g_last_log_message, message, sizeof(g_last_log_message) - 1);
        g_last_log_message[sizeof(g_last_log_message) - 1] = '\0';
    }
}

static void test_log_callback_api(void) {
    printf("Testing log callback API (Phase 6)...\n");

    legends_handle handle = NULL;
    legends_error_t err;

    /* Create instance for testing */
    err = legends_create(NULL, &handle);
    assert(err == LEGENDS_OK);

    /* Reset test state */
    g_log_call_count = 0;
    g_last_log_level = -1;
    g_last_log_message[0] = '\0';

    /* Set log callback */
    err = legends_set_log_callback(handle, test_log_callback, NULL);
    assert(err == LEGENDS_OK);
    printf("    set_log_callback: OK\n");

    /* Setting callback should have logged a debug message */
    assert(g_log_call_count > 0);
    assert(g_last_log_level == 3);  /* LOG_LEVEL_DEBUG = 3 */
    printf("    callback received debug message: OK\n");

    /* Clear callback */
    err = legends_set_log_callback(handle, NULL, NULL);
    assert(err == LEGENDS_OK);
    printf("    clear_log_callback: OK\n");

    /* Set callback again and trigger an error */
    g_log_call_count = 0;
    err = legends_set_log_callback(handle, test_log_callback, NULL);
    assert(err == LEGENDS_OK);
    g_log_call_count = 0;

    /* Try to create second instance (should fail and log error) */
    legends_handle handle2 = NULL;
    err = legends_create(NULL, &handle2);
    assert(err == LEGENDS_ERR_ALREADY_CREATED);

    /* Should have logged an error (level 0) */
    assert(g_log_call_count > 0);
    assert(g_last_log_level == 0);  /* LOG_LEVEL_ERROR = 0 */
    printf("    callback received error message: OK\n");

    /* Clean up */
    legends_destroy(handle);

    printf("  Log callback API tests passed.\n");
}

/* =========================================================================
 * ERROR MESSAGE API
 * ========================================================================= */

static void test_error_message_api(void) {
    printf("Testing error message API...\n");

    legends_error_t err;
    size_t length;

    /* Query size with null buffer */
    err = legends_get_last_error(NULL, NULL, 0, &length);
    assert(err == LEGENDS_OK);

    /* Trigger an error to have something to retrieve */
    legends_handle handle = NULL;
    legends_create(NULL, &handle);  /* Create one */
    legends_handle handle2 = NULL;
    legends_create(NULL, &handle2);  /* Second should fail */

    /* Now there should be an error message */
    err = legends_get_last_error(NULL, NULL, 0, &length);
    assert(err == LEGENDS_OK);
    assert(length > 1);  /* Should have message plus null terminator */

    /* Get the actual message */
    char buffer[256];
    err = legends_get_last_error(NULL, buffer, sizeof(buffer), &length);
    assert(err == LEGENDS_OK);
    assert(strlen(buffer) > 0);  /* Should have actual content */

    /* Buffer too small */
    char small_buffer[2];
    err = legends_get_last_error(NULL, small_buffer, sizeof(small_buffer), &length);
    assert(err == LEGENDS_ERR_BUFFER_TOO_SMALL);

    /* Clean up */
    legends_destroy(handle);

    printf("  Error message API works correctly.\n");
}

/* =========================================================================
 * MAIN
 * ========================================================================= */

int main(void) {
    printf("=== DOSBox-X Embed API - Pure C ABI Tests ===\n\n");

    /* ABI stability tests */
    test_abi_sizes();
    test_field_offsets();
    test_version_constants();
    test_error_codes();
    test_stop_reasons();
    test_config_initializer();

    /* API functionality tests */
    test_version_handshake();
    test_instance_lifecycle();
    test_null_handle_rejection();
    test_config_validation();
    test_stepping_api();
    test_frame_capture_api();
    test_input_api();
    test_save_state_api();
    test_log_callback_api();
    test_error_message_api();

    printf("\n=== All tests passed! ===\n");
    return 0;
}
