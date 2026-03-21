# Plan 2: Test Infrastructure

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Create shared test fixtures, split monolith test files, and fix build system issues to unblock rapid test development and reduce ~1,190 lines of boilerplate.

**Architecture:** Create 3 shared header files in `tests/unit/test_utils/`, 1 in `tests/integration/test_utils/`, split the largest test file, and create an intermediate library target.

**Tech Stack:** C++23, GoogleTest v1.14.0, CMake

---

### Task 1: Create `tests/unit/test_utils/temp_file_fixture.h`

**Audit ref:** Agent 5 — ~155 lines duplicated across 4+ config test files

**Files:**
- Create: `tests/unit/test_utils/temp_file_fixture.h`
- Modify: `tests/unit/test_config_parser.cpp` (migrate first)
- Modify: `tests/unit/test_glide_config.cpp`
- Modify: `tests/unit/test_ipx_config.cpp`
- Modify: `tests/unit/test_pc98_config.cpp`

- [ ] **Step 1: Create the shared fixture header**

```cpp
#pragma once
#include <gtest/gtest.h>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

namespace legends::test {

class TempFileFixture : public ::testing::Test {
protected:
    std::string writeTempFile(const std::string& prefix, const std::string& content) {
        auto path = std::filesystem::temp_directory_path() /
            (prefix + std::to_string(counter_++) + ".conf");
        std::ofstream ofs(path);
        ofs << content;
        temp_files_.push_back(path.string());
        return path.string();
    }

    void TearDown() override {
        for (const auto& f : temp_files_) {
            std::filesystem::remove(f);
        }
    }

private:
    std::vector<std::string> temp_files_;
    static inline int counter_ = 0;
};

class ScopedTempDir {
public:
    explicit ScopedTempDir(const std::string& name)
        : path_(std::filesystem::temp_directory_path() / name) {
        std::filesystem::create_directories(path_);
    }
    ~ScopedTempDir() {
        std::error_code ec;
        std::filesystem::remove_all(path_, ec);
    }
    ScopedTempDir(const ScopedTempDir&) = delete;
    ScopedTempDir& operator=(const ScopedTempDir&) = delete;
    const std::filesystem::path& path() const { return path_; }
    std::string string() const { return path_.string(); }
private:
    std::filesystem::path path_;
};

}  // namespace legends::test
```

- [ ] **Step 2: Migrate `test_config_parser.cpp` to use TempFileFixture**

Replace inline `writeTempFile` method and `TearDown` with inheritance from `legends::test::TempFileFixture`.

- [ ] **Step 3: Run tests to verify migration**

Run: `ctest --test-dir build/dev -R test_config_parser -V`

- [ ] **Step 4: Migrate remaining 3 config test files**

- [ ] **Step 5: Run all config tests**

- [ ] **Step 6: Commit**

```bash
git add tests/unit/test_utils/temp_file_fixture.h tests/unit/test_config_parser.cpp tests/unit/test_glide_config.cpp tests/unit/test_ipx_config.cpp tests/unit/test_pc98_config.cpp
git commit -m "refactor: extract shared TempFileFixture and ScopedTempDir for test cleanup"
```

---

### Task 2: Create `tests/unit/test_utils/pal_headless_fixture.h`

**Audit ref:** Agent 5 — ~60 lines duplicated across 7+ PAL test files

**Files:**
- Create: `tests/unit/test_utils/pal_headless_fixture.h`
- Modify: `tests/unit/test_pal_window.cpp`, `test_pal_context.cpp`, `test_pal_audio_sink.cpp`, `test_pal_input_source.cpp`, `test_pal_host_clock.cpp`, `test_pal_platform.cpp`

- [ ] **Step 1: Create the shared PAL fixture header**

```cpp
#pragma once
#include <gtest/gtest.h>
#include <pal/platform.h>

namespace legends::test {

class PalHeadlessFixture : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
    }
    void TearDown() override {
        pal::Platform::shutdown();
    }
};

}  // namespace legends::test
```

- [ ] **Step 2: Migrate PAL test files one at a time, running tests after each**

- [ ] **Step 3: Run full PAL test suite**

Run: `ctest --test-dir build/dev -R test_pal -V`

- [ ] **Step 4: Commit**

---

### Task 3: Create `tests/unit/test_utils/ipc_test_helpers.h`

**Audit ref:** Agent 5 — ~65 lines duplicated across 6 IPC test files

**Files:**
- Create: `tests/unit/test_utils/ipc_test_helpers.h`
- Modify: 6 IPC test files

- [ ] **Step 1: Create the shared IPC helper header**

Include: `ipc_test_unique_name()`, `SKIP_IF_NO_SHM()` macro, spawn config helpers.

- [ ] **Step 2: Migrate IPC test files**

- [ ] **Step 3: Run IPC tests**

- [ ] **Step 4: Commit**

---

### Task 4: Create `tests/integration/test_utils/integration_fixture.h`

**Audit ref:** Agent 6 — 15+ integration test files share identical SetUp/TearDown boilerplate

**Files:**
- Create: `tests/integration/test_utils/integration_fixture.h`
- Modify: At least 5 integration test files as initial migration

- [ ] **Step 1: Create base fixtures**

`LegendsIntegrationTest`, `LegendsConfiguredTest` (deterministic=1), `LegendsWarmupTest` (N frames), `PalOnlyTest` (no engine).

Include shared helpers: `save_state()`, `get_hash()`, `capture_screen_chars()`, `stepFrames()`.

- [ ] **Step 2: Migrate `test_workflow_basic.cpp` first (lowest risk)**

- [ ] **Step 3: Migrate 4 more integration files**

- [ ] **Step 4: Run integration suite**

- [ ] **Step 5: Commit**

---

### Task 5: Split `test_legends_embed.cpp`

**Audit ref:** Agent 11 — 2,652 lines, 165 tests, 12 fixture classes

**Files:**
- Modify: `tests/unit/test_legends_embed.cpp` (extract from)
- Create: `tests/unit/test_legends_embed_lifecycle.cpp`
- Create: `tests/unit/test_legends_embed_capture.cpp`
- Create: `tests/unit/test_legends_embed_input.cpp`
- Create: `tests/unit/test_legends_embed_savestate.cpp`
- Create: `tests/unit/test_legends_embed_security.cpp`
- Modify: `CMakeLists.txt` (add new source files)

- [ ] **Step 1: Extract `LegendsInstanceFixture` base class**

- [ ] **Step 2: Split by fixture class grouping**

- [ ] **Step 3: Update CMakeLists.txt**

- [ ] **Step 4: Run all embed tests**

- [ ] **Step 5: Commit**

---

### Task 6: Create `legends_app` Library Target

**Audit ref:** Agent 11 — production sources compiled into test target, doubling compile time

**Files:**
- Modify: `CMakeLists.txt`

- [ ] **Step 1: Extract `src/app/*.cpp` into a STATIC library target `legends_app`**

```cmake
add_library(legends_app STATIC ${APP_SOURCES})
legends_set_strict_cxx_standard(legends_app)
target_link_libraries(legends_app PUBLIC legends_core legends_pal)
```

- [ ] **Step 2: Link `project_legends` executable against `legends_app`**

- [ ] **Step 3: Link `legends_unit_tests` against `legends_app` instead of recompiling sources**

- [ ] **Step 4: Build both targets to verify**

- [ ] **Step 5: Run full test suite**

- [ ] **Step 6: Commit**

---

### Task 7: Add Missing fuzz_config_parser CMake Target

**Audit ref:** Agent 6 — source exists but no CMake target, CI references it

**Files:**
- Modify: `tests/fuzz/CMakeLists.txt`

- [ ] **Step 1: Add target analogous to other fuzz targets**

- [ ] **Step 2: Build with `-DENABLE_FUZZING=ON`**

- [ ] **Step 3: Commit**

---

### Task 8: Add TIMEOUT to Unit Test Discovery

**Audit ref:** Agent 10 — no TIMEOUT on `gtest_discover_tests()` for unit tests

**Files:**
- Modify: `CMakeLists.txt`

- [ ] **Step 1: Add `PROPERTIES TIMEOUT 30` to `gtest_discover_tests(legends_unit_tests)`**

- [ ] **Step 2: Verify CTest respects the timeout**

- [ ] **Step 3: Commit**
