# Plan 3: Security & Correctness

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix all 7 security requirements overstated as "Done" in the ROADMAP, plus critical QA gaps that block Release A.

**Architecture:** Each task addresses one REQ-SEC or REQ-QA finding. Independent, no cross-dependencies.

**Tech Stack:** C++23, GoogleTest

---

### Task 1: Enforce Image Validation Depth Limit (REQ-SEC-016)

**Audit ref:** Agent 2 — `kMaxDirectoryDepth=32` declared but never checked

**Files:**
- Modify: `src/app/image_validator.cpp`
- Test: `tests/unit/test_mount_manager.cpp`

- [ ] **Step 1: Write a test with deeply nested directory structure assertion**
- [ ] **Step 2: Implement depth checking in FAT directory traversal**
- [ ] **Step 3: Run tests**
- [ ] **Step 4: Commit**

---

### Task 2: Add AI Response Sanitization (REQ-SEC-008)

**Audit ref:** Agent 2 — no sanitization of AI responses before display

**Files:**
- Modify: `src/app/ai_panel.cpp`
- Test: `tests/unit/test_ai_panel.cpp`

- [ ] **Step 1: Write test that HTML/URI content is stripped**
- [ ] **Step 2: Add `sanitizeResponse()` that strips `<script>`, `<img>`, `file://`, `javascript:` patterns**
- [ ] **Step 3: Call sanitizeResponse in addResponse()**
- [ ] **Step 4: Run tests**
- [ ] **Step 5: Commit**

---

### Task 3: Detect Raw API Keys in Config (REQ-SEC-006)

**Audit ref:** Agent 2 — no detection/rejection of raw `api_key=sk-...` in config

**Files:**
- Modify: `src/app/ai_config.cpp`
- Test: `tests/unit/test_ai_config.cpp`

- [ ] **Step 1: Write test that raw key pattern triggers warning**
- [ ] **Step 2: Add pattern check in loadFrom() for `sk-` prefix**
- [ ] **Step 3: Emit warning to stderr and refuse to store raw key**
- [ ] **Step 4: Run tests**
- [ ] **Step 5: Commit**

---

### Task 4: Add Suspend/Resume Frame Cap (REQ-QA-001)

**Audit ref:** Agent 4 — no elapsed-time cap, engine could attempt massive step intervals after system resume

**Files:**
- Modify: `src/app/application.cpp`

- [ ] **Step 1: Add `constexpr uint64_t kMaxFrameUs = 100'000;` (100ms cap)**
- [ ] **Step 2: Clamp elapsed time before computing step_ms**
- [ ] **Step 3: Run application tests**
- [ ] **Step 4: Commit**

---

### Task 5: Check step_result After legends_step_ms (REQ-QA-005)

**Audit ref:** Agent 4 — step_result captured but never checked, errors silently ignored

**Files:**
- Modify: `src/app/application.cpp`

- [ ] **Step 1: After `legends_step_ms()`, check result for error**
- [ ] **Step 2: On error, log via file_logger, suppress capture/audio for that frame**
- [ ] **Step 3: Run tests**
- [ ] **Step 4: Commit**

---

### Task 6: Add Windows DPI-Aware Manifest (REQ-QA-015)

**Audit ref:** Agent 4 — missing entirely, Windows users on high-DPI get bitmap-scaled output

**Files:**
- Create: `src/app/project_legends.manifest`
- Modify: `CMakeLists.txt` (add manifest to executable)

- [ ] **Step 1: Create the application manifest with dpiAware/dpiAwareness settings**

```xml
<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<assembly xmlns="urn:schemas-microsoft-com:asm.v1" manifestVersion="1.0"
          xmlns:asmv3="urn:schemas-microsoft-com:asm.v3">
  <asmv3:application>
    <asmv3:windowsSettings>
      <dpiAware xmlns="http://schemas.microsoft.com/SMI/2005/WindowsSettings">true/pm</dpiAware>
      <dpiAwareness xmlns="http://schemas.microsoft.com/SMI/2016/WindowsSettings">PerMonitorV2</dpiAwareness>
    </asmv3:windowsSettings>
  </asmv3:application>
</assembly>
```

- [ ] **Step 2: Add manifest to CMake Windows executable**

```cmake
if(WIN32)
    target_sources(project_legends PRIVATE src/app/project_legends.manifest)
endif()
```

- [ ] **Step 3: Build on Windows to verify manifest is embedded**
- [ ] **Step 4: Commit**

---

### Task 7: Add Dimension Change Debouncing (REQ-QA-006)

**Audit ref:** Agent 4 — resolution changes apply immediately with no debounce

**Files:**
- Modify: `src/app/application.cpp`

- [ ] **Step 1: Add frame counter for resolution stability**

Track last 3 frames' dimensions. Only recreate context when dimensions are stable for 3 consecutive frames.

- [ ] **Step 2: Run application tests**
- [ ] **Step 3: Commit**

---

### Task 8: Fix file_logger UTF-8 to Wstring Conversion (Windows)

**Audit ref:** Agent 3 (C++23), Agent 7 — `std::wstring(begin, end)` only works for ASCII

**Files:**
- Modify: `src/app/file_logger.cpp`

- [ ] **Step 1: Replace `std::wstring(filepath.begin(), filepath.end())` with `MultiByteToWideChar`**

```cpp
int len = MultiByteToWideChar(CP_UTF8, 0, filepath.c_str(), -1, nullptr, 0);
std::wstring wpath(len - 1, L'\0');
MultiByteToWideChar(CP_UTF8, 0, filepath.c_str(), -1, wpath.data(), len);
```

- [ ] **Step 2: Run file logger tests**
- [ ] **Step 3: Commit**

---

### Task 9: Stub Functions Should Return NOT_SUPPORTED

**Audit ref:** Agent 8 — `legends_start_video_capture`, `legends_joystick_event`, `legends_set_ttf_font` return OK

**Files:**
- Modify: `src/legends/legends_embed_api.cpp`

- [ ] **Step 1: Change return values from LEGENDS_OK to LEGENDS_ERR_NOT_SUPPORTED**

For all stub functions that accept input and silently discard it.

- [ ] **Step 2: Update any tests that expect OK from these stubs**
- [ ] **Step 3: Commit**
