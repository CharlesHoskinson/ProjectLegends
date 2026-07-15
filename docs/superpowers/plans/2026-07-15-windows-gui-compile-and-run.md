# Plan: Compile and run Project Legends GUI on Windows

**Goal:** A developer (or CI) can produce `project_legends.exe` on Windows, launch a window via SDL3, and interact with the emulator shell.

**Non-goals (this plan):** Full Phase-3 feature completeness (IPX/Glide/PC-98 polish), FluidSynth MIDI, shipping an installer, fixing every open product issue.

**Success criteria:**

1. Configure + build succeeds on MSVC (VS 2022/2026) Release.
2. `build/Release/project_legends.exe` (or Ninja equivalent) exists and starts without missing DLL errors.
3. An SDL window appears; basic keyboard input reaches the app loop (quit with Esc/window close).
4. Optional: mount a test image / boot path documented if the shell supports it without extra secrets.

---

## Current state (facts from tree + CI)

| Fact | Detail |
|------|--------|
| GUI target | `project_legends` when `PAL_BACKEND_SDL3=ON` (preferred) or `PAL_BACKEND_SDL2=ON` |
| Entry | `src/main.cpp` → `legends::Application` |
| CI default Windows | **Headless only** (`LEGENDS_HEADLESS=ON`, no `PAL_BACKEND_SDL3`) |
| Optional CI | `Optional Windows SDL3 (MSVC)` builds with `PAL_BACKEND_SDL3=ON` but only **on schedule / dispatch / tags** — verifies exe exists, does not GUI-smoke |
| SDL | Not under `external/SDL3`; CMake **FetchContent** from `LEGENDS_DEP_SDL3_TAG` (`release-3.2.8`) when SDL3 backend on |
| Blocker on tip `d5f0062` | Windows **MSVC /WX + gsl-lite C4875** can still fail; INTERFACE `/wd4875` on `gsl-lite` may not apply to all consumers |
| Last known full green Windows headless | `621a099` / `54d85be` era — re-verify after C4875 fix |

---

## Architecture of the GUI product

```text
project_legends.exe
  └─ Application / RuntimeHost (app shell: menus, config, capture, …)
       └─ legends_app + legends_pal (SDL3 backend)
            └─ legends_core → aibox_core (engine)
                 └─ SDL3.dll (window, input, audio)
```

Monolithic default (`LEGENDS_USE_IPC=OFF`): single process.  
IPC mode (`LEGENDS_USE_IPC=ON`): shell + `legends_engine_host.exe` — **phase 2** of this plan, not required for first GUI.

---

## Phased plan

### Phase 0 — Unblock MSVC build (hard gate)

**Why:** GUI cannot ship if `Windows (MSVC)` fails before link.

| Step | Action | Done when |
|------|--------|-----------|
| 0.1 | Fix C4875 under `/WX` so **all** targets that include `gsl-lite.hpp` compile | Windows CI job builds Release |
| 0.2 | **`legends_link_gsl(target)`** applies consumer **PRIVATE** `/wd4875` on MSVC (INTERFACE-only on gsl-lite failed in CI F019) | No C2220 from gsl-lite.hpp |
| 0.3 | Keep silence **out of** non-gsl TUs (not on global `legends_compile_options`) | Audit-friendly scoping |
| 0.4 | CI green: `Windows (MSVC)` headless job success on a tip SHA | Job URL recorded |
| 0.5 | Keep **#44** open until upstream pin needs no `/wd4875` | Issue state honest |
| 0.6 | **Implemented:** `legends_link_gsl` on aibox_core, legends_*, unit tests, fuzz_config_parser | Push + CI |

**Recommended fix order for 0.1–0.2:**

1. After `FetchContent_MakeAvailable(gsl-lite)`, set **SYSTEM** includes for gsl-lite if CMake version supports it, **and**
2. Attach `/wd4875` to **every consumer** via a small CMake helper `legends_link_gsl(target)` that does `target_link_libraries(... gsl::gsl-lite-v1)` + `target_compile_options(... PRIVATE /wd4875)` on MSVC — including `aibox_core` (engine), `legends_core`, `legends_app`, `project_legends`, unit tests.

Do **not** rely only on INTERFACE options on the `gsl-lite` target without verifying MSVC actually inherits them into `.obj` compiles (CI already showed attachment message but C4875 still fired).

---

### Phase 1 — Local Windows GUI build recipe (developer MVP)

**Prerequisites**

- Visual Studio 2022 or 2026 with “Desktop development with C++”
- CMake ≥ 3.28, Ninja **or** VS generator
- Git, network (first configure fetches SDL3 + gsl-lite + gtest if tests on)
- Optional: Ninja + `Developer PowerShell for VS`

**Configure (SDL3 GUI — preferred)**

```powershell
cd C:\ProjectLegends
cmake -B build-win-gui -G "Visual Studio 17 2022" -A x64 `
  -DPAL_BACKEND_SDL3=ON `
  -DPAL_BACKEND_HEADLESS=ON `
  -DLEGENDS_HEADLESS=OFF `
  -DLEGENDS_BUILD_TESTS=OFF `
  -DLEGENDS_ENABLE_FLUIDSYNTH=OFF `
  -DLEGENDS_ENABLE_MT32=OFF `
  -DLEGENDS_ENABLE_AI=OFF
```

Notes:

- `PAL_BACKEND_SDL3=ON` creates `project_legends`.
- Keep `PAL_BACKEND_HEADLESS=ON` so library/tests paths still compile if needed; shell uses SDL3.
- `LEGENDS_HEADLESS=OFF` so app is not forced into no-GUI mode (align with how `Application` checks defines — verify during first build if window fails to create).
- Tests OFF for first GUI iteration (faster); turn ON later.

**Build**

```powershell
cmake --build build-win-gui --config Release --target project_legends
```

**Expected outputs**

- `build-win-gui\Release\project_legends.exe`
- `SDL3.dll` copied next to exe (POST_BUILD if `SDL3-shared` target exists)

**Run**

```powershell
cd build-win-gui\Release
.\project_legends.exe
# or with help if CLI exists:
.\project_legends.exe --help
```

**Acceptance**

- Process starts; no “SDL3.dll was not found”
- Window opens (title/size per `Application`)
- Close window or quit key exits 0

**If build fails — triage order**

1. C4875/C2220 → Phase 0 incomplete  
2. SDL3 FetchContent fail → network/proxy; retry; check `cmake/dependencies.cmake` tag  
3. Link errors on OpenGL/glad → ensure Windows SDK + opengl32 (add if missing)  
4. Duplicate `project_legends` if both SDL2 and SDL3 ON → enable only one  

---

### Phase 2 — Make GUI build first-class in repo tooling

| Step | Action |
|------|--------|
| 2.1 | Add **CMake preset** `windows-gui` (VS generator + SDL3 flags above) |
| 2.2 | Add **CMake preset** `windows-gui-ninja` optional |
| 2.3 | Document recipe in `README.md` under “Windows GUI” |
| 2.4 | Add CI job **Windows GUI (MSVC)** on PR (or at least `workflow_dispatch` + nightly): configure SDL3, build `project_legends`, assert exe path, **cache** `_deps/sdl3-*` like optional job |
| 2.5 | Optional smoke: run exe with `--help` or a headless-quit flag if one exists; full GUI smoke on self-hosted later |

Promote optional job:

```yaml
# Today: schedule | workflow_dispatch | tags only
# Target: also pull_request (or path-filtered when app/PAL changes)
```

---

### Phase 3 — Runtime usability (first “real” session)

| Step | Action | Notes |
|------|--------|-------|
| 3.1 | Map CLI/config entry points (`cli_parser`, `config_parser`, default.conf paths) | How to open a disk/image |
| 3.2 | Document minimal “boot” path: mount host dir or floppy/ISO if supported | Use existing `legends_mount_drive` / mount_manager |
| 3.3 | Keyboard: verify scancode path in SDL3 backend | `scancode_map`, input_mapper |
| 3.4 | Audio: optional; may be silent initially | Buffer/SDL audio |
| 3.5 | Crash/error: ensure `crash_breadcrumb` / logger don’t block GUI | Mutex path already fixed |
| 3.6 | Capture a short screenshot or log of first successful run | Evidence for “runs” |

---

### Phase 4 — Hardening (after first green GUI)

| Step | Action |
|------|--------|
| 4.1 | Debug vs Release both build |
| 4.2 | `LEGENDS_USE_IPC=ON` GUI (proxy + `legends_engine_host`) if isolation required |
| 4.3 | Portable mode / relative asset paths (`portable_mode`) |
| 4.4 | Packaging: zip exe + SDL3.dll + README snippet (not full installer) |
| 4.5 | Re-enable optional features only as needed (MT32, AI, FluidSynth external) |

---

## Risk register

| Risk | Impact | Mitigation |
|------|--------|------------|
| C4875 still fires on some target | Windows red | Consumer-side `/wd4875` helper; verify aibox_core + legends_app + project_legends |
| SDL3 FetchContent slow/flaky | First build fails | Cache `_deps`; document offline vendoring later |
| `LEGENDS_HEADLESS=ON` with SDL3 | Window never shows | Explicit `OFF` for GUI preset; code audit Application for define |
| Missing OpenGL / GPU driver | Black window / crash | Require basic WDDM drivers; soft-fail message |
| Expecting full DOSBox feature parity | “Doesn’t run my game” | Scope MVP as **shell launches + input**; content is follow-up |
| Dual SDL2/SDL3 | CMake FATAL | Preset enables only SDL3 |

---

## Suggested implementation order (for the agent)

1. **Phase 0** — Fix Windows MSVC C4875 so default CI Windows is green again.  
2. **Phase 1** — Document + run local GUI recipe on a real Windows box (or CI artifact job).  
3. **Phase 2.1–2.4** — Preset + mandatory-or-optional CI job for `project_legends.exe`.  
4. **Phase 3** — Minimal boot/mount docs + first interactive session notes.  
5. **Phase 4** — Packaging and IPC only if needed.

---

## Verification checklist (end-to-end)

- [ ] `Windows (MSVC)` headless CI green on tip  
- [ ] `cmake` GUI configure succeeds with `PAL_BACKEND_SDL3=ON`  
- [ ] `project_legends.exe` links and sits next to `SDL3.dll`  
- [ ] Manual launch: window visible, quit clean  
- [ ] CI or script asserts exe exists (Optional Windows SDL3 job or new PR job)  
- [ ] README “Windows GUI” section matches reality  
- [ ] #44 status matches actual C4875 strategy  

---

## Effort estimate (rough)

| Phase | Effort |
|-------|--------|
| 0 Unblock MSVC | 0.5–1 day |
| 1 Local GUI recipe + first run | 0.5–1 day |
| 2 Presets + CI | 0.5 day |
| 3 Usable session (mount/boot docs) | 1–2 days |
| 4 Packaging / IPC | 1–3 days |

---

## Immediate next command block (after Phase 0)

```powershell
cd C:\ProjectLegends
cmake -B build-win-gui -G "Visual Studio 17 2022" -A x64 `
  -DPAL_BACKEND_SDL3=ON `
  -DPAL_BACKEND_HEADLESS=ON `
  -DLEGENDS_HEADLESS=OFF `
  -DLEGENDS_BUILD_TESTS=OFF
cmake --build build-win-gui --config Release --target project_legends
explorer build-win-gui\Release
.\build-win-gui\Release\project_legends.exe
```

---

## Related docs

- README Quick Start / API  
- `cmake/dependencies.cmake` (SDL3 pin)  
- Optional CI: `.github/workflows/ci.yml` → `Optional Windows SDL3 (MSVC)`  
- Issue **#44** (C4875 / `/wd4875`)  
- Residual tracker: `docs/ci/r1-residual-closeout.md`  
