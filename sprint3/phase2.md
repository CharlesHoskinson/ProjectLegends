# Phase 2: Fix Cross-Module Path Includes

## Objective

Eliminate all 14 `../src/` includes from engine public headers by creating shim public headers that expose only the required types.

## Current Violations

| File | Line | Include | Violation |
|------|------|---------|-----------|
| engine/include/builtin.h | 3-14 | `../src/builtin/zip.h` | 12 includes to private source |
| engine/include/bios_disk.h | ~24 | `../src/dos/cdrom.h` | 1 include to private source |
| engine/include/render.h | ~28 | `../src/gui/render_scalers.h` | 1 include to private source |

**Total: 14 violations**

## Deliverables

### 2.1 Fix builtin.h (12 violations)

**Create:** `engine/include/dosbox/builtin_types.h`

```cpp
/**
 * @file builtin_types.h
 * @brief Public types for built-in file blobs
 *
 * This header defines the BuiltinFileBlob structure used to embed
 * binary resources (utilities, drivers) into the DOSBox library.
 */

#ifndef DOSBOX_BUILTIN_TYPES_H
#define DOSBOX_BUILTIN_TYPES_H

#include <cstdint>
#include <cstddef>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Binary blob embedded in the library
 */
struct BuiltinFileBlob {
    const char* filename;      /**< DOS filename (8.3 format) */
    const uint8_t* data;       /**< Pointer to embedded binary data */
    size_t size;               /**< Size in bytes */
};

#ifdef __cplusplus
}
#endif

#endif /* DOSBOX_BUILTIN_TYPES_H */
```

**Create:** `engine/src/builtin/builtin_data.cpp`

Move all blob data definitions from individual headers to this compilation unit:

```cpp
/**
 * @file builtin_data.cpp
 * @brief Compiled binary blob data for built-in utilities
 */

#include "dosbox/builtin_types.h"

// Include the binary data (private headers)
#include "zip.h"
#include "eval.h"
#include "cdplay.h"
#include "dosmid.h"
#include "mpxplay.h"
#include "ne2000bin.h"
#include "glide2x.h"
#include "emsmagic.h"
#include "shutdown.h"
#include "textutil.h"
#include "4DOS_img.h"
#include "patchutil.h"

// Blob definitions (previously in headers)
struct BuiltinFileBlob bfb_CWSDPMI_EXE = { "CWSDPMI.EXE", zip_data, sizeof(zip_data) };
// ... remaining blob definitions
```

**Modify:** `engine/include/builtin.h`

```cpp
#ifndef DOSBOX_BUILTIN_H
#define DOSBOX_BUILTIN_H

#include "dos_inc.h"
#include "dosbox/builtin_types.h"  // Public types only

// External declarations - data lives in builtin_data.cpp
extern struct BuiltinFileBlob bfb_CWSDPMI_EXE;
extern struct BuiltinFileBlob bfb_DOS4GW_EXE;
extern struct BuiltinFileBlob bfb_DOS32A_EXE;
extern struct BuiltinFileBlob bfb_HEXMEM16_EXE;
extern struct BuiltinFileBlob bfb_HEXMEM32_EXE;
extern struct BuiltinFileBlob bfb_DEBUG_EXE;
extern struct BuiltinFileBlob bfb_DOSIDLE_EXE;
extern struct BuiltinFileBlob bfb_EVAL_EXE;
extern struct BuiltinFileBlob bfb_CDPLAY_EXE;
extern struct BuiltinFileBlob bfb_DOSMID_EXE;
extern struct BuiltinFileBlob bfb_MPXPLAY_EXE;
extern struct BuiltinFileBlob bfb_NE2000_COM;

#endif /* DOSBOX_BUILTIN_H */
```

### 2.2 Fix bios_disk.h (1 violation)

**Create:** `engine/include/dosbox/cdrom_interface.h`

```cpp
/**
 * @file cdrom_interface.h
 * @brief Public CDROM interface for BIOS disk access
 */

#ifndef DOSBOX_CDROM_INTERFACE_H
#define DOSBOX_CDROM_INTERFACE_H

#include <cstdint>

#ifdef __cplusplus

/**
 * @brief MSF (Minutes:Seconds:Frames) time format
 */
struct TMSF {
    uint8_t min;
    uint8_t sec;
    uint8_t fr;
};

/**
 * @brief Audio channel control structure
 */
struct TCtrl {
    uint8_t out[4];
    uint8_t vol[4];
};

/**
 * @brief Abstract CDROM interface
 *
 * Implementations provide access to physical or image-based CD drives.
 */
class CDROM_Interface {
public:
    virtual ~CDROM_Interface() = default;

    virtual bool SetDevice(const char* path, int forceCD) = 0;
    virtual bool GetUPC(unsigned char& attr, char* upc) = 0;
    virtual bool GetAudioTracks(uint8_t& stTrack, uint8_t& end, TMSF& leadOut) = 0;
    virtual bool GetAudioTrackInfo(uint8_t track, TMSF& start, unsigned char& attr) = 0;
    virtual bool GetAudioSub(unsigned char& attr, unsigned char& track,
                             unsigned char& index, TMSF& relPos, TMSF& absPos) = 0;
    virtual bool GetAudioStatus(bool& playing, bool& pause) = 0;
    virtual bool GetMediaTrayStatus(bool& mediaPresent, bool& mediaChanged, bool& trayOpen) = 0;
    virtual bool PlayAudioSector(unsigned long start, unsigned long len) = 0;
    virtual bool PauseAudio(bool resume) = 0;
    virtual bool StopAudio() = 0;
    virtual void ChannelControl(TCtrl ctrl) = 0;
    virtual bool ReadSectors(void* buffer, bool raw, unsigned long sector, unsigned long num) = 0;
    virtual bool ReadSectorsHost(void* buffer, bool raw, unsigned long sector, unsigned long num) = 0;
    virtual bool LoadUnloadMedia(bool unload) = 0;
};

/**
 * @brief Get CDROM interface for a drive letter
 * @param drive_letter DOS drive letter (0=A, 2=C, etc.)
 * @param cdrom Output pointer to CDROM interface
 * @return true if drive is a CDROM, false otherwise
 */
bool GetMSCDEXDrive(unsigned char drive_letter, CDROM_Interface** cdrom);

#endif /* __cplusplus */

#endif /* DOSBOX_CDROM_INTERFACE_H */
```

**Modify:** `engine/include/bios_disk.h`

Replace:
```cpp
#include "../src/dos/cdrom.h"
```

With:
```cpp
#include "dosbox/cdrom_interface.h"
```

### 2.3 Fix render.h (1 violation)

**Create:** `engine/include/dosbox/render_types.h`

```cpp
/**
 * @file render_types.h
 * @brief Public render/scaler types
 */

#ifndef DOSBOX_RENDER_TYPES_H
#define DOSBOX_RENDER_TYPES_H

#include <cstdint>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Scaler color mode
 */
typedef enum {
    scalerMode8,
    scalerMode15,
    scalerMode16,
    scalerMode32
} scalerMode_t;

/**
 * @brief Scaler operation type
 */
typedef enum scalerOperation {
    scalerOpNormal,
    scalerOpAdvMame,
    scalerOpAdvInterp,
    scalerOpHQ,
    scalerOpSuperSaI,
    scalerOpSuperEagle,
    scalerOp2xSaI,
    scalerOpTV,
    scalerOpRGB,
    scalerOpScan,
    scalerOpGray,
    scalerLast
} scalerOperation_t;

/**
 * @brief Simple line scaler function pointer
 */
typedef void (*ScalerLineHandler_t)(const void* src);

/**
 * @brief Complex block scaler function pointer
 */
typedef void (*ScalerComplexHandler_t)(void);

#ifdef __cplusplus
}
#endif

#endif /* DOSBOX_RENDER_TYPES_H */
```

**Modify:** `engine/include/render.h`

Replace:
```cpp
#include "../src/gui/render_scalers.h"
```

With:
```cpp
#include "dosbox/render_types.h"
```

## Implementation Steps

| Step | Action | Files |
|------|--------|-------|
| 2.1.1 | Create builtin_types.h | engine/include/dosbox/builtin_types.h |
| 2.1.2 | Create builtin_data.cpp | engine/src/builtin/builtin_data.cpp |
| 2.1.3 | Update builtin.h to use extern declarations | engine/include/builtin.h |
| 2.1.4 | Add builtin_data.cpp to engine CMakeLists.txt | engine/CMakeLists.txt |
| 2.2.1 | Create cdrom_interface.h | engine/include/dosbox/cdrom_interface.h |
| 2.2.2 | Update bios_disk.h | engine/include/bios_disk.h |
| 2.3.1 | Create render_types.h | engine/include/dosbox/render_types.h |
| 2.3.2 | Update render.h | engine/include/render.h |
| 2.4.1 | Full rebuild to verify | Build all targets |

## Test Plan

### Unit Tests

No new unit tests required - existing tests validate functionality.

### Integration Tests

```cpp
// test_phase2_includes.cpp
// Verify public headers are self-contained

#include "dosbox/builtin_types.h"
#include "dosbox/cdrom_interface.h"
#include "dosbox/render_types.h"

// If this compiles, the headers are self-contained
static_assert(sizeof(BuiltinFileBlob) > 0, "BuiltinFileBlob defined");
static_assert(sizeof(TMSF) == 3, "TMSF is packed");
static_assert(scalerMode32 == 3, "Scaler modes defined");
```

### Manual Verification

| Test | Command | Expected Result |
|------|---------|-----------------|
| No ../src/ in public headers | `grep -r '../src/' engine/include/` | No output (empty) |
| Headers self-contained | Compile test_phase2_includes.cpp | Compiles without errors |
| Full build passes | `cmake --build build` | 0 errors, 0 new warnings |
| Existing tests pass | `ctest --test-dir build` | All tests pass |

### Acceptance Criteria

- [ ] `grep -r '../src/' engine/include/` returns empty
- [ ] All 3 new headers created in engine/include/dosbox/
- [ ] builtin_data.cpp compiles and links
- [ ] Full build succeeds with no new warnings
- [ ] All existing tests pass
- [ ] No functional regression in CDROM or rendering

## Rollback Plan

If issues arise:
1. Restore original builtin.h, bios_disk.h, render.h from git
2. Remove new headers: builtin_types.h, cdrom_interface.h, render_types.h
3. Remove builtin_data.cpp
4. Revert engine/CMakeLists.txt changes

**Git commands:**
```bash
git checkout HEAD -- engine/include/builtin.h
git checkout HEAD -- engine/include/bios_disk.h
git checkout HEAD -- engine/include/render.h
git rm engine/include/dosbox/builtin_types.h
git rm engine/include/dosbox/cdrom_interface.h
git rm engine/include/dosbox/render_types.h
git rm engine/src/builtin/builtin_data.cpp
```
