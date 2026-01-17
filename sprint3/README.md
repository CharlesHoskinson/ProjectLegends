# Sprint 3: Module Graph Implementation

## Overview

Transform the projectlegends codebase into a verifiable static library DAG with clean module boundaries, CI enforcement, and measurable rebuild improvements.

## Key Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| aibox/ ownership | Engine module | LLM/vision utilities are engine features |
| Header fix strategy | Shim headers | Preserves existing layout, minimal disruption |
| CI enforcement | Strict from day 1 | All violations must be fixed before merge |

## Phases

| Phase | Title | Deliverables | Dependencies |
|-------|-------|--------------|--------------|
| [Phase 1](phase1.md) | Define Module Boundaries | ModuleManifest.cmake, docs | None |
| [Phase 2](phase2.md) | Fix Cross-Module Includes | 3 new headers, 3 modified | Phase 1 |
| [Phase 3](phase3.md) | Build Static Library DAG | ModuleDAG.cmake | Phase 1 |
| [Phase 4](phase4.md) | Service Interfaces | engine_services.h | Phase 2 |
| [Phase 5](phase5.md) | CI Enforcement | check_includes.py, workflow | Phase 2, 3 |
| [Phase 6](phase6.md) | Measure Improvement | Metrics scripts, docs | Phase 5 |

## Violations to Fix (14 Total)

| File | Violations | Fix |
|------|------------|-----|
| engine/include/builtin.h | 12 | Create builtin_types.h shim |
| engine/include/bios_disk.h | 1 | Create cdrom_interface.h shim |
| engine/include/render.h | 1 | Create render_types.h shim |

## New Files Created

```
cmake/
├── ModuleManifest.cmake      (Phase 1)
└── ModuleDAG.cmake           (Phase 3)

engine/include/dosbox/
├── builtin_types.h           (Phase 2)
├── cdrom_interface.h         (Phase 2)
├── render_types.h            (Phase 2)
└── engine_services.h         (Phase 4)

engine/src/builtin/
└── builtin_data.cpp          (Phase 2)

scripts/
├── check_includes.py         (Phase 5)
└── measure_rebuild.py        (Phase 6)

.github/workflows/
└── module-dag.yml            (Phase 5)
```

## Files Modified

```
CMakeLists.txt                 (Phase 1, 3)
engine/CMakeLists.txt          (Phase 2)
engine/include/builtin.h       (Phase 2)
engine/include/bios_disk.h     (Phase 2)
engine/include/render.h        (Phase 2)
ARCHITECTURE.md                (Phase 1, 4, 6)
```

## Success Criteria

- [ ] `grep -r '../src/' engine/include/` returns empty
- [ ] `cmake -B build` prints "All DAGs Valid"
- [ ] `python scripts/check_includes.py --path .` exits 0
- [ ] All existing tests pass
- [ ] Incremental rebuild time improved >50%

## Execution Order

```
┌─────────────────────────────────────────────────────────────┐
│ Phase 1: Define Module Boundaries                           │
│ - Create cmake/ModuleManifest.cmake                         │
│ - Update ARCHITECTURE.md                                    │
└─────────────────────────────────────────────────────────────┘
                              │
              ┌───────────────┴───────────────┐
              ▼                               ▼
┌─────────────────────────────┐   ┌─────────────────────────────┐
│ Phase 2: Fix Includes       │   │ Phase 3: Build DAG          │
│ - Create shim headers       │   │ - Create ModuleDAG.cmake    │
│ - Remove ../src/ includes   │   │ - Add verification calls    │
└─────────────────────────────┘   └─────────────────────────────┘
              │                               │
              └───────────────┬───────────────┘
                              ▼
┌─────────────────────────────────────────────────────────────┐
│ Phase 4: Service Interfaces                                  │
│ - Create engine_services.h                                   │
│ - Document cross-module contract                            │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│ Phase 5: CI Enforcement                                      │
│ - Create check_includes.py                                   │
│ - Create GitHub Actions workflow                            │
│ - Enable strict enforcement                                  │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│ Phase 6: Measure Improvement                                 │
│ - Collect baseline metrics (before Phase 2)                  │
│ - Collect after metrics                                      │
│ - Generate comparison report                                 │
└─────────────────────────────────────────────────────────────┘
```

## Test Summary

Each phase includes:
- **Unit Tests** - Isolated component tests
- **Integration Tests** - End-to-end workflow tests
- **Manual Verification** - Commands to run
- **Acceptance Criteria** - Checkboxes for completion
- **Rollback Plan** - How to undo if issues arise

## Quick Start

```bash
# Collect baseline metrics FIRST (before any changes)
python scripts/measure_rebuild.py --baseline

# Then implement phases 1-5...

# After all phases complete:
python scripts/measure_rebuild.py --after
python scripts/measure_rebuild.py --compare

# Verify success:
grep -r '../src/' engine/include/  # Should be empty
cmake -B build  # Should show "All DAGs Valid"
python scripts/check_includes.py --path .  # Should exit 0
```
