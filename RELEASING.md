# Releasing Project Legends

## Branch Model

| Branch Pattern | Purpose |
|---|---|
| `main` | Latest stable code; merge-to-main triggers sanitizer builds |
| `develop` | Integration branch for feature work |
| `release/X.Y` | Release stabilization branch (created from `develop`) |
| `feature/*` | Feature branches (PR into `develop`) |

## Tag Convention

| Tag Pattern | Meaning |
|---|---|
| `vX.Y.Z` | Stable release (e.g., `v1.0.0`) |
| `vX.Y.Z-rc.N` | Release candidate (e.g., `v1.0.0-rc.1`) |
| `vX.Y.Z-alpha.N` | Alpha pre-release |
| `vX.Y.Z-beta.N` | Beta pre-release |

Tags must match `v[0-9]*` for `cmake/version.cmake` to parse them.

## Release Workflow

### 1. Prepare

```bash
git checkout develop
git pull
git checkout -b release/X.Y
```

### 2. Stabilize

- Bump `PROJECT_VERSION` in `CMakeLists.txt` if needed
- Update `DEPENDENCIES.md` with any version changes
- Fix release-blocking issues on the release branch
- All CI checks must pass (sanitizers, fuzz, TLA+)

### 3. Tag

```bash
git tag -a vX.Y.Z -m "Release vX.Y.Z"
git push origin vX.Y.Z
```

### 4. Package

The tag push triggers the CI packaging job which runs `cpack` on all platforms:
- **Windows**: NSIS installer + ZIP archive
- **macOS**: DMG + TGZ archive
- **Linux**: TGZ archive

### 5. Merge Back

```bash
git checkout main
git merge release/X.Y
git checkout develop
git merge release/X.Y
```

## Hotfix Process

For critical fixes to a released version:

```bash
git checkout vX.Y.Z
git checkout -b hotfix/X.Y.Z+1
# ... fix ...
git tag -a vX.Y.(Z+1) -m "Hotfix release"
git push origin vX.Y.(Z+1)
git checkout develop
git merge hotfix/X.Y.Z+1
```
