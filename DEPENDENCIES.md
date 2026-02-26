# Project Legends — Dependency Manifest

All external dependencies are version-pinned in `cmake/dependencies.cmake`.

| Dependency | Version/Tag | SPDX License | Repository | Purpose | Pinning Method |
|---|---|---|---|---|---|
| gsl-lite | v1.0.0 | MIT | https://github.com/gsl-lite/gsl-lite | C++ Contracts (Expects/Ensures) | FetchContent `GIT_TAG` |
| SDL3 | release-3.2.8 | Zlib | https://github.com/libsdl-org/SDL | Window, input, audio (PAL backend) | FetchContent `GIT_TAG` |
| GoogleTest | v1.14.0 | BSD-3-Clause | https://github.com/google/googletest | Unit and integration testing | FetchContent `GIT_TAG` |
| Google Benchmark | v1.8.3 | Apache-2.0 | https://github.com/google/benchmark | Performance benchmarks | FetchContent `GIT_TAG` |
| SDL2 | system | Zlib | https://github.com/libsdl-org/SDL | Legacy PAL backend (SDL2) | System `find_package` |

## Notes

- **Hermetic builds**: SDL3, gsl-lite, GoogleTest, and Benchmark all use FetchContent with pinned `GIT_TAG` values, so builds are reproducible without pre-installed system packages.
- **SDL2**: Currently uses system-installed SDL2 via `find_package(SDL2 REQUIRED)`. SDL2 and SDL3 backends are mutually exclusive for the `project_legends` executable.
- **gsl-lite**: Kept `PRIVATE` to `legends_core` — never exposed in public headers. Uses v1 namespace (`gsl_lite`) and header (`<gsl-lite/gsl-lite.hpp>`).
- **License compatibility**: All dependencies are compatible with the project's GPL-2.0-or-later license. The MIT-licensed IPC/proxy libraries (`legends_ipc`, `legends_proxy`) do not link any GPL code.
