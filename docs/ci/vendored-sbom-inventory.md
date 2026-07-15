# Vendored library inventory for SBOM expansion (#42)

**Purpose:** Map `engine/src/libs/**` to version identity sources so
`scripts/generate_vendored_sbom.py` can grow beyond CMake pins + FluidSynth
without inventing phantom versions.

**Current generator (post F015):**

| Component | Identity source | In SBOM today |
|-----------|-----------------|---------------|
| gsl-lite | `LEGENDS_DEP_GSL_LITE_TAG` (FetchContent) | yes |
| SDL3 | `LEGENDS_DEP_SDL3_TAG` (optional FetchContent) | yes |
| googletest | `LEGENDS_DEP_GOOGLETEST_TAG` | yes |
| benchmark | `LEGENDS_DEP_BENCHMARK_TAG` | yes |
| fluidsynth | `engine/include/fluidsynth/version.h` → `1.1.6-noglib` | yes |

Unused CMake pins (do **not** invent SBOM rows from these alone):

- `LEGENDS_DEP_FLUIDSYNTH_TAG` — not wired to FetchContent for the engine
- `LEGENDS_DEP_MT32EMU_TAG` — verify before treating as active FetchContent

## Tree map (`engine/src/libs`)

| Directory | Role | Version discovery notes | Priority |
|-----------|------|-------------------------|----------|
| `fluidsynth/` | Softsynth | `version.h` **1.1.6-noglib**; CVE #43 | **P0** (done in SBOM) |
| `mt32/` | MT-32 emu (munt) | `VersionTagging.h` / `globals.h` maj/min macros | P1 |
| `physfs/` | Virtual FS | `PHYSFS_Version` / header docs; grep `PHYSFS_VER` | P1 |
| `libchdr/` | CHD disc images | Nested **lzma** + **zstd**; version via upstream tags / LICENSE | P1 |
| `decoders/` | Audio codecs | Bundles dr_*, stb, opus, speexdsp, ogg; multi-component | P2 |
| `zmbv/` | Video codec | Local + stubs; no clear semver | P2 |
| `xBRZ/` | Scaler | Changelog.txt | P2 |
| `gui_tk/` | GUI toolkit remnant | Likely unused in headless CI | P3 |
| `tinyfiledialogs/` | File dialogs | `tinyfd_version[]` runtime string | P2 |
| `passthroughio/` | I/O helper | Project-local | P3 |

## Generator extension plan

1. **Header parsers** (preferred): regex for well-known `#define FOO_VERSION` patterns (FluidSynth pattern already exists).  
2. **Manifest table** in `scripts/vendored_components.toml` for trees without clean macros (path → name → version → purl → notes).  
3. **Link-set filter:** only emit components that are actually referenced by a CMake target used in headless/CI builds (avoid inventorying dead `gui_tk` if unlinked).  
4. **CI:** keep `generate_vendored_sbom.py --check` fail-closed; add unit test for “no 2.x fluidsynth if version.h is 1.1.x”.  
5. **Do not** claim full #42 closed until every **linked** vendored component has a row.

## Suggested next code change (after R1 green)

```text
scripts/vendored_components.toml   # hand-reviewed table
scripts/generate_vendored_sbom.py  # merge pins + version.h + table
docs/ci/vendored-sbom.cdx.json     # regenerate
```

## Exit for #42 (partial → full)

- [x] Non-empty CycloneDX with pin integrity check  
- [x] Runtime FluidSynth identity from source (not phantom pin)  
- [ ] All CI-linked vendored libs inventoried  
- [ ] Optional: content hash / git submodule commit per tree  
