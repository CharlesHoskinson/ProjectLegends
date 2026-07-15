/**
 * @file generate_corpus.cpp
 * @brief Generates seed corpus files for fuzzing.
 *
 * Creates valid save state files that serve as starting points for
 * the fuzzer. These help the fuzzer explore deeper code paths faster.
 *
 * Build:
 *   g++ -o generate_corpus generate_corpus.cpp -I../../include -L../../build -llegends_core
 *
 * Or just build with the project:
 *   cmake --build build --target generate_fuzz_corpus
 *
 * Run:
 *   ./generate_corpus corpus/
 */

#include <legends/legends_embed.h>
#include <dosbox/dosbox_library.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#ifdef _WIN32
#include <direct.h>
static void make_dir(const char* path) {
    _mkdir(path);
}
#else
#include <sys/stat.h>
static void make_dir(const char* path) {
    mkdir(path, 0777);
}
#endif

static bool write_file(const char* path, const void* data, size_t size) {
    FILE* f = fopen(path, "wb");
    if (!f) {
        fprintf(stderr, "Failed to open %s for writing\n", path);
        return false;
    }
    size_t written = fwrite(data, 1, size, f);
    fclose(f);
    return written == size;
}

static void save_engine_state(dosbox_lib_handle_t handle, const char* path) {
    size_t size = 0;
    if (dosbox_lib_save_state(handle, nullptr, 0, &size) != DOSBOX_LIB_OK || size == 0) {
        fprintf(stderr, "Failed to query engine state size for %s\n", path);
        return;
    }

    std::vector<uint8_t> buffer(size);
    if (dosbox_lib_save_state(handle, buffer.data(), buffer.size(), &size) != DOSBOX_LIB_OK) {
        fprintf(stderr, "Failed to save engine state for %s\n", path);
        return;
    }
    buffer.resize(size);

    if (write_file(path, buffer.data(), buffer.size())) {
        printf("Created: %s (%zu bytes)\n", path, buffer.size());
    }
}

static void generate_engine_memory_blob_corpus(const char* output_dir) {
    std::string engine_dir = std::string(output_dir) + "/engine_memory_blob";
    make_dir(engine_dir.c_str());

    dosbox_lib_handle_t handle = nullptr;
    dosbox_lib_destroy(nullptr);

    if (dosbox_lib_create(nullptr, &handle) != DOSBOX_LIB_OK ||
        dosbox_lib_init(handle) != DOSBOX_LIB_OK) {
        fprintf(stderr, "Failed to create engine instance for memory blob corpus\n");
        if (handle != nullptr) {
            dosbox_lib_destroy(handle);
        }
        return;
    }

    auto path = engine_dir + "/fresh_v5_engine_state.bin";
    save_engine_state(handle, path.c_str());

    dosbox_lib_step_cycles(handle, 2048, nullptr);
    path = engine_dir + "/stepped_v5_engine_state.bin";
    save_engine_state(handle, path.c_str());

    dosbox_lib_reset(handle);
    path = engine_dir + "/reset_v5_engine_state.bin";
    save_engine_state(handle, path.c_str());

    dosbox_lib_destroy(handle);
}

// Seeds for fuzz_config_parser (CI smoke path: corpus/config).
// libFuzzer requires the directory to exist when a corpus path is passed.
static void generate_config_parser_corpus(const char* output_dir) {
    std::string config_dir = std::string(output_dir) + "/config";
    make_dir(config_dir.c_str());

    struct Seed {
        const char* name;
        const char* body;
    };
    // Minimal DOSBox-style INI fragments to seed section/key parsers.
    static const Seed seeds[] = {
        {"empty.conf", ""},
        {"minimal.conf",
         "[dosbox]\n"
         "machine=svga_s3\n"
         "memsize=16\n"
         "\n"
         "[cpu]\n"
         "core=normal\n"
         "cycles=3000\n"
         "\n"
         "[render]\n"
         "fullscreen=false\n"
         "aspect=true\n"},
        {"comments_and_ws.conf",
         "# header comment\n"
         "\n"
         "  [dosbox]  \n"
         "machine = vga\n"
         "; inline-ish comment line\n"
         "memsize=4\n"},
        {"no_sections.conf",
         "orphan_key=value\n"
         "another=1\n"},
        {"malformed.conf",
         "[unclosed\n"
         "key=value\n"
         "[]\n"
         "=\n"
         "onlykey\n"},
    };

    for (const auto& seed : seeds) {
        std::string path = config_dir + "/" + seed.name;
        if (write_file(path.c_str(), seed.body, std::strlen(seed.body))) {
            printf("Created: %s (%zu bytes)\n", path.c_str(), std::strlen(seed.body));
        }
    }
}

static void generate_corpus(const char* output_dir) {
    make_dir(output_dir);
    legends_handle handle = nullptr;

    // Clean up any existing instance
    legends_force_destroy();

    auto err = legends_create(nullptr, &handle);
    if (err != LEGENDS_OK) {
        fprintf(stderr, "Failed to create instance: %d\n", err);
        return;
    }

    char path[512];

    // ─────────────────────────────────────────────────────────────────────
    // Corpus 1: Fresh state (no stepping)
    // ─────────────────────────────────────────────────────────────────────
    {
        size_t size = 0;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle, buffer.data(), size, &size);

        snprintf(path, sizeof(path), "%s/fresh_state.bin", output_dir);
        if (write_file(path, buffer.data(), size)) {
            printf("Created: %s (%zu bytes)\n", path, size);
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // Corpus 2: After stepping (1000 cycles)
    // ─────────────────────────────────────────────────────────────────────
    {
        legends_step_cycles(handle, 1000, nullptr);

        size_t size = 0;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle, buffer.data(), size, &size);

        snprintf(path, sizeof(path), "%s/stepped_1k.bin", output_dir);
        if (write_file(path, buffer.data(), size)) {
            printf("Created: %s (%zu bytes)\n", path, size);
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // Corpus 3: After more stepping (10000 cycles)
    // ─────────────────────────────────────────────────────────────────────
    {
        legends_step_cycles(handle, 9000, nullptr);  // Total 10000

        size_t size = 0;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle, buffer.data(), size, &size);

        snprintf(path, sizeof(path), "%s/stepped_10k.bin", output_dir);
        if (write_file(path, buffer.data(), size)) {
            printf("Created: %s (%zu bytes)\n", path, size);
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // Corpus 4: With input events
    // ─────────────────────────────────────────────────────────────────────
    {
        legends_key_event(handle, 0x1E, 1);  // 'A' down
        legends_step_cycles(handle, 100, nullptr);
        legends_key_event(handle, 0x1E, 0);  // 'A' up
        legends_step_cycles(handle, 100, nullptr);

        size_t size = 0;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle, buffer.data(), size, &size);

        snprintf(path, sizeof(path), "%s/with_input.bin", output_dir);
        if (write_file(path, buffer.data(), size)) {
            printf("Created: %s (%zu bytes)\n", path, size);
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // Corpus 5: After reset
    // ─────────────────────────────────────────────────────────────────────
    {
        legends_reset(handle);

        size_t size = 0;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle, buffer.data(), size, &size);

        snprintf(path, sizeof(path), "%s/after_reset.bin", output_dir);
        if (write_file(path, buffer.data(), size)) {
            printf("Created: %s (%zu bytes)\n", path, size);
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // Corpus 6-10: Various edge cases with corrupted headers
    // (These help the fuzzer learn to bypass validation)
    // ─────────────────────────────────────────────────────────────────────
    {
        // Get a valid state first
        size_t size = 0;
        legends_save_state(handle, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle, buffer.data(), size, &size);

        // Variant: Wrong magic (but otherwise valid structure)
        auto variant = buffer;
        variant[0] = 0x00;
        snprintf(path, sizeof(path), "%s/wrong_magic.bin", output_dir);
        if (write_file(path, variant.data(), variant.size())) {
            printf("Created: %s (%zu bytes)\n", path, variant.size());
        }

        // Variant: Wrong version
        variant = buffer;
        variant[4] = 99;
        snprintf(path, sizeof(path), "%s/wrong_version.bin", output_dir);
        if (write_file(path, variant.data(), variant.size())) {
            printf("Created: %s (%zu bytes)\n", path, variant.size());
        }

        // Variant: Truncated
        snprintf(path, sizeof(path), "%s/truncated.bin", output_dir);
        if (write_file(path, buffer.data(), size / 2)) {
            printf("Created: %s (%zu bytes)\n", path, size / 2);
        }

        // Variant: Minimal header only
        snprintf(path, sizeof(path), "%s/header_only.bin", output_dir);
        if (write_file(path, buffer.data(), 96)) {  // Just the header
            printf("Created: %s (96 bytes)\n", path);
        }
    }

    legends_destroy(handle);

    generate_engine_memory_blob_corpus(output_dir);
    generate_config_parser_corpus(output_dir);
    printf("\nCorpus generation complete.\n");
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <output_directory>\n", argv[0]);
        return 1;
    }

    generate_corpus(argv[1]);
    return 0;
}
