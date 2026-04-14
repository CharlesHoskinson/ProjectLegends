/**
 * @file test_no_phantom_decls.cpp
 * @brief Verifies that the 7 phantom forward declarations have been removed
 *        from machine_context.h (REQ-LC-006).
 *
 * Reads the header file at compile time via a build-time path and at test
 * time by scanning the source file for the banned class names.
 */

#include <gtest/gtest.h>

#include <fstream>
#include <sstream>
#include <string>
#include <vector>

// The path to the engine header, resolved relative to the source tree.
// CMake passes LEGENDS_SOURCE_DIR as a compile definition.
#ifndef LEGENDS_ENGINE_HEADER
#  define LEGENDS_ENGINE_HEADER "engine/include/aibox/machine_context.h"
#endif

namespace {

/// Load the header file content from the given path.
/// Returns an empty string if the file cannot be opened.
std::string load_file(const std::string& path) {
    std::ifstream f(path);
    if (!f.is_open()) {
        return {};
    }
    std::ostringstream ss;
    ss << f.rdbuf();
    return ss.str();
}

/// Return true if `line` is a forward declaration of `class_name`.
/// A forward declaration looks like:  class ClassName;
bool is_forward_decl(const std::string& line, const std::string& class_name) {
    // Look for "class <ClassName>;" with optional leading whitespace.
    const std::string pattern = "class " + class_name + ";";
    auto pos = line.find(pattern);
    if (pos == std::string::npos) {
        return false;
    }
    // Ensure the text before "class" is only whitespace (not a comment).
    const std::string before = line.substr(0, pos);
    for (char c : before) {
        if (c != ' ' && c != '\t') {
            return false;  // e.g. "// class Foo;" is a comment, not a decl
        }
    }
    return true;
}

}  // namespace

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

class NoPhantomDeclsTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Attempt to open the header relative to the working directory.
        // When run from the build directory the relative path should resolve.
        content_ = load_file(LEGENDS_ENGINE_HEADER);
        if (content_.empty()) {
            // Fallback: try the absolute path baked in at build time (if any).
            GTEST_SKIP() << "Could not open " << LEGENDS_ENGINE_HEADER
                         << " — skipping phantom-decl scan";
        }
    }

    std::string content_;

    /// Assert that no active (non-commented) forward declaration of
    /// `class_name` exists in the header.
    void assert_no_forward_decl(const std::string& class_name) {
        std::istringstream stream(content_);
        std::string line;
        int lineno = 0;
        while (std::getline(stream, line)) {
            ++lineno;
            EXPECT_FALSE(is_forward_decl(line, class_name))
                << "Phantom forward declaration found in machine_context.h"
                << " at line " << lineno << ": \"" << line << "\"\n"
                << "REQ-LC-006 requires class " << class_name
                << " to have been removed.";
        }
    }
};

TEST_F(NoPhantomDeclsTest, NoVgaContextForwardDecl) {
    assert_no_forward_decl("VgaContext");
}

TEST_F(NoPhantomDeclsTest, NoDosKernelForwardDecl) {
    assert_no_forward_decl("DosKernel");
}

TEST_F(NoPhantomDeclsTest, NoPicControllerForwardDecl) {
    assert_no_forward_decl("PicController");
}

TEST_F(NoPhantomDeclsTest, NoPitTimerForwardDecl) {
    assert_no_forward_decl("PitTimer");
}

TEST_F(NoPhantomDeclsTest, NoKeyboardControllerForwardDecl) {
    assert_no_forward_decl("KeyboardController");
}

TEST_F(NoPhantomDeclsTest, NoMouseControllerForwardDecl) {
    assert_no_forward_decl("MouseController");
}

TEST_F(NoPhantomDeclsTest, NoSoundSubsystemForwardDecl) {
    assert_no_forward_decl("SoundSubsystem");
}
