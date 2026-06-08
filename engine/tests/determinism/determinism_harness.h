/**
 * @file determinism_harness.h
 * @brief Test harness for determinism verification (PR #23)
 *
 * Provides utilities for verifying that DOSBox-X execution is deterministic:
 * - Golden trace recording and replay
 * - State hash verification
 * - Save/load round-trip testing
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef AIBOX_DETERMINISM_HARNESS_H
#define AIBOX_DETERMINISM_HARNESS_H

#include "dosbox/dosbox_library.h"
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

#include <array>
#include <cstdint>
#include <fstream>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

namespace aibox::determinism {

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash Utilities
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief 32-byte state hash.
 */
struct StateHash {
    std::array<uint8_t, 32> bytes{};

    bool operator==(const StateHash& other) const {
        return bytes == other.bytes;
    }

    bool operator!=(const StateHash& other) const {
        return bytes != other.bytes;
    }

    /**
     * @brief Convert to hex string for display/logging.
     */
    [[nodiscard]] std::string to_hex() const {
        static const char hex_chars[] = "0123456789abcdef";
        std::string result;
        result.reserve(64);
        for (uint8_t b : bytes) {
            result += hex_chars[b >> 4];
            result += hex_chars[b & 0x0F];
        }
        return result;
    }

    /**
     * @brief Parse from hex string.
     */
    static std::optional<StateHash> from_hex(const std::string& hex) {
        if (hex.length() != 64) {
            return std::nullopt;
        }
        StateHash hash;
        for (size_t i = 0; i < 32; ++i) {
            char hi = hex[i * 2];
            char lo = hex[i * 2 + 1];
            auto nibble = [](char c) -> int {
                if (c >= '0' && c <= '9') return c - '0';
                if (c >= 'a' && c <= 'f') return c - 'a' + 10;
                if (c >= 'A' && c <= 'F') return c - 'A' + 10;
                return -1;
            };
            int hi_val = nibble(hi);
            int lo_val = nibble(lo);
            if (hi_val < 0 || lo_val < 0) {
                return std::nullopt;
            }
            hash.bytes[i] = static_cast<uint8_t>((hi_val << 4) | lo_val);
        }
        return hash;
    }
};

/**
 * @brief Get current state hash from library handle.
 */
inline StateHash get_state_hash(dosbox_lib_handle_t handle) {
    StateHash hash;
    dosbox_lib_get_state_hash(handle, hash.bytes.data());
    return hash;
}

inline std::vector<std::pair<std::string, std::string>> get_component_hashes(
    dosbox_lib_handle_t handle
) {
    void* ctx_ptr = nullptr;
    if (dosbox_lib_get_context_ptr(handle, &ctx_ptr) != DOSBOX_LIB_OK || ctx_ptr == nullptr) {
        return {};
    }

    auto* ctx = static_cast<dosbox::DOSBoxContext*>(ctx_ptr);
    auto hash_state = [](const auto& state) {
        dosbox::HashBuilder builder;
        state.hash_into(builder);
        return dosbox::hash_to_hex(builder.finalize());
    };

    return {
        {"timing", hash_state(ctx->timing)},
        {"cpu", hash_state(ctx->cpu_state)},
        {"mixer", hash_state(ctx->mixer)},
        {"vga", hash_state(ctx->vga)},
        {"pic", hash_state(ctx->pic)},
        {"keyboard", hash_state(ctx->keyboard)},
        {"input", hash_state(ctx->input)},
        {"memory", hash_state(ctx->memory)},
        {"dma", hash_state(ctx->dma)},
        {"dos", hash_state(ctx->dos)},
    };
}

inline std::string format_component_diff(
    const std::vector<std::pair<std::string, std::string>>& expected,
    const std::vector<std::pair<std::string, std::string>>& actual
) {
    std::ostringstream out;
    const size_t count = std::min(expected.size(), actual.size());
    for (size_t i = 0; i < count; ++i) {
        if (expected[i].second != actual[i].second) {
            out << "\n  " << expected[i].first
                << ": expected " << expected[i].second
                << ", actual " << actual[i].second;
        }
    }
    return out.str();
}

// ═══════════════════════════════════════════════════════════════════════════════
// Trace Point
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief A single point in a trace recording.
 */
struct TracePoint {
    uint64_t cycles;        ///< Total cycles at this point
    uint64_t emu_time_us;   ///< Emulated time in microseconds
    StateHash hash;         ///< State hash at this point
    std::string label;      ///< Optional label for debugging

    /**
     * @brief Serialize to JSONL format.
     */
    [[nodiscard]] std::string to_jsonl() const {
        std::ostringstream ss;
        ss << "{\"cycles\":" << cycles
           << ",\"emu_time_us\":" << emu_time_us
           << ",\"hash\":\"" << hash.to_hex() << "\"";
        if (!label.empty()) {
            ss << ",\"label\":\"" << label << "\"";
        }
        ss << "}";
        return ss.str();
    }

    /**
     * @brief Parse from JSONL format (simple parser).
     */
    static std::optional<TracePoint> from_jsonl(const std::string& line) {
        TracePoint point;

        // Simple JSON parsing (assumes well-formed input)
        auto find_value = [&line](const std::string& key) -> std::string {
            std::string search = "\"" + key + "\":";
            auto pos = line.find(search);
            if (pos == std::string::npos) return "";
            pos += search.length();
            if (line[pos] == '"') {
                // String value
                pos++;
                auto end = line.find('"', pos);
                if (end == std::string::npos) return "";
                return line.substr(pos, end - pos);
            } else {
                // Numeric value
                auto end = line.find_first_of(",}", pos);
                if (end == std::string::npos) return "";
                return line.substr(pos, end - pos);
            }
        };

        auto cycles_str = find_value("cycles");
        auto time_str = find_value("emu_time_us");
        auto hash_str = find_value("hash");
        point.label = find_value("label");

        if (cycles_str.empty() || time_str.empty() || hash_str.empty()) {
            return std::nullopt;
        }

        point.cycles = std::stoull(cycles_str);
        point.emu_time_us = std::stoull(time_str);

        auto hash = StateHash::from_hex(hash_str);
        if (!hash) {
            return std::nullopt;
        }
        point.hash = *hash;

        return point;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Trace Recording
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief A complete trace recording.
 */
class TraceRecording {
public:
    /**
     * @brief Add a trace point.
     */
    void add_point(const TracePoint& point) {
        points_.push_back(point);
    }

    /**
     * @brief Add a trace point from current state.
     */
    void capture(dosbox_lib_handle_t handle, const std::string& label = "") {
        TracePoint point;
        dosbox_lib_get_total_cycles(handle, &point.cycles);
        dosbox_lib_get_emu_time(handle, &point.emu_time_us);
        point.hash = get_state_hash(handle);
        point.label = label;
        points_.push_back(point);
    }

    /**
     * @brief Get all trace points.
     */
    [[nodiscard]] const std::vector<TracePoint>& points() const {
        return points_;
    }

    /**
     * @brief Get number of trace points.
     */
    [[nodiscard]] size_t size() const {
        return points_.size();
    }

    /**
     * @brief Check if empty.
     */
    [[nodiscard]] bool empty() const {
        return points_.empty();
    }

    /**
     * @brief Save to JSONL file.
     */
    bool save(const std::string& path) const {
        std::ofstream file(path);
        if (!file) return false;
        for (const auto& point : points_) {
            file << point.to_jsonl() << "\n";
        }
        return true;
    }

    /**
     * @brief Load from JSONL file.
     */
    static std::optional<TraceRecording> load(const std::string& path) {
        std::ifstream file(path);
        if (!file) return std::nullopt;

        TraceRecording recording;
        std::string line;
        while (std::getline(file, line)) {
            if (line.empty()) continue;
            auto point = TracePoint::from_jsonl(line);
            if (!point) return std::nullopt;
            recording.points_.push_back(*point);
        }
        return recording;
    }

    /**
     * @brief Compare two recordings for equality.
     */
    [[nodiscard]] bool matches(const TraceRecording& other) const {
        if (points_.size() != other.points_.size()) {
            return false;
        }
        for (size_t i = 0; i < points_.size(); ++i) {
            if (points_[i].cycles != other.points_[i].cycles ||
                points_[i].hash != other.points_[i].hash) {
                return false;
            }
        }
        return true;
    }

    /**
     * @brief Find first difference between two recordings.
     * @return Index of first difference, or nullopt if identical.
     */
    [[nodiscard]] std::optional<size_t> find_divergence(
        const TraceRecording& other
    ) const {
        size_t min_size = std::min(points_.size(), other.points_.size());
        for (size_t i = 0; i < min_size; ++i) {
            if (points_[i].hash != other.points_[i].hash) {
                return i;
            }
        }
        if (points_.size() != other.points_.size()) {
            return min_size;
        }
        return std::nullopt;
    }

private:
    std::vector<TracePoint> points_;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Determinism Verifier
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Verification result.
 */
struct VerificationResult {
    bool passed = false;
    std::string message;
    std::optional<size_t> divergence_index;
    StateHash expected_hash;
    StateHash actual_hash;
};

/**
 * @brief Verifies deterministic execution.
 */
class DeterminismVerifier {
public:
    /**
     * @brief Verify that running the same input produces the same output.
     *
     * Runs the emulator twice with the same configuration and steps,
     * recording traces at each checkpoint, then compares.
     *
     * @param config Configuration to use
     * @param total_ms Total milliseconds to run
     * @param checkpoint_interval_ms Interval between checkpoints
     * @return Verification result
     */
    static VerificationResult verify_replay(
        const dosbox_lib_config_t* config,
        uint32_t total_ms,
        uint32_t checkpoint_interval_ms
    ) {
        // Run 1
        auto trace1 = run_and_trace(config, total_ms, checkpoint_interval_ms);
        if (!trace1) {
            return {false, "Failed to run first trace", {}, {}, {}};
        }

        // Run 2
        auto trace2 = run_and_trace(config, total_ms, checkpoint_interval_ms);
        if (!trace2) {
            return {false, "Failed to run second trace", {}, {}, {}};
        }

        // Compare
        auto divergence = trace1->find_divergence(*trace2);
        if (divergence) {
            VerificationResult result;
            result.passed = false;
            result.message = "Traces diverged at checkpoint " +
                             std::to_string(*divergence);
            result.divergence_index = divergence;
            if (*divergence < trace1->size()) {
                result.expected_hash = trace1->points()[*divergence].hash;
            }
            if (*divergence < trace2->size()) {
                result.actual_hash = trace2->points()[*divergence].hash;
            }
            return result;
        }

        return {true, "Traces match", {}, {}, {}};
    }

    /**
     * @brief Verify save/load round-trip preserves state.
     *
     * Steps, saves state, continues stepping, restores state,
     * continues stepping, verifies hashes match.
     *
     * @param config Configuration to use
     * @param ms_before_save Steps before saving
     * @param ms_after_save Steps after saving (and after restore)
     * @return Verification result
     */
    static VerificationResult verify_save_load(
        const dosbox_lib_config_t* config,
        uint32_t ms_before_save,
        uint32_t ms_after_save
    ) {
        dosbox_lib_handle_t handle = nullptr;

        if (dosbox_lib_create(config, &handle) != DOSBOX_LIB_OK) {
            return {false, "Failed to create instance", {}, {}, {}};
        }

        if (dosbox_lib_init(handle) != DOSBOX_LIB_OK) {
            dosbox_lib_destroy(handle);
            return {false, "Failed to init instance", {}, {}, {}};
        }

        // Step to save point
        dosbox_lib_step_ms(handle, ms_before_save, nullptr);
        StateHash hash_at_save = get_state_hash(handle);
        auto components_at_save = get_component_hashes(handle);

        // Save state
        size_t state_size = 0;
        dosbox_lib_save_state(handle, nullptr, 0, &state_size);
        std::vector<uint8_t> saved_state(state_size);
        dosbox_lib_save_state(handle, saved_state.data(), state_size, &state_size);

        // Continue stepping and record hash
        dosbox_lib_step_ms(handle, ms_after_save, nullptr);
        StateHash hash_run1 = get_state_hash(handle);
        auto components_run1 = get_component_hashes(handle);

        // Restore state
        dosbox_lib_load_state(handle, saved_state.data(), state_size);
        StateHash hash_after_load = get_state_hash(handle);
        auto components_after_load = get_component_hashes(handle);
        if (hash_at_save != hash_after_load) {
            VerificationResult result;
            result.passed = false;
            result.message =
                "State hash differs immediately after save/load restore\n"
                "  saved:    " + hash_at_save.to_hex() + "\n"
                "  restored: " + hash_after_load.to_hex() +
                format_component_diff(components_at_save, components_after_load);
            result.expected_hash = hash_at_save;
            result.actual_hash = hash_after_load;
            dosbox_lib_destroy(handle);
            return result;
        }

        // Step same amount and record hash
        dosbox_lib_step_ms(handle, ms_after_save, nullptr);
        StateHash hash_run2 = get_state_hash(handle);
        auto components_run2 = get_component_hashes(handle);

        dosbox_lib_destroy(handle);

        // Compare
        if (hash_run1 != hash_run2) {
            VerificationResult result;
            result.passed = false;
            result.message =
                "State hashes differ after save/load round-trip\n"
                "  expected: " + hash_run1.to_hex() + "\n"
                "  actual:   " + hash_run2.to_hex() +
                format_component_diff(components_run1, components_run2);
            result.expected_hash = hash_run1;
            result.actual_hash = hash_run2;
            return result;
        }

        return {true, "Save/load round-trip preserves determinism", {}, {}, {}};
    }

private:
    static std::optional<TraceRecording> run_and_trace(
        const dosbox_lib_config_t* config,
        uint32_t total_ms,
        uint32_t checkpoint_interval_ms
    ) {
        dosbox_lib_handle_t handle = nullptr;

        if (dosbox_lib_create(config, &handle) != DOSBOX_LIB_OK) {
            return std::nullopt;
        }

        if (dosbox_lib_init(handle) != DOSBOX_LIB_OK) {
            dosbox_lib_destroy(handle);
            return std::nullopt;
        }

        TraceRecording trace;
        trace.capture(handle, "start");

        uint32_t ms_run = 0;
        while (ms_run < total_ms) {
            uint32_t step = std::min(checkpoint_interval_ms, total_ms - ms_run);
            dosbox_lib_step_ms(handle, step, nullptr);
            ms_run += step;
            trace.capture(handle, "checkpoint_" + std::to_string(ms_run));
        }

        dosbox_lib_destroy(handle);
        return trace;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Golden Trace
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief A golden (expected) trace for regression testing.
 */
class GoldenTrace {
public:
    explicit GoldenTrace(std::string name) : name_(std::move(name)) {}

    /**
     * @brief Add expected checkpoint.
     */
    void add_checkpoint(uint64_t cycles, const StateHash& hash) {
        checkpoints_.push_back({cycles, hash});
    }

    /**
     * @brief Verify against actual execution.
     */
    [[nodiscard]] VerificationResult verify(dosbox_lib_handle_t handle) const {
        for (size_t i = 0; i < checkpoints_.size(); ++i) {
            const auto& [expected_cycles, expected_hash] = checkpoints_[i];

            // Step to checkpoint
            uint64_t current_cycles = 0;
            dosbox_lib_get_total_cycles(handle, &current_cycles);

            if (current_cycles < expected_cycles) {
                uint64_t cycles_to_run = expected_cycles - current_cycles;
                dosbox_lib_step_cycles(handle, cycles_to_run, nullptr);
            }

            // Check hash
            StateHash actual_hash = get_state_hash(handle);
            if (actual_hash != expected_hash) {
                VerificationResult result;
                result.passed = false;
                result.message = "Golden trace mismatch at checkpoint " +
                                 std::to_string(i) + " (" + name_ + ")";
                result.divergence_index = i;
                result.expected_hash = expected_hash;
                result.actual_hash = actual_hash;
                return result;
            }
        }

        return {true, "Golden trace matched: " + name_, {}, {}, {}};
    }

    /**
     * @brief Get trace name.
     */
    [[nodiscard]] const std::string& name() const { return name_; }

private:
    std::string name_;
    std::vector<std::pair<uint64_t, StateHash>> checkpoints_;
};

} // namespace aibox::determinism

#endif // AIBOX_DETERMINISM_HARNESS_H
