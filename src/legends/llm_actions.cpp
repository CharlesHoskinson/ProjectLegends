/**
 * @file llm_actions.cpp
 * @brief Implementation of LLM action types.
 */

#include <legends/llm_actions.h>
#include <legends/llm_serializer.h>
#include <algorithm>
#include <cctype>
#include <sstream>
#include <unordered_map>

namespace legends::llm {

// ─────────────────────────────────────────────────────────────────────────────
// SpecialKey Parsing
// ─────────────────────────────────────────────────────────────────────────────

std::optional<SpecialKey> parse_special_key(const std::string& name) {
    // Case-insensitive lookup
    std::string lower_name;
    lower_name.reserve(name.size());
    for (char c : name) {
        lower_name += static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    }

    static const std::unordered_map<std::string, SpecialKey> key_map = {
        {"enter", SpecialKey::Enter},
        {"return", SpecialKey::Enter},
        {"escape", SpecialKey::Escape},
        {"esc", SpecialKey::Escape},
        {"tab", SpecialKey::Tab},
        {"backspace", SpecialKey::Backspace},
        {"up", SpecialKey::Up},
        {"down", SpecialKey::Down},
        {"left", SpecialKey::Left},
        {"right", SpecialKey::Right},
        {"home", SpecialKey::Home},
        {"end", SpecialKey::End},
        {"pageup", SpecialKey::PageUp},
        {"pgup", SpecialKey::PageUp},
        {"pagedown", SpecialKey::PageDown},
        {"pgdn", SpecialKey::PageDown},
        {"insert", SpecialKey::Insert},
        {"ins", SpecialKey::Insert},
        {"delete", SpecialKey::Delete},
        {"del", SpecialKey::Delete},
        {"f1", SpecialKey::F1},
        {"f2", SpecialKey::F2},
        {"f3", SpecialKey::F3},
        {"f4", SpecialKey::F4},
        {"f5", SpecialKey::F5},
        {"f6", SpecialKey::F6},
        {"f7", SpecialKey::F7},
        {"f8", SpecialKey::F8},
        {"f9", SpecialKey::F9},
        {"f10", SpecialKey::F10},
        {"f11", SpecialKey::F11},
        {"f12", SpecialKey::F12},
        {"ctrlc", SpecialKey::CtrlC},
        {"ctrl-c", SpecialKey::CtrlC},
        {"ctrlz", SpecialKey::CtrlZ},
        {"ctrl-z", SpecialKey::CtrlZ},
        {"ctrlbreak", SpecialKey::CtrlBreak},
        {"ctrl-break", SpecialKey::CtrlBreak},
        {"altf4", SpecialKey::AltF4},
        {"alt-f4", SpecialKey::AltF4},
        {"altenter", SpecialKey::AltEnter},
        {"alt-enter", SpecialKey::AltEnter},
    };

    auto it = key_map.find(lower_name);
    if (it != key_map.end()) {
        return it->second;
    }
    return std::nullopt;
}

uint8_t get_scancode(SpecialKey key, bool& extended) noexcept {
    extended = false;

    switch (key) {
        case SpecialKey::Enter:     return 0x1C;
        case SpecialKey::Escape:    return 0x01;
        case SpecialKey::Tab:       return 0x0F;
        case SpecialKey::Backspace: return 0x0E;
        case SpecialKey::Up:        extended = true; return 0x48;
        case SpecialKey::Down:      extended = true; return 0x50;
        case SpecialKey::Left:      extended = true; return 0x4B;
        case SpecialKey::Right:     extended = true; return 0x4D;
        case SpecialKey::Home:      extended = true; return 0x47;
        case SpecialKey::End:       extended = true; return 0x4F;
        case SpecialKey::PageUp:    extended = true; return 0x49;
        case SpecialKey::PageDown:  extended = true; return 0x51;
        case SpecialKey::Insert:    extended = true; return 0x52;
        case SpecialKey::Delete:    extended = true; return 0x53;
        case SpecialKey::F1:        return 0x3B;
        case SpecialKey::F2:        return 0x3C;
        case SpecialKey::F3:        return 0x3D;
        case SpecialKey::F4:        return 0x3E;
        case SpecialKey::F5:        return 0x3F;
        case SpecialKey::F6:        return 0x40;
        case SpecialKey::F7:        return 0x41;
        case SpecialKey::F8:        return 0x42;
        case SpecialKey::F9:        return 0x43;
        case SpecialKey::F10:       return 0x44;
        case SpecialKey::F11:       return 0x57;
        case SpecialKey::F12:       return 0x58;
        case SpecialKey::CtrlC:     return 0x2E;  // C key (with Ctrl)
        case SpecialKey::CtrlZ:     return 0x2C;  // Z key (with Ctrl)
        case SpecialKey::CtrlBreak: return 0x46;  // Scroll Lock (Ctrl+Break)
        case SpecialKey::AltF4:     return 0x3E;  // F4 key (with Alt)
        case SpecialKey::AltEnter:  return 0x1C;  // Enter key (with Alt)
        default:                    return 0;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionBatch Validation
// ─────────────────────────────────────────────────────────────────────────────

std::optional<std::string> ActionBatch::validate() const {
    if (actions.size() > MaxBatchSize) {
        return "Too many actions in batch (max " + std::to_string(MaxBatchSize) + ")";
    }

    if (timeout_ms > MaxTimeoutMs) {
        return "Timeout exceeds maximum (" + std::to_string(MaxTimeoutMs) + "ms)";
    }

    for (size_t i = 0; i < actions.size(); ++i) {
        const auto& action = actions[i];

        if (std::holds_alternative<TypeAction>(action)) {
            const auto& type_action = std::get<TypeAction>(action);
            if (type_action.text.size() > MaxTypeLength) {
                return "Action " + std::to_string(i) +
                       ": text too long (max " + std::to_string(MaxTypeLength) + ")";
            }
        } else if (std::holds_alternative<WaitAction>(action)) {
            const auto& wait_action = std::get<WaitAction>(action);
            if (wait_action.milliseconds > MaxTimeoutMs) {
                return "Action " + std::to_string(i) +
                       ": wait too long (max " + std::to_string(MaxTimeoutMs) + "ms)";
            }
        }
    }

    return std::nullopt;
}

std::variant<ActionBatch, std::string> ActionBatch::from_json(const std::string& json) {
    // Simple JSON parsing - for production use a proper JSON library
    // This is a minimal implementation for testing

    ActionBatch batch;

    // Check for basic structure
    if (json.find("\"actions\"") == std::string::npos) {
        return std::string("Missing 'actions' field");
    }

    // Parse timeout if present
    auto timeout_pos = json.find("\"timeout_ms\"");
    if (timeout_pos != std::string::npos) {
        // Find the number after the colon
        auto colon_pos = json.find(':', timeout_pos);
        if (colon_pos != std::string::npos) {
            try {
                batch.timeout_ms = std::stoul(json.substr(colon_pos + 1));
            } catch (...) {
                // Use default
            }
        }
    }

    // Parse return_frame if present
    if (json.find("\"return_frame\":false") != std::string::npos ||
        json.find("\"return_frame\": false") != std::string::npos) {
        batch.return_frame = false;
    }

    // Parse stop_on_error if present
    if (json.find("\"stop_on_error\":false") != std::string::npos ||
        json.find("\"stop_on_error\": false") != std::string::npos) {
        batch.stop_on_error = false;
    }

    // For a complete implementation, parse the actions array
    // This is left as a stub since proper JSON parsing requires more code

    return batch;
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionBatchResponse Implementation
// ─────────────────────────────────────────────────────────────────────────────

std::string ActionBatchResponse::to_json() const {
    std::ostringstream oss;
    oss << "{";
    oss << "\"success\":" << (success ? "true" : "false") << ",";
    oss << "\"actions_executed\":" << results.size() << ",";

    oss << "\"results\":[";
    for (size_t i = 0; i < results.size(); ++i) {
        if (i > 0) oss << ",";
        const auto& r = results[i];
        oss << "{\"index\":" << r.action_index
            << ",\"status\":\"" << to_string(r.status) << "\""
            << ",\"duration_us\":" << r.duration_us;
        if (!r.error_message.empty()) {
            oss << ",\"error\":\"" << json_escape(r.error_message) << "\"";
        }
        oss << "}";
    }
    oss << "],";

    oss << "\"total_duration_us\":" << total_duration_us;

    if (frame.has_value()) {
        oss << ",\"frame\":" << frame->to_json();
    }

    oss << "}";
    return oss.str();
}

size_t ActionBatchResponse::success_count() const noexcept {
    size_t count = 0;
    for (const auto& r : results) {
        if (r.status == ActionStatus::Success) {
            ++count;
        }
    }
    return count;
}

const ActionResult* ActionBatchResponse::first_error() const noexcept {
    for (const auto& r : results) {
        if (r.status != ActionStatus::Success) {
            return &r;
        }
    }
    return nullptr;
}

// ─────────────────────────────────────────────────────────────────────────────
// Scancode Conversion
// ─────────────────────────────────────────────────────────────────────────────

namespace {

// Scancode lookup table for lowercase letters a-z
constexpr uint8_t letter_scancodes[26] = {
    0x1E, 0x30, 0x2E, 0x20, 0x12, 0x21, 0x22, 0x23, 0x17,
    0x24, 0x25, 0x26, 0x32, 0x31, 0x18, 0x19, 0x10, 0x13,
    0x1F, 0x14, 0x16, 0x2F, 0x11, 0x2D, 0x15, 0x2C
};

// Scancode lookup for digits 0-9
constexpr uint8_t digit_scancodes[10] = {
    0x0B, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A
};

// Common punctuation scancodes (without shift)
struct PunctuationMapping {
    char character;
    uint8_t scancode;
    bool needs_shift;
};

constexpr PunctuationMapping punctuation_map[] = {
    {' ',  0x39, false},
    {'-',  0x0C, false},
    {'=',  0x0D, false},
    {'[',  0x1A, false},
    {']',  0x1B, false},
    {';',  0x27, false},
    {'\'', 0x28, false},
    {'`',  0x29, false},
    {'\\', 0x2B, false},
    {',',  0x33, false},
    {'.',  0x34, false},
    {'/',  0x35, false},
    {'!',  0x02, true},
    {'@',  0x03, true},
    {'#',  0x04, true},
    {'$',  0x05, true},
    {'%',  0x06, true},
    {'^',  0x07, true},
    {'&',  0x08, true},
    {'*',  0x09, true},
    {'(',  0x0A, true},
    {')',  0x0B, true},
    {'_',  0x0C, true},
    {'+',  0x0D, true},
    {'{',  0x1A, true},
    {'}',  0x1B, true},
    {':',  0x27, true},
    {'"',  0x28, true},
    {'~',  0x29, true},
    {'|',  0x2B, true},
    {'<',  0x33, true},
    {'>',  0x34, true},
    {'?',  0x35, true},
};

} // anonymous namespace

std::vector<ScancodeEvent> char_to_scancodes(char c) {
    std::vector<ScancodeEvent> events;
    uint8_t scancode = 0;
    bool need_shift = false;

    // Check for letters
    if (c >= 'a' && c <= 'z') {
        scancode = letter_scancodes[c - 'a'];
    } else if (c >= 'A' && c <= 'Z') {
        scancode = letter_scancodes[c - 'A'];
        need_shift = true;
    }
    // Check for digits
    else if (c >= '0' && c <= '9') {
        scancode = digit_scancodes[c - '0'];
    }
    // Check for special characters
    else if (c == '\n' || c == '\r') {
        scancode = 0x1C;  // Enter
    } else if (c == '\t') {
        scancode = 0x0F;  // Tab
    } else {
        // Search punctuation map
        for (const auto& pm : punctuation_map) {
            if (pm.character == c) {
                scancode = pm.scancode;
                need_shift = pm.needs_shift;
                break;
            }
        }
    }

    if (scancode == 0) {
        return events;  // Unsupported character
    }

    // Build scancode sequence
    if (need_shift) {
        events.push_back({0x2A, true, false});   // Left Shift down
    }
    events.push_back({scancode, true, false});   // Key down
    events.push_back({scancode, false, false});  // Key up
    if (need_shift) {
        events.push_back({0x2A, false, false});  // Left Shift up
    }

    return events;
}

std::vector<ScancodeEvent> text_to_scancodes(const std::string& text) {
    std::vector<ScancodeEvent> events;

    for (char c : text) {
        auto char_events = char_to_scancodes(c);
        events.insert(events.end(), char_events.begin(), char_events.end());
    }

    return events;
}

std::vector<ScancodeEvent> special_key_to_scancodes(SpecialKey key) {
    std::vector<ScancodeEvent> events;

    bool extended = false;
    uint8_t scancode = get_scancode(key, extended);

    if (scancode == 0) {
        return events;
    }

    // Handle modifier keys
    bool need_ctrl = (key == SpecialKey::CtrlC || key == SpecialKey::CtrlZ ||
                      key == SpecialKey::CtrlBreak);
    bool need_alt = (key == SpecialKey::AltF4 || key == SpecialKey::AltEnter);

    // Modifier down
    if (need_ctrl) {
        events.push_back({0x1D, true, false});  // Left Ctrl
    }
    if (need_alt) {
        events.push_back({0x38, true, false});  // Left Alt
    }

    // Extended prefix
    if (extended) {
        events.push_back({0xE0, true, true});
    }

    // Key press
    events.push_back({scancode, true, extended});
    events.push_back({scancode, false, extended});

    // Extended prefix for release
    if (extended) {
        events.push_back({0xE0, false, true});
    }

    // Modifier up
    if (need_alt) {
        events.push_back({0x38, false, false});
    }
    if (need_ctrl) {
        events.push_back({0x1D, false, false});
    }

    return events;
}

} // namespace legends::llm
