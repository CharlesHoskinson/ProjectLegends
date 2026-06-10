## ADDED Requirements

### Requirement: Dead code deletion
The system SHALL NOT contain `engine/src/aibox/dosboxx_embed_api.cpp`. This file (2,016 lines) is deprecated, never compiled, and duplicates functionality in `legends_embed_api.cpp`.

#### Scenario: File removed and build succeeds
- **WHEN** `dosboxx_embed_api.cpp` is deleted
- **THEN** the project SHALL build successfully on all 3 CI platforms (Linux, Windows, macOS)

#### Scenario: No references remain
- **WHEN** the file is deleted
- **THEN** no CMakeLists.txt, source file, or header SHALL reference `dosboxx_embed_api`
