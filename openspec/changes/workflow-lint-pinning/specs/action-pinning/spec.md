## ADDED Requirements

### Requirement: Third-party actions are pinned to commit SHAs
Every `uses:` reference to a third-party action (any owner other than `actions`, excluding local `./` references) SHALL pin a full-length 40-hex commit SHA followed by a comment naming the release tag the SHA was resolved from. First-party `actions/*` references MAY remain on major version tags.

#### Scenario: Existing third-party action pinned
- **WHEN** this change lands
- **THEN** `codecov/codecov-action` in `ci.yml` references the commit SHA that its current `v4` tag resolves to, with a trailing `# vX.Y.Z` comment

#### Scenario: Mutable tag re-pointed upstream
- **WHEN** a third-party action's release tag is moved to a different commit after the pin lands
- **THEN** the workflows continue to execute the pinned commit; the re-point has no effect until a reviewed update PR changes the SHA

### Requirement: Lint lane enforces the pin policy
The lint lane SHALL fail when any workflow file contains a third-party `uses:` reference that is not a full-length commit SHA. Local references (`./...`) and first-party `actions/*` references SHALL be exempt.

#### Scenario: Unpinned third-party action introduced
- **WHEN** a PR adds a `uses: someowner/someaction@v2` reference
- **THEN** the lint lane fails, naming the file and the reference

#### Scenario: Local reusable workflow reference
- **WHEN** a job uses a same-repo reusable workflow (`uses: ./.github/workflows/<file>.yml`)
- **THEN** the pin check passes — local references are pinned to the caller's commit by construction

### Requirement: Pins land only together with an automated updater
A SHA pin SHALL NOT be introduced without an active updater configuration. `.github/dependabot.yml` SHALL declare the `github-actions` package ecosystem on a recurring schedule, and SHALL land in the same change as the first pin.

#### Scenario: Updater proposes a pin bump
- **WHEN** a pinned third-party action publishes a new release
- **THEN** dependabot opens a PR updating the commit SHA and its trailing version comment, and the PR runs through the same CI as any other change

#### Scenario: Pin without updater rejected
- **WHEN** a change proposes SHA-pinning an action while no updater configuration exists or the change removes it
- **THEN** review rejects the change — an unmaintained pin is stale-pin rot, worse than a tracked tag

#### Scenario: Future third-party action arrives
- **WHEN** a later change adds a new third-party action (e.g. compiler-cache actions under R14)
- **THEN** the pin check forces it to land SHA-pinned, and the existing dependabot config covers it with no further setup
