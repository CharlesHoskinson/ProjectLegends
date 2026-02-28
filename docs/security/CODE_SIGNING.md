# Project Legends -- Code Signing Runbook

Procedures for signing release binaries on all three platforms.

---

## Windows: Authenticode

### Certificate procurement

Purchase an EV (Extended Validation) code signing certificate from a CA that
supports hardware tokens (e.g., DigiCert, Sectigo, GlobalSign). EV certs cost
roughly $300-600/year and require identity verification.

EV certificates ship on a hardware token (USB HSM, e.g., SafeNet eToken).
This is required for immediate SmartScreen reputation -- standard OV certs
require accumulating reputation over time.

### Local signing

```bat
signtool.exe sign ^
    /tr http://timestamp.digicert.com ^
    /td sha256 ^
    /fd sha256 ^
    /a ^
    "build\Release\project_legends.exe"
```

Flags:
- `/tr` -- RFC 3161 timestamp server (ensures signature survives cert expiry)
- `/td sha256` -- timestamp digest algorithm
- `/fd sha256` -- file digest algorithm
- `/a` -- auto-select best signing cert from the certificate store

For NSIS installers, sign both the inner executable and the outer installer:

```bat
signtool.exe sign /tr http://timestamp.digicert.com /td sha256 /fd sha256 /a ^
    "build\ProjectLegends-1.0.0-win64.exe"
```

Verify:

```bat
signtool.exe verify /pa /v "build\Release\project_legends.exe"
```

### CI signing (placeholder)

The following step would be added to the Windows job in
`.github/workflows/ci.yml`. Do not add it yet -- requires secrets configuration.

```yaml
# -- Placeholder: Windows Authenticode signing --
# Requires repository secrets:
#   WINDOWS_CERT_PFX_BASE64  - Base64-encoded .pfx (exported from EV token for CI)
#   WINDOWS_CERT_PASSWORD    - PFX password
#
# NOTE: EV certs on hardware tokens cannot be directly exported. Options:
#   1. Use Azure Key Vault or AWS CloudHSM to host the key
#   2. Use a CI-compatible signing service (e.g., Azure SignTool, SignPath)
#   3. Use DigiCert KeyLocker for cloud-based EV signing
#
# - name: Sign Windows binaries
#   if: github.event_name == 'release'
#   shell: pwsh
#   run: |
#     $pfxBytes = [Convert]::FromBase64String($env:WINDOWS_CERT_PFX_BASE64)
#     [IO.File]::WriteAllBytes("$env:RUNNER_TEMP\cert.pfx", $pfxBytes)
#     & signtool.exe sign `
#       /f "$env:RUNNER_TEMP\cert.pfx" `
#       /p $env:WINDOWS_CERT_PASSWORD `
#       /tr http://timestamp.digicert.com `
#       /td sha256 /fd sha256 `
#       build\Release\project_legends.exe
#     Remove-Item "$env:RUNNER_TEMP\cert.pfx"
#   env:
#     WINDOWS_CERT_PFX_BASE64: ${{ secrets.WINDOWS_CERT_PFX_BASE64 }}
#     WINDOWS_CERT_PASSWORD: ${{ secrets.WINDOWS_CERT_PASSWORD }}
```

---

## macOS: codesign + notarization

### Prerequisites

- Apple Developer ID certificate ($99/year Apple Developer Program)
- Certificate type: "Developer ID Application" for standalone distribution
- Xcode command-line tools installed

### Local signing

```sh
codesign --force --options runtime \
    --sign "Developer ID Application: Your Name (TEAMID)" \
    --timestamp \
    build/Release/project_legends

# Verify
codesign --verify --deep --strict --verbose=2 \
    build/Release/project_legends
```

The `--options runtime` flag enables the hardened runtime, which is required
for notarization. If the app loads third-party dylibs (e.g., SDL3), sign those
first, then sign the main binary.

For .app bundles:

```sh
codesign --force --options runtime --deep \
    --sign "Developer ID Application: Your Name (TEAMID)" \
    --timestamp \
    build/Release/ProjectLegends.app
```

For DMG distribution:

```sh
# Create DMG
hdiutil create -volname "ProjectLegends" \
    -srcfolder build/Release/ProjectLegends.app \
    -ov -format UDZO \
    build/ProjectLegends-1.0.0.dmg

# Sign the DMG
codesign --force \
    --sign "Developer ID Application: Your Name (TEAMID)" \
    --timestamp \
    build/ProjectLegends-1.0.0.dmg
```

### Notarization

Apple requires notarization for apps distributed outside the Mac App Store.
Notarization submits the binary to Apple for automated malware scanning.

```sh
# Submit for notarization
xcrun notarytool submit build/ProjectLegends-1.0.0.dmg \
    --apple-id "your@email.com" \
    --team-id "TEAMID" \
    --password "@keychain:AC_PASSWORD" \
    --wait

# Staple the notarization ticket to the DMG
xcrun stapler staple build/ProjectLegends-1.0.0.dmg

# Verify
spctl --assess --type open --context context:primary-signature \
    --verbose=2 build/ProjectLegends-1.0.0.dmg
```

Store the app-specific password in the keychain:

```sh
xcrun notarytool store-credentials "AC_PASSWORD" \
    --apple-id "your@email.com" \
    --team-id "TEAMID" \
    --password "app-specific-password-from-appleid.apple.com"
```

### CI notarization (placeholder)

```yaml
# -- Placeholder: macOS codesign + notarization --
# Requires repository secrets:
#   MACOS_CERT_P12_BASE64     - Base64-encoded .p12 certificate
#   MACOS_CERT_PASSWORD       - P12 password
#   MACOS_NOTARY_APPLE_ID     - Apple ID email
#   MACOS_NOTARY_TEAM_ID      - Apple Developer Team ID
#   MACOS_NOTARY_PASSWORD     - App-specific password
#
# - name: Import signing certificate
#   if: github.event_name == 'release'
#   run: |
#     echo "$MACOS_CERT_P12_BASE64" | base64 --decode > cert.p12
#     security create-keychain -p "" build.keychain
#     security default-keychain -s build.keychain
#     security unlock-keychain -p "" build.keychain
#     security import cert.p12 -k build.keychain -P "$MACOS_CERT_PASSWORD" -T /usr/bin/codesign
#     security set-key-partition-list -S apple-tool:,apple: -s -k "" build.keychain
#     rm cert.p12
#   env:
#     MACOS_CERT_P12_BASE64: ${{ secrets.MACOS_CERT_P12_BASE64 }}
#     MACOS_CERT_PASSWORD: ${{ secrets.MACOS_CERT_PASSWORD }}
#
# - name: Sign and notarize
#   if: github.event_name == 'release'
#   run: |
#     codesign --force --options runtime \
#       --sign "Developer ID Application: Your Name ($MACOS_NOTARY_TEAM_ID)" \
#       --timestamp \
#       build/Release/project_legends
#
#     hdiutil create -volname "ProjectLegends" \
#       -srcfolder build/Release/ -ov -format UDZO \
#       build/ProjectLegends.dmg
#
#     codesign --force \
#       --sign "Developer ID Application: Your Name ($MACOS_NOTARY_TEAM_ID)" \
#       --timestamp \
#       build/ProjectLegends.dmg
#
#     xcrun notarytool submit build/ProjectLegends.dmg \
#       --apple-id "$MACOS_NOTARY_APPLE_ID" \
#       --team-id "$MACOS_NOTARY_TEAM_ID" \
#       --password "$MACOS_NOTARY_PASSWORD" \
#       --wait
#
#     xcrun stapler staple build/ProjectLegends.dmg
#   env:
#     MACOS_NOTARY_APPLE_ID: ${{ secrets.MACOS_NOTARY_APPLE_ID }}
#     MACOS_NOTARY_TEAM_ID: ${{ secrets.MACOS_NOTARY_TEAM_ID }}
#     MACOS_NOTARY_PASSWORD: ${{ secrets.MACOS_NOTARY_PASSWORD }}
```

---

## Linux: GPG signing

### Key setup

Generate a dedicated release signing key (or use an existing one):

```sh
gpg --full-generate-key
# Select: RSA and RSA, 4096 bits, no expiration (or set policy-appropriate expiry)
# Real name: Project Legends Release Signing
# Email: releases@projectlegends.example.com
```

Export the public key for distribution:

```sh
gpg --armor --export "releases@projectlegends.example.com" > projectlegends-release.asc
```

Publish the public key:
- In the repository under `docs/security/projectlegends-release.asc`
- On a public keyserver: `gpg --keyserver keys.openpgp.org --send-keys KEYID`
- On the project website

### Signing releases

```sh
# Sign the tarball (creates .asc detached signature)
gpg --armor --detach-sign \
    --local-user "releases@projectlegends.example.com" \
    build/ProjectLegends-1.0.0-Linux.tar.gz

# Also produce SHA-256 checksum
sha256sum build/ProjectLegends-1.0.0-Linux.tar.gz \
    > build/ProjectLegends-1.0.0-Linux.tar.gz.sha256
```

### Verification

Users verify with:

```sh
gpg --verify ProjectLegends-1.0.0-Linux.tar.gz.asc \
    ProjectLegends-1.0.0-Linux.tar.gz

sha256sum --check ProjectLegends-1.0.0-Linux.tar.gz.sha256
```

### CI signing (placeholder)

```yaml
# -- Placeholder: Linux GPG signing --
# Requires repository secrets:
#   GPG_PRIVATE_KEY_BASE64  - Base64-encoded private key (armor export)
#   GPG_PASSPHRASE          - Key passphrase
#
# - name: Import GPG key
#   if: github.event_name == 'release'
#   run: |
#     echo "$GPG_PRIVATE_KEY_BASE64" | base64 --decode | gpg --batch --import
#   env:
#     GPG_PRIVATE_KEY_BASE64: ${{ secrets.GPG_PRIVATE_KEY_BASE64 }}
#
# - name: Sign release tarball
#   if: github.event_name == 'release'
#   run: |
#     gpg --batch --yes --pinentry-mode loopback \
#       --passphrase "$GPG_PASSPHRASE" \
#       --armor --detach-sign \
#       build/ProjectLegends-*.tar.gz
#
#     sha256sum build/ProjectLegends-*.tar.gz > checksums-linux.sha256
#   env:
#     GPG_PASSPHRASE: ${{ secrets.GPG_PASSPHRASE }}
#
# - name: Upload signatures
#   if: github.event_name == 'release'
#   uses: softprops/action-gh-release@v2
#   with:
#     files: |
#       build/ProjectLegends-*.tar.gz.asc
#       checksums-linux.sha256
```

---

## Cost summary

| Platform | Certificate | Annual cost | Notes |
|---|---|---|---|
| Windows | EV code signing (DigiCert/Sectigo) | $300-600 | Hardware token required; cloud HSM option for CI |
| macOS | Apple Developer ID | $99 | Includes notarization |
| Linux | GPG key | Free | Self-managed key infrastructure |

---

## Checklist before first signed release

- [ ] Procure Windows EV code signing certificate
- [ ] Enroll in Apple Developer Program; create Developer ID Application cert
- [ ] Generate GPG release signing key; publish public key
- [ ] Configure GitHub repository secrets for all three platforms
- [ ] Add signing steps to `.github/workflows/ci.yml` (adapt placeholders above)
- [ ] Test signed builds on each platform before tagging v1.0.0
- [ ] Document public key fingerprints in project README or website
