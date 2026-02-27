// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Windows update checker: WinHTTP-based manifest fetch.

#include "app/update_checker.h"

#include <memory>

#if defined(_WIN32)

#ifndef WIN32_LEAN_AND_MEAN
#  define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <winhttp.h>

#pragma comment(lib, "winhttp.lib")

namespace legends {

/// Windows-specific update checker using WinHTTP.
class WinUpdateChecker : public UpdateChecker {
protected:
    std::string fetchManifest() override {
        static const wchar_t* kHost = L"api.github.com";
        static const wchar_t* kPath = L"/repos/user/ProjectLegends/releases/latest";

        HINTERNET session = WinHttpOpen(
            L"ProjectLegends-UpdateChecker/1.0",
            WINHTTP_ACCESS_TYPE_DEFAULT_PROXY,
            WINHTTP_NO_PROXY_NAME,
            WINHTTP_NO_PROXY_BYPASS, 0);
        if (!session) return {};

        HINTERNET connect = WinHttpConnect(session, kHost,
            INTERNET_DEFAULT_HTTPS_PORT, 0);
        if (!connect) {
            WinHttpCloseHandle(session);
            return {};
        }

        HINTERNET request = WinHttpOpenRequest(connect, L"GET", kPath,
            nullptr, WINHTTP_NO_REFERER,
            WINHTTP_DEFAULT_ACCEPT_TYPES,
            WINHTTP_FLAG_SECURE);
        if (!request) {
            WinHttpCloseHandle(connect);
            WinHttpCloseHandle(session);
            return {};
        }

        // Set timeout (10 seconds)
        DWORD timeout = 10000;
        WinHttpSetOption(request, WINHTTP_OPTION_RECEIVE_TIMEOUT,
            &timeout, sizeof(timeout));

        if (!WinHttpSendRequest(request, WINHTTP_NO_ADDITIONAL_HEADERS, 0,
                                WINHTTP_NO_REQUEST_DATA, 0, 0, 0) ||
            !WinHttpReceiveResponse(request, nullptr)) {
            WinHttpCloseHandle(request);
            WinHttpCloseHandle(connect);
            WinHttpCloseHandle(session);
            return {};
        }

        std::string result;
        DWORD bytes_available = 0;
        while (WinHttpQueryDataAvailable(request, &bytes_available) && bytes_available > 0) {
            std::string chunk(bytes_available, '\0');
            DWORD bytes_read = 0;
            if (WinHttpReadData(request, chunk.data(), bytes_available, &bytes_read)) {
                result.append(chunk.data(), bytes_read);
            }
        }

        WinHttpCloseHandle(request);
        WinHttpCloseHandle(connect);
        WinHttpCloseHandle(session);

        return result;
    }
};

/// Factory function to create the platform-specific update checker.
std::unique_ptr<UpdateChecker> createPlatformUpdateChecker() {
    return std::make_unique<WinUpdateChecker>();
}

} // namespace legends

#endif // _WIN32
