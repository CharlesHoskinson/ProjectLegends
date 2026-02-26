// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Project Legends — entry point for the interactive emulator.

#include "app/application.h"

int main(int /*argc*/, char* /*argv*/[]) {
    legends::Application app;

    auto code = app.init();
    if (code != legends::ExitCode::Success) {
        return static_cast<int>(code);
    }

    return static_cast<int>(app.run());
}
