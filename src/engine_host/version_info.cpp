// SPDX-License-Identifier: GPL-2.0-or-later
#include <cstdio>
#include <legends/legends_embed.h>

namespace legends::engine_host {

void print_version() {
    uint32_t major = 0, minor = 0, patch = 0;
    legends_get_api_version(&major, &minor, &patch);
    std::printf("legends_engine_host %u.%u.%u\n", major, minor, patch);
    std::printf("Licensed under GNU General Public License v2.0\n");
    std::printf("Based on DOSBox-X by the DOSBox-X Team\n");
}

} // namespace legends::engine_host
