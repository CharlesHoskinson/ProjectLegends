# Sprint 3 Module Graph - Module Definitions
#
# This file defines the formal module boundaries and allowed dependencies.
# Violations are detected at configure time via ModuleDAG.cmake.

#------------------------------------------------------------------------------
# Module: legends
# Purpose: Embeddable x86 emulation framework with stable C ABI
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_LEGENDS_PUBLIC_INCLUDE "include/legends")
set(LEGENDS_MODULE_LEGENDS_PRIVATE_INCLUDE "src/legends")
set(LEGENDS_MODULE_LEGENDS_TARGET "legends_core")

#------------------------------------------------------------------------------
# Module: pal (Platform Abstraction Layer)
# Purpose: Platform-agnostic interfaces for I/O, audio, timing, input
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_PAL_PUBLIC_INCLUDE "include/pal")
set(LEGENDS_MODULE_PAL_PRIVATE_INCLUDE "src/pal")
set(LEGENDS_MODULE_PAL_TARGET "legends_pal")

#------------------------------------------------------------------------------
# Module: engine
# Purpose: DOSBox-X core with library mode API
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_ENGINE_PUBLIC_INCLUDE "engine/include/dosbox;engine/include/aibox")
set(LEGENDS_MODULE_ENGINE_PRIVATE_INCLUDE "engine/include;engine/src")
set(LEGENDS_MODULE_ENGINE_TARGET "aibox_core")

#------------------------------------------------------------------------------
# Module: ipc (IPC Library — MIT-licensed)
# Purpose: Message serialization, shared memory, named pipe transport
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_IPC_PUBLIC_INCLUDE "include/legends_ipc")
set(LEGENDS_MODULE_IPC_PRIVATE_INCLUDE "src/legends_ipc")
set(LEGENDS_MODULE_IPC_TARGET "legends_ipc")

#------------------------------------------------------------------------------
# Module: proxy (Proxy Library — MIT-licensed)
# Purpose: IPC frontend implementing legends_embed.h C API
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_PROXY_PUBLIC_INCLUDE "include/legends_ipc")
set(LEGENDS_MODULE_PROXY_PRIVATE_INCLUDE "src/legends_proxy")
set(LEGENDS_MODULE_PROXY_TARGET "legends_proxy")

#------------------------------------------------------------------------------
# Module: engine_host (Engine Host — GPL-2.0)
# Purpose: Runs DOSBox-X engine in separate process via IPC
#------------------------------------------------------------------------------
set(LEGENDS_MODULE_ENGINE_HOST_PRIVATE_INCLUDE "src/engine_host")
set(LEGENDS_MODULE_ENGINE_HOST_TARGET "legends_engine_host")

#------------------------------------------------------------------------------
# Dependency Graph (DAG)
#
# legends_core       --> aibox_core     (legends depends on engine)
# legends_pal        --> (leaf)
# aibox_core         --> (leaf)
# legends_ipc        --> (leaf, MIT — no GPL deps)
# legends_proxy      --> legends_ipc    (MIT only)
# legends_engine_host --> legends_core;legends_ipc (GPL + IPC)
#------------------------------------------------------------------------------
set(LEGENDS_DAG_legends_core "aibox_core")
set(LEGENDS_DAG_legends_pal "")
set(LEGENDS_DAG_aibox_core "")
set(LEGENDS_DAG_legends_ipc "")
set(LEGENDS_DAG_legends_proxy "legends_ipc")
set(LEGENDS_DAG_legends_engine_host "legends_core;legends_ipc")

#------------------------------------------------------------------------------
# Public Header Allowlists
# Only these directories can be included cross-module
#------------------------------------------------------------------------------
set(LEGENDS_PUBLIC_HEADERS
    "include/legends"
    "include/pal"
    "include/legends_ipc"
    "engine/include/dosbox"
    "engine/include/aibox"
)

#------------------------------------------------------------------------------
# Forbidden Include Patterns
# These patterns indicate module boundary violations
#------------------------------------------------------------------------------
set(LEGENDS_FORBIDDEN_PATTERNS
    "../src/"           # Public header reaching into private source
    "../../"            # Cross-module private include
    "engine/src/"       # Direct include of engine internals
)
