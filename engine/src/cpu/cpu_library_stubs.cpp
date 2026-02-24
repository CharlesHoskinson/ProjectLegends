/**
 * @file cpu_library_stubs.cpp
 * @brief Stubs for DOSBox-X symbols needed by the CPU core in library mode.
 *
 * The CPU interpretive core (core_normal.cpp, flags.cpp, paging.cpp, etc.)
 * references functions and globals from parts of DOSBox-X we don't compile
 * in library mode (FPU, I/O subsystem, PIC, memory paging, etc.).
 *
 * This file provides minimal implementations so the CPU core links.
 * Real implementations can be added as we integrate more subsystems.
 */

#ifdef DOSBOX_LIBRARY_MODE

#include "dosbox.h"
#include "cpu.h"
#include "fpu.h"
#include "paging.h"
#include "callback.h"
#include "logging.h"
#include "mem.h"

#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

/* ── Logging ──────────────────────────────────────────────────────── */

void LOG::operator()(char const* fmt, ...) {
    (void)fmt;
}

void DEBUG_ShowMsg(char const* fmt, ...) {
    (void)fmt;
}

void E_Exit(const char* format, ...) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stderr, format, ap);
    va_end(ap);
    fprintf(stderr, "\n");
#ifdef DOSBOX_LIBRARY_MODE
    throw std::runtime_error("E_Exit");
#else
    abort();
#endif
}

/* ── PIC ──────────────────────────────────────────────────────────── */

Bitu PIC_IRQCheck = 0;
Bitu PIC_Ticks = 0;

/* ── GFX / UI ─────────────────────────────────────────────────────── */

void GFX_SetTitle(int32_t, int, Bits, bool) { }
void DOSBOX_RunMachine() { }
void On_Software_CPU_Reset() { }

bool dos_kernel_disabled = true;

/* ── FPU stubs ────────────────────────────────────────────────────── */

FPU_rec fpu = {};

void FPU_ESC0_Normal(Bitu) { }
void FPU_ESC0_EA(Bitu, PhysPt) { }
void FPU_ESC1_Normal(Bitu) { }
void FPU_ESC1_EA(Bitu, PhysPt, bool) { }
void FPU_ESC2_Normal(Bitu) { }
void FPU_ESC2_EA(Bitu, PhysPt) { }
void FPU_ESC3_Normal(Bitu) { }
void FPU_ESC3_EA(Bitu, PhysPt) { }
void FPU_ESC4_Normal(Bitu) { }
void FPU_ESC4_EA(Bitu, PhysPt) { }
void FPU_ESC5_Normal(Bitu) { }
void FPU_ESC5_EA(Bitu, PhysPt, bool) { }
void FPU_ESC6_Normal(Bitu) { }
void FPU_ESC6_EA(Bitu, PhysPt) { }
void FPU_ESC7_Normal(Bitu) { }
void FPU_ESC7_EA(Bitu, PhysPt) { }

/* ── CPU SSE/MSR stubs ────────────────────────────────────────────── */

bool CPU_RDMSR() { return false; }
bool CPU_WRMSR() { return false; }
bool CPU_SYSENTER() { return false; }
bool CPU_SYSEXIT() { return false; }
bool CPU_LDMXCSR(PhysPt) { return false; }
bool CPU_STMXCSR(PhysPt) { return false; }
void CPU_CMPXCHG8B(PhysPt) { }
void CPU_FXSAVE(PhysPt) { }
void CPU_FXRSTOR(PhysPt) { }

Bits CPU_Core_Full_Run(void) { return CBRET_NONE; }

/* ── Memory access (uses context-aware MemBase) ───────────────────── */

static uint8_t* get_mem_base() {
    return MemBase;
}

static size_t get_mem_size() {
    return MemSize;
}

uint8_t mem_readb(PhysPt addr) {
    uint8_t* base = get_mem_base();
    if (base && addr < get_mem_size()) return base[addr];
    return 0xFF;
}

uint16_t mem_readw(PhysPt addr) {
    uint8_t* base = get_mem_base();
    if (base && (addr + 1) < get_mem_size()) {
        uint16_t val;
        memcpy(&val, base + addr, 2);
        return val;
    }
    return 0xFFFF;
}

uint32_t mem_readd(PhysPt addr) {
    uint8_t* base = get_mem_base();
    if (base && (addr + 3) < get_mem_size()) {
        uint32_t val;
        memcpy(&val, base + addr, 4);
        return val;
    }
    return 0xFFFFFFFF;
}

void mem_writeb(PhysPt addr, uint8_t val) {
    uint8_t* base = get_mem_base();
    if (base && addr < get_mem_size()) base[addr] = val;
}

void mem_writew(PhysPt addr, uint16_t val) {
    uint8_t* base = get_mem_base();
    if (base && (addr + 1) < get_mem_size()) memcpy(base + addr, &val, 2);
}

void mem_writed(PhysPt addr, uint32_t val) {
    uint8_t* base = get_mem_base();
    if (base && (addr + 3) < get_mem_size()) memcpy(base + addr, &val, 4);
}

uint16_t mem_unalignedreadw(PhysPt addr) { return mem_readw(addr); }
uint32_t mem_unalignedreadd(PhysPt addr) { return mem_readd(addr); }
void mem_unalignedwritew(PhysPt addr, uint16_t val) { mem_writew(addr, val); }
void mem_unalignedwrited(PhysPt addr, uint32_t val) { mem_writed(addr, val); }

/* ── Paging stubs ─────────────────────────────────────────────────── */

Bitu MEM_TotalPages() {
    return get_mem_size() / MEM_PAGESIZE;
}

/* Stub page handler for flat memory model */
static PageHandler stub_page_handler;

PageHandler* MEM_GetPageHandler(Bitu) {
    return &stub_page_handler;
}

/* ── I/O stubs ────────────────────────────────────────────────────── */

uint8_t  IO_ReadB(Bitu)      { return 0xFF; }
uint16_t IO_ReadW(Bitu)      { return 0xFFFF; }
uint32_t IO_ReadD(Bitu)      { return 0xFFFFFFFF; }
void     IO_WriteB(Bitu, uint8_t)  { }
void     IO_WriteW(Bitu, uint16_t) { }
void     IO_WriteD(Bitu, uint32_t) { }

#endif /* DOSBOX_LIBRARY_MODE */
