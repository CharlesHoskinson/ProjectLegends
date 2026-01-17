/**
 * @file cpu_context.h
 * @brief CPU state encapsulation.
 *
 * Replaces global CPU_Regs and related structures with
 * a clean, testable interface.
 *
 * Requirements implemented:
 * - REQ-GSE-001: Encapsulate all mutable state
 * - REQ-GSE-005: Dependency injection for subsystem access
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include <cstdint>
#include <array>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// CPU Flags (EFLAGS)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief CPU flags register (EFLAGS).
 *
 * Provides structured access to x86 EFLAGS register bits.
 * Can pack/unpack to 32-bit EFLAGS format.
 */
struct CpuFlags {
    bool carry = false;           ///< CF - Carry flag
    bool parity = false;          ///< PF - Parity flag
    bool auxiliary = false;       ///< AF - Auxiliary carry flag
    bool zero = false;            ///< ZF - Zero flag
    bool sign = false;            ///< SF - Sign flag
    bool trap = false;            ///< TF - Trap flag
    bool interrupt = true;        ///< IF - Interrupt enable flag
    bool direction = false;       ///< DF - Direction flag
    bool overflow = false;        ///< OF - Overflow flag
    uint8_t iopl = 0;             ///< IOPL - I/O privilege level (2 bits)
    bool nested_task = false;     ///< NT - Nested task flag
    bool resume = false;          ///< RF - Resume flag
    bool virtual_8086 = false;    ///< VM - Virtual 8086 mode
    bool alignment_check = false; ///< AC - Alignment check
    bool virtual_interrupt = false;         ///< VIF - Virtual interrupt flag
    bool virtual_interrupt_pending = false; ///< VIP - Virtual interrupt pending
    bool cpuid_available = false; ///< ID - CPUID available

    /**
     * @brief Pack flags into 32-bit EFLAGS format.
     * @return EFLAGS value
     */
    [[nodiscard]] uint32_t to_eflags() const noexcept {
        uint32_t eflags = 0x0002;  // Reserved bit 1 always set
        if (carry)      eflags |= (1u << 0);
        if (parity)     eflags |= (1u << 2);
        if (auxiliary)  eflags |= (1u << 4);
        if (zero)       eflags |= (1u << 6);
        if (sign)       eflags |= (1u << 7);
        if (trap)       eflags |= (1u << 8);
        if (interrupt)  eflags |= (1u << 9);
        if (direction)  eflags |= (1u << 10);
        if (overflow)   eflags |= (1u << 11);
        eflags |= (static_cast<uint32_t>(iopl & 0x03) << 12);
        if (nested_task) eflags |= (1u << 14);
        if (resume)      eflags |= (1u << 16);
        if (virtual_8086) eflags |= (1u << 17);
        if (alignment_check) eflags |= (1u << 18);
        if (virtual_interrupt) eflags |= (1u << 19);
        if (virtual_interrupt_pending) eflags |= (1u << 20);
        if (cpuid_available) eflags |= (1u << 21);
        return eflags;
    }

    /**
     * @brief Unpack from 32-bit EFLAGS.
     * @param eflags EFLAGS value to unpack
     */
    void from_eflags(uint32_t eflags) noexcept {
        carry      = (eflags & (1u << 0)) != 0;
        parity     = (eflags & (1u << 2)) != 0;
        auxiliary  = (eflags & (1u << 4)) != 0;
        zero       = (eflags & (1u << 6)) != 0;
        sign       = (eflags & (1u << 7)) != 0;
        trap       = (eflags & (1u << 8)) != 0;
        interrupt  = (eflags & (1u << 9)) != 0;
        direction  = (eflags & (1u << 10)) != 0;
        overflow   = (eflags & (1u << 11)) != 0;
        iopl       = static_cast<uint8_t>((eflags >> 12) & 0x03);
        nested_task = (eflags & (1u << 14)) != 0;
        resume      = (eflags & (1u << 16)) != 0;
        virtual_8086 = (eflags & (1u << 17)) != 0;
        alignment_check = (eflags & (1u << 18)) != 0;
        virtual_interrupt = (eflags & (1u << 19)) != 0;
        virtual_interrupt_pending = (eflags & (1u << 20)) != 0;
        cpuid_available = (eflags & (1u << 21)) != 0;
    }

    /**
     * @brief Reset to default state.
     */
    void reset() noexcept {
        carry = false;
        parity = false;
        auxiliary = false;
        zero = false;
        sign = false;
        trap = false;
        interrupt = true;  // Interrupts enabled by default
        direction = false;
        overflow = false;
        iopl = 0;
        nested_task = false;
        resume = false;
        virtual_8086 = false;
        alignment_check = false;
        virtual_interrupt = false;
        virtual_interrupt_pending = false;
        cpuid_available = false;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Segment Register
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Segment register with cached descriptor.
 *
 * Contains both the visible selector value and the hidden
 * descriptor cache (base, limit, access rights).
 */
struct SegmentRegister {
    uint16_t selector = 0;    ///< Segment selector value
    uint32_t base = 0;        ///< Cached base address
    uint32_t limit = 0xFFFF;  ///< Cached limit (default 64KB)
    uint32_t access = 0;      ///< Access rights

    /**
     * @brief Check if segment is valid (present).
     * @return true if present bit is set
     */
    [[nodiscard]] bool is_valid() const noexcept {
        // Present bit is bit 7 of access byte
        return (access & 0x80) != 0;
    }

    /**
     * @brief Check if segment is code segment.
     * @return true if code segment
     */
    [[nodiscard]] bool is_code() const noexcept {
        // Code segment has bit 3 of type field set
        return (access & 0x08) != 0;
    }

    /**
     * @brief Check if segment is writable (data) or readable (code).
     * @return true if accessible for read/write as appropriate
     */
    [[nodiscard]] bool is_accessible() const noexcept {
        if (is_code()) {
            // Code segment: check readable bit (bit 1)
            return (access & 0x02) != 0;
        } else {
            // Data segment: check writable bit (bit 1)
            return (access & 0x02) != 0;
        }
    }

    /**
     * @brief Get descriptor privilege level (DPL).
     * @return DPL value (0-3)
     */
    [[nodiscard]] uint8_t dpl() const noexcept {
        return static_cast<uint8_t>((access >> 5) & 0x03);
    }

    /**
     * @brief Reset to real mode defaults.
     * @param default_selector Initial selector value
     */
    void reset(uint16_t default_selector = 0) noexcept {
        selector = default_selector;
        base = static_cast<uint32_t>(default_selector) << 4;
        limit = 0xFFFF;
        access = 0x0093;  // Present, DPL=0, data, writable
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// CPU Mode
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief CPU operating mode.
 */
enum class CpuMode {
    Real,           ///< 16-bit real mode
    Protected16,    ///< 16-bit protected mode
    Protected32,    ///< 32-bit protected mode
    Virtual8086     ///< Virtual 8086 mode
};

// ─────────────────────────────────────────────────────────────────────────────
// CPU Context
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief CPU state context.
 *
 * Contains all CPU registers, flags, and mode state.
 * Replaces global reg, Segs, cpu.* variables.
 *
 * ## Responsibilities
 * - Store all CPU register state
 * - Provide mode and address size queries
 * - Support reset to initial state
 *
 * ## Dependencies
 * - None (leaf subsystem)
 *
 * ## Thread Safety
 * Not thread-safe. Access from emulation thread only.
 */
class CpuContext {
public:
    // ─────────────────────────────────────────────────────────────────────────
    // General Purpose Registers (using anonymous unions for aliasing)
    // Anonymous structs are a common extension for register aliasing in emulators
    // ─────────────────────────────────────────────────────────────────────────

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#endif
#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4201) // nameless struct/union
#endif

    union {
        uint32_t eax = 0;
        struct { uint16_t ax; uint16_t eax_hi_; };
        struct { uint8_t al; uint8_t ah; uint16_t eax_top_; };
    };

    union {
        uint32_t ebx = 0;
        struct { uint16_t bx; uint16_t ebx_hi_; };
        struct { uint8_t bl; uint8_t bh; uint16_t ebx_top_; };
    };

    union {
        uint32_t ecx = 0;
        struct { uint16_t cx; uint16_t ecx_hi_; };
        struct { uint8_t cl; uint8_t ch; uint16_t ecx_top_; };
    };

    union {
        uint32_t edx = 0;
        struct { uint16_t dx; uint16_t edx_hi_; };
        struct { uint8_t dl; uint8_t dh; uint16_t edx_top_; };
    };

    union {
        uint32_t esi = 0;
        struct { uint16_t si; uint16_t esi_hi_; };
    };

    union {
        uint32_t edi = 0;
        struct { uint16_t di; uint16_t edi_hi_; };
    };

    union {
        uint32_t ebp = 0;
        struct { uint16_t bp; uint16_t ebp_hi_; };
    };

    union {
        uint32_t esp = 0;
        struct { uint16_t sp; uint16_t esp_hi_; };
    };

    // ─────────────────────────────────────────────────────────────────────────
    // Instruction Pointer and Flags
    // ─────────────────────────────────────────────────────────────────────────

    union {
        uint32_t eip = 0;
        struct { uint16_t ip; uint16_t eip_hi_; };
    };

#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif
#ifdef _MSC_VER
#pragma warning(pop)
#endif

    CpuFlags flags;

    // ─────────────────────────────────────────────────────────────────────────
    // Segment Registers
    // ─────────────────────────────────────────────────────────────────────────

    SegmentRegister cs;  ///< Code segment
    SegmentRegister ds;  ///< Data segment
    SegmentRegister es;  ///< Extra segment
    SegmentRegister fs;  ///< FS segment
    SegmentRegister gs;  ///< GS segment
    SegmentRegister ss;  ///< Stack segment

    // ─────────────────────────────────────────────────────────────────────────
    // Control Registers
    // ─────────────────────────────────────────────────────────────────────────

    uint32_t cr0 = 0;    ///< Control register 0 (PE, PG, etc.)
    uint32_t cr2 = 0;    ///< Page fault linear address
    uint32_t cr3 = 0;    ///< Page directory base register
    uint32_t cr4 = 0;    ///< Control register 4 (extensions)

    // ─────────────────────────────────────────────────────────────────────────
    // Debug Registers
    // ─────────────────────────────────────────────────────────────────────────

    std::array<uint32_t, 4> dr = {0, 0, 0, 0};  ///< DR0-DR3 (breakpoints)
    uint32_t dr6 = 0;    ///< Debug status register
    uint32_t dr7 = 0;    ///< Debug control register

    // ─────────────────────────────────────────────────────────────────────────
    // Descriptor Tables
    // ─────────────────────────────────────────────────────────────────────────

    struct DescriptorTable {
        uint32_t base = 0;
        uint16_t limit = 0;
    };

    DescriptorTable gdtr;  ///< Global descriptor table register
    DescriptorTable idtr;  ///< Interrupt descriptor table register
    DescriptorTable ldtr;  ///< Local descriptor table register
    uint16_t tr = 0;       ///< Task register

    // ─────────────────────────────────────────────────────────────────────────
    // Mode and State
    // ─────────────────────────────────────────────────────────────────────────

    CpuMode mode = CpuMode::Real;

    /**
     * @brief CPU configuration.
     */
    struct Config {
        bool nmi_enabled = true;         ///< NMI enabled
        bool fpu_enabled = true;         ///< FPU present
        uint32_t cycles_per_ms = 3000;   ///< CPU speed
        int rep_limit = 0;               ///< REP instruction limit (0 = none)
    } config;

    // ─────────────────────────────────────────────────────────────────────────
    // Instruction Execution State
    // ─────────────────────────────────────────────────────────────────────────

    bool halted = false;           ///< CPU in HLT state
    bool in_interrupt = false;     ///< Currently handling interrupt
    uint8_t current_prefix = 0;    ///< Current instruction prefix

    // ─────────────────────────────────────────────────────────────────────────
    // Methods
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Default constructor - creates uninitialized context.
     */
    CpuContext() = default;

    /**
     * @brief Reset CPU to initial (power-on) state.
     */
    void reset() noexcept {
        // General purpose registers
        eax = ebx = ecx = edx = 0;
        esi = edi = ebp = esp = 0;
        eip = 0xFFF0;  // Start at reset vector

        // Flags
        flags.reset();

        // Segment registers - real mode defaults
        cs.reset(0xF000);
        cs.base = 0xFFFF0000;  // Special reset value
        ds.reset(0);
        es.reset(0);
        fs.reset(0);
        gs.reset(0);
        ss.reset(0);

        // Control registers
        cr0 = 0x60000010;  // ET bit set (387 present)
        cr2 = cr3 = cr4 = 0;

        // Debug registers
        dr.fill(0);
        dr6 = 0xFFFF0FF0;
        dr7 = 0x00000400;

        // Descriptor tables
        gdtr = {0, 0};
        idtr = {0, 0x03FF};  // Real mode default
        ldtr = {0, 0};
        tr = 0;

        // Mode
        mode = CpuMode::Real;

        // State
        halted = false;
        in_interrupt = false;
        current_prefix = 0;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Mode Queries
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Check if in protected mode.
     * @return true if PE bit in CR0 is set
     */
    [[nodiscard]] bool is_protected_mode() const noexcept {
        return (cr0 & 0x01) != 0;
    }

    /**
     * @brief Check if paging is enabled.
     * @return true if PG bit in CR0 is set
     */
    [[nodiscard]] bool is_paging_enabled() const noexcept {
        return (cr0 & 0x80000000) != 0;
    }

    /**
     * @brief Check if in virtual 8086 mode.
     * @return true if VM flag is set
     */
    [[nodiscard]] bool is_v86_mode() const noexcept {
        return flags.virtual_8086;
    }

    /**
     * @brief Check if in real mode.
     * @return true if not in protected mode
     */
    [[nodiscard]] bool is_real_mode() const noexcept {
        return !is_protected_mode();
    }

    /**
     * @brief Get current privilege level (CPL).
     * @return CPL (0-3)
     */
    [[nodiscard]] uint8_t cpl() const noexcept {
        return static_cast<uint8_t>(cs.selector & 0x03);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Address and Operand Size
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get default address size (16 or 32 bit).
     * @return Address size in bits
     */
    [[nodiscard]] int default_address_size() const noexcept {
        if (is_real_mode() || is_v86_mode()) {
            return 16;
        }
        // In protected mode, check D bit of CS descriptor
        return (cs.access & 0x4000) ? 32 : 16;
    }

    /**
     * @brief Get default operand size (16 or 32 bit).
     * @return Operand size in bits
     */
    [[nodiscard]] int default_operand_size() const noexcept {
        return default_address_size();  // Same as address size by default
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Address Calculation
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Calculate linear address from segment:offset.
     * @param seg Segment register
     * @param offset Offset within segment
     * @return Linear address
     */
    [[nodiscard]] uint32_t linear_address(
        const SegmentRegister& seg,
        uint32_t offset) const noexcept {
        return seg.base + offset;
    }

    /**
     * @brief Calculate physical address (linear address for now).
     *
     * @note Paging translation is not implemented here.
     * @param seg Segment register
     * @param offset Offset within segment
     * @return Physical address
     */
    [[nodiscard]] uint32_t physical_address(
        const SegmentRegister& seg,
        uint32_t offset) const noexcept {
        // TODO: Add paging translation when is_paging_enabled()
        return linear_address(seg, offset);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Stack Operations
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get stack pointer value based on mode.
     * @return SP or ESP depending on stack segment size
     */
    [[nodiscard]] uint32_t stack_pointer() const noexcept {
        // TODO: Check stack segment B bit
        return esp;
    }

    /**
     * @brief Get stack segment base address.
     * @return SS base address
     */
    [[nodiscard]] uint32_t stack_base() const noexcept {
        return ss.base;
    }
};

} // namespace legends
