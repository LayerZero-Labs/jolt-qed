#!/usr/bin/env python3
"""Generate a random RV64IMAC guest for the difftest harness.

    gen-random.py SEED [LENGTH [MIX]] > guest.S

The guest installs a trap handler, sets every integer register except x0, s0
and s1 to a random value, then runs LENGTH random items and exits through
`tohost` with code 0. An item is one instruction or a short sequence (see
below). Memory accesses are aligned and stay inside a 256-byte random buffer
that s0 points to (s1 points 64 bytes into it); s0 and s1 are never written.
Control flow only goes forwards, and the guest stays in M-mode with
mstatus.MPRV clear, so every guest runs straight through. The handler returns
past an ECALL from M-mode and exits with code 2 on any other trap, so a guest
that does not run straight through cannot pass for one that does. The same
SEED, LENGTH and MIX always give the same guest.

MIX chooses what the items are. In both mixes about 8% of items are a forward
branch or jump to a label one to three items ahead: a conditional branch,
C.BEQZ or C.BNEZ, JAL or C.J, or JALR after an `la` of the target.

base    (default) otherwise one instruction from RV64I, M, A, C and Zicsr:
        arithmetic and logic, loads and stores, AMOs and single LR or SC
        instructions, and all six CSR instructions on mscratch, which both
        simulators treat as a plain read/write register. Nothing traps.
system  weighted towards the machine-mode system state: all six CSR
        instructions on mstatus, mscratch, mepc, mcause and mtval with random
        operands, reads of mtvec and writes of its MODE field, ECALL, MRET on
        its own (to the next instruction, through mepc), and LR ... SC
        sequences that mostly reuse the LR's address and width. The rest are
        base instructions. Each mstatus instruction is followed by setting
        MPP to M and clearing MPRV, and each lone MRET is preceded by setting
        MPP to M, so that MRET returns to M-mode on a model with U-mode too;
        these writes, the MRET sequences and the handler clobber x31.
"""

import random
import sys

REGS = [r for r in range(32) if r not in (8, 9)]          # never write s0, s1
CREGS = list(range(8, 16))                                # x8..x15
CREGS_RD = [r for r in CREGS if r not in (8, 9)]          # x10..x15

R_OPS = ["add", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and",
         "addw", "subw", "sllw", "srlw", "sraw",
         "mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu",
         "mulw", "divw", "divuw", "remw", "remuw"]
I_OPS = ["addi", "slti", "sltiu", "xori", "ori", "andi", "addiw"]
SHIFT_OPS = [("slli", 64), ("srli", 64), ("srai", 64),
             ("slliw", 32), ("srliw", 32), ("sraiw", 32)]
LOADS = [("lb", 1), ("lbu", 1), ("lh", 2), ("lhu", 2), ("lw", 4), ("lwu", 4), ("ld", 8)]
STORES = [("sb", 1), ("sh", 2), ("sw", 4), ("sd", 8)]
AMOS = ["amoswap", "amoadd", "amoxor", "amoand", "amoor",
        "amomin", "amomax", "amominu", "amomaxu"]
CSR_OPS = ["csrrw", "csrrs", "csrrc"]
SYS_CSRS = ["mstatus", "mscratch", "mepc", "mcause", "mtval"]
MIXES = ("base", "system")
BRANCHES = ["beq", "bne", "blt", "bge", "bltu", "bgeu"]
C_ALU = ["c.sub", "c.xor", "c.or", "c.and", "c.subw", "c.addw"]
BUF = 256
# Keep MRET in M-mode and data accesses untranslated: MPP := M, MPRV := 0.
SET_MPP_M = ["li x31, 0x1800", "csrs mstatus, x31"]
RESTORE_MSTATUS = SET_MPP_M + ["li x31, 0x20000", "csrc mstatus, x31"]


def x(r):
    return f"x{r}"


def nz(rng, lo, hi):
    while True:
        v = rng.randint(lo, hi)
        if v:
            return v


class Gen:
    def __init__(self, seed):
        self.rng = random.Random(seed)
        self.labels = 0

    def label(self):
        self.labels += 1
        return f".Lf{self.labels}"

    def straight(self):
        """One instruction that does not change control flow."""
        rng = self.rng
        k = rng.random()
        rd, rs1, rs2 = rng.choice(REGS), rng.randrange(32), rng.randrange(32)
        if k < 0.22:
            return f"{rng.choice(R_OPS)} {x(rd)}, {x(rs1)}, {x(rs2)}"
        if k < 0.32:
            return f"{rng.choice(I_OPS)} {x(rd)}, {x(rs1)}, {rng.randint(-2048, 2047)}"
        if k < 0.38:
            op, w = rng.choice(SHIFT_OPS)
            return f"{op} {x(rd)}, {x(rs1)}, {rng.randrange(w)}"
        if k < 0.41:
            return f"{rng.choice(['lui', 'auipc'])} {x(rd)}, {rng.randrange(1 << 20)}"
        if k < 0.51:
            op, size = rng.choice(LOADS)
            return f"{op} {x(rd)}, {rng.randrange(BUF // size) * size}(s0)"
        if k < 0.60:
            op, size = rng.choice(STORES)
            return f"{op} {x(rs2)}, {rng.randrange(BUF // size) * size}(s0)"
        if k < 0.66:
            width = rng.choice(["w", "d"])
            base = rng.choice(["s0", "s1"])
            return f"{rng.choice(AMOS)}.{width} {x(rd)}, {x(rs2)}, ({base})"
        if k < 0.70:
            op = rng.choice(CSR_OPS)
            if rng.random() < 0.5:
                return f"{op} {x(rd)}, mscratch, {x(rs1)}"
            return f"{op}i {x(rd)}, mscratch, {rng.randrange(32)}"
        if k < 0.74:
            width = rng.choice(["w", "d"])
            base = rng.choice(["s0", "s1"])
            if rng.random() < 0.5:
                return f"lr.{width} {x(rd)}, ({base})"
            return f"sc.{width} {x(rd)}, {x(rs2)}, ({base})"
        return self.compressed()

    def compressed(self):
        rng = self.rng
        k = rng.randrange(13)
        rd = rng.choice([r for r in REGS if r != 0])
        crd, crs2 = rng.choice(CREGS_RD), rng.choice(CREGS)
        if k == 0:
            return f"c.addi {x(rd)}, {nz(rng, -32, 31)}"
        if k == 1:
            return f"c.addiw {x(rd)}, {rng.randint(-32, 31)}"
        if k == 2:
            return f"c.li {x(rd)}, {rng.randint(-32, 31)}"
        if k == 3:
            r = rng.choice([r for r in REGS if r not in (0, 2)])
            imm = rng.choice([rng.randint(1, 31), rng.randint(0xFFFE0, 0xFFFFF)])
            return f"c.lui {x(r)}, {imm}"
        if k == 4:
            return f"c.slli {x(rd)}, {rng.randint(1, 63)}"
        if k == 5:
            return f"{rng.choice(['c.srli', 'c.srai'])} {x(crd)}, {rng.randint(1, 63)}"
        if k == 6:
            return f"c.andi {x(crd)}, {rng.randint(-32, 31)}"
        if k == 7:
            return f"{rng.choice(['c.mv', 'c.add'])} {x(rd)}, {x(rng.randint(1, 31))}"
        if k == 8:
            return f"{rng.choice(C_ALU)} {x(crd)}, {x(crs2)}"
        if k == 9:
            return f"c.lw {x(crd)}, {rng.randrange(32) * 4}(s0)"
        if k == 10:
            return f"c.ld {x(crd)}, {rng.randrange(32) * 8}(s0)"
        if k == 11:
            return f"{rng.choice(['c.sw', 'c.sd'])} {x(crs2)}, 0(s0)"
        return "c.nop"

    def csr(self):
        """A random CSR instruction on one of the CSRs both simulators model,
        as a list of lines.

        mtvec only has its MODE field written, so traps keep reaching the
        handler; its BASE is the handler address throughout. An mstatus
        instruction is followed by RESTORE_MSTATUS."""
        rng = self.rng
        rd, rs1 = rng.choice(REGS), rng.randrange(32)
        op = rng.choice(CSR_OPS)
        if rng.random() < 0.1:
            if rng.random() < 0.5:
                return [f"{rng.choice(['csrrs', 'csrrc'])} {x(rd)}, mtvec, x0"]
            return [f"{rng.choice(['csrrsi', 'csrrci'])} {x(rd)}, mtvec, {rng.randrange(4)}"]
        csr = rng.choice(SYS_CSRS)
        if rng.random() < 0.5:
            line = f"{op} {x(rd)}, {csr}, {x(rs1)}"
        else:
            line = f"{op}i {x(rd)}, {csr}, {rng.randrange(32)}"
        return [line] + (RESTORE_MSTATUS if csr == "mstatus" else [])

    def lrsc(self):
        """LR, up to three other instructions, then SC: usually at the LR's
        address and width, sometimes at the other base or width."""
        rng = self.rng
        width, base = rng.choice(["w", "d"]), rng.choice(["s0", "s1"])
        out = [f"lr.{width} {x(rng.choice(REGS))}, ({base})"]
        for _ in range(rng.randint(0, 3)):
            k = rng.random()
            if k < 0.15:
                out.append("ecall")
            elif k < 0.3:
                op, size = rng.choice(STORES)
                out.append(f"{op} {x(rng.randrange(32))}, {rng.randrange(BUF // size) * size}(s0)")
            else:
                out.append(self.straight())
        if rng.random() < 0.2:
            width = "d" if width == "w" else "w"
        if rng.random() < 0.2:
            base = "s1" if base == "s0" else "s0"
        out.append(f"sc.{width} {x(rng.choice(REGS))}, {x(rng.randrange(32))}, ({base})")
        return out

    def system(self):
        """One item of the system mix, as a list of lines."""
        rng = self.rng
        k = rng.random()
        if k < 0.30:
            return self.csr()
        if k < 0.38:
            return ["ecall"]
        if k < 0.42:
            # MRET to the next instruction, in M-mode: MPP = M, mepc = target.
            lab = self.label()
            return [SET_MPP_M[0], SET_MPP_M[1], f"la x31, {lab}", "csrw mepc, x31", "mret",
                    f"{lab}:"]
        if k < 0.57:
            return self.lrsc()
        return [self.straight()]

    def body(self, length, mix="base"):
        rng = self.rng
        out, pending = [], []          # pending: [label, instructions left]
        for _ in range(length):
            for p in pending:
                p[1] -= 1
            out += [f"{p[0]}:" for p in pending if p[1] < 0]
            pending = [p for p in pending if p[1] >= 0]
            if rng.random() < 0.08:
                lab = self.label()
                pending.append([lab, rng.randint(1, 3)])
                k = rng.randrange(4)
                if k == 0:
                    out.append(f"{rng.choice(BRANCHES)} {x(rng.randrange(32))}, "
                               f"{x(rng.randrange(32))}, {lab}")
                elif k == 1:
                    out.append(f"{rng.choice(['c.beqz', 'c.bnez'])} {x(rng.choice(CREGS))}, {lab}")
                elif k == 2:
                    out.append(f"{rng.choice(['jal ' + x(rng.choice(REGS)) + ',', 'c.j'])} {lab}")
                else:
                    # JALR through a register set to the target.
                    r = rng.choice([r for r in REGS if r != 0])
                    out.append(f"la {x(r)}, {lab}")
                    out.append(f"jalr {x(rng.choice(REGS))}, 0({x(r)})")
            elif mix == "system":
                out += self.system()
            else:
                out.append(self.straight())
        out += [f"{p[0]}:" for p in pending]
        return out


def main():
    if not 2 <= len(sys.argv) <= 4 or (len(sys.argv) == 4 and sys.argv[3] not in MIXES):
        sys.exit(f"usage: gen-random.py SEED [LENGTH [{'|'.join(MIXES)}]]")
    seed = int(sys.argv[1])
    length = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    mix = sys.argv[3] if len(sys.argv) > 3 else "base"
    g = Gen(seed)
    rng = g.rng
    lines = [f"/* Random guest: gen-random.py {seed} {length} {mix} */",
             '#include "common.h"',
             "GUEST_START",
             "  la s0, rbuf",
             "  addi s1, s0, 64"]
    lines += ["  la t0, .Lreturn_handler", "  csrw mtvec, t0"]
    lines += [f"  li {x(r)}, 0x{rng.getrandbits(64):x}" for r in REGS if r != 0]
    lines += ["  " + i if not i.endswith(":") else i for i in g.body(length, mix)]
    lines += ["  GUEST_EXIT(0)"]
    # Trap handler: return past an ECALL from M-mode (mcause 11, 4 bytes);
    # exit with code 2 on any other trap.
    lines += ["  .align 2", ".Lreturn_handler:", "  csrr x31, mcause",
              "  addi x31, x31, -11", "  bnez x31, .Lunexpected_trap",
              "  csrr x31, mepc", "  addi x31, x31, 4", "  csrw mepc, x31", "  mret",
              ".Lunexpected_trap:", "  GUEST_EXIT(2)"]
    lines += ["GUEST_END", "  .data", "  .align 6", "rbuf:"]
    data = [rng.getrandbits(64) for _ in range(BUF // 8)]
    lines += [f"  .dword 0x{v:016x}" for v in data]
    print("\n".join(lines))

if __name__ == "__main__":
    main()
