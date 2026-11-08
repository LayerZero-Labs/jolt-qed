#!/usr/bin/env python3
"""Generate a random RV64IMAC guest for the difftest harness.

    gen-random.py SEED [LENGTH] > guest.S

The guest sets every integer register except x0, s0 and s1 to a random value,
then runs LENGTH random instructions and exits through `tohost`. The
instructions are drawn from RV64I, M, A, C and Zicsr: arithmetic and logic,
loads and stores, AMOs and LR/SC, forward branches and jumps, and all six CSR
instructions on mscratch, which both simulators treat as a plain read/write
register. Memory accesses are
aligned and stay inside a 256-byte random buffer that s0 points to (s1 points
64 bytes into it); s0 and s1 are never written. There are no other CSR
accesses, traps, misaligned accesses or backward jumps, so every guest runs
straight through. The same SEED always gives the same guest.
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
BRANCHES = ["beq", "bne", "blt", "bge", "bltu", "bgeu"]
C_ALU = ["c.sub", "c.xor", "c.or", "c.and", "c.subw", "c.addw"]
BUF = 256


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

    def body(self, length):
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
            else:
                out.append(self.straight())
        out += [f"{p[0]}:" for p in pending]
        return out


def main():
    seed = int(sys.argv[1])
    length = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    g = Gen(seed)
    rng = g.rng
    lines = [f"/* Random guest: gen-random.py {seed} {length} */",
             '#include "common.h"',
             "GUEST_START",
             "  la s0, rbuf",
             "  addi s1, s0, 64"]
    lines += [f"  li {x(r)}, 0x{rng.getrandbits(64):x}" for r in REGS if r != 0]
    lines += ["  " + i if not i.endswith(":") else i for i in g.body(length)]
    lines += ["  GUEST_EXIT(0)", "GUEST_END",
              "  .data", "  .align 6", "rbuf:"]
    data = [rng.getrandbits(64) for _ in range(BUF // 8)]
    lines += [f"  .dword 0x{v:016x}" for v in data]
    print("\n".join(lines))


if __name__ == "__main__":
    main()
