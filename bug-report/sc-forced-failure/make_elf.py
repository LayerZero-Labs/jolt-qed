"""Write the SC.W test ELF: python3 make_elf.py out.elf"""

import struct
import sys


def r_type(funct7, rs2, rs1, funct3, rd, opcode):
    return funct7 << 25 | rs2 << 20 | rs1 << 15 | funct3 << 12 | rd << 7 | opcode


def i_type(imm, rs1, funct3, rd, opcode):
    return (imm & 0xFFF) << 20 | rs1 << 15 | funct3 << 12 | rd << 7 | opcode


def s_type(imm, rs2, rs1, funct3, opcode):
    imm &= 0xFFF
    return (imm >> 5) << 25 | rs2 << 20 | rs1 << 15 | funct3 << 12 | (imm & 0x1F) << 7 | opcode


def auipc(rd, imm20):
    return imm20 << 12 | rd << 7 | 0x17


def addi(rd, rs1, imm):
    return i_type(imm, rs1, 0, rd, 0x13)


def slli(rd, rs1, shamt):
    return i_type(shamt, rs1, 1, rd, 0x13)


def or_(rd, rs1, rs2):
    return r_type(0, rs2, rs1, 6, rd, 0x33)


def lw(rd, rs1, imm):
    return i_type(imm, rs1, 2, rd, 0x03)


def sd(rs2, rs1, imm):
    return s_type(imm, rs2, rs1, 3, 0x23)


def sb(rs2, rs1, imm):
    return s_type(imm, rs2, rs1, 0, 0x23)


def lr_w(rd, rs1):
    return r_type(0b00010 << 2, 0, rs1, 2, rd, 0x2F)


def sc_w(rd, rs2, rs1):
    return r_type(0b00011 << 2, rs2, rs1, 2, rd, 0x2F)


JAL_SELF = 0x0000006F  # jal x0, 0

# The program starts at 0x80000000. It uses one word of memory, at address
# A = 0x80000040, just after its code. The ELF fills that word with 0.
# Output: x5 | (x4 << 8), where x4 is SC.W's result (0 = stored) and x5 the
# word at A afterwards. Honest run: 7. If the SC fails: 0x100.
PROGRAM = [
    auipc(1, 0),        # 0x00  x1 = 0x80000000
    addi(1, 1, 0x40),   # 0x04  x1 = A
    lr_w(2, 1),         # 0x08  reserve A
    addi(3, 0, 7),      # 0x0c  x3 = 7
    sc_w(4, 3, 1),      # 0x10  store 7 at A if the reservation holds; x4 = 0 if stored
    lw(5, 1, 0),        # 0x14  x5 = word at A
    auipc(6, 0),        # 0x18  x6 = 0x80000018
    addi(6, 6, -0x38),  # 0x1c  x6 = 0x7fffffe0, the output address
    slli(4, 4, 8),      # 0x20
    or_(5, 5, 4),       # 0x24  x5 = x5 | (x4 << 8)
    sd(5, 6, 0),        # 0x28  output it
    addi(7, 0, 1),      # 0x2c
    sb(7, 6, 0x10),     # 0x30  termination byte (0x7ffffff0) = 1, as SDK guests do
    JAL_SELF,           # 0x34  stop: the PC repeats
]


def make_elf(path, text, entry):
    names = b"\0.text\0.shstrtab\0"
    buf = bytearray(0x1200 + 3 * 64)
    buf[0:16] = b"\x7fELF\x02\x01\x01" + bytes(9)
    struct.pack_into("<HHIQQQIHHHHHH", buf, 16,
                     2, 243, 1, entry, 64, 0x1200, 0, 64, 56, 1, 64, 3, 2)
    struct.pack_into("<IIQQQQQQ", buf, 64,
                     1, 7, 0x1000, 0x80000000, 0x80000000,
                     len(text), len(text), 0x1000)
    buf[0x1000:0x1000 + len(text)] = text
    buf[0x1100:0x1100 + len(names)] = names
    struct.pack_into("<IIQQQQIIQQ", buf, 0x1240,
                     1, 1, 7, 0x80000000, 0x1000, len(text), 0, 0, 4, 0)
    struct.pack_into("<IIQQQQIIQQ", buf, 0x1280,
                     7, 3, 0, 0, 0x1100, len(names), 0, 0, 1, 0)
    with open(path, "wb") as f:
        f.write(buf)


def main():
    text = b"".join(struct.pack("<I", word) for word in PROGRAM)
    text += bytes(0x48 - len(text))  # pad; A = 0x80000040 holds 0
    make_elf(sys.argv[1], text, 0x80000000)


if __name__ == "__main__":
    main()
