# Usage: python3 make_elf.py OUT.elf
# Program at 0x80000000:
#   addi x6, x0, 1
#   slli x6, x6, 32      x6 = 0x1_0000_0000 (2 GiB above RAM_START)
#   addi x5, x0, 7
#   sd   x5, 0(x6)       store 7 at 0x1_0000_0000
#   jal  x0, 0           self-jump ends the trace
import struct
import sys

def i_type(opcode, funct3, rd, rs1, imm):
    return ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode

def s_type(opcode, funct3, rs1, rs2, imm):
    imm &= 0xFFF
    return ((imm >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | ((imm & 0x1F) << 7) | opcode

instructions = [
    i_type(0x13, 0, 6, 0, 1),        # addi x6, x0, 1
    i_type(0x13, 1, 6, 6, 32),       # slli x6, x6, 32
    i_type(0x13, 0, 5, 0, 7),        # addi x5, x0, 7
    s_type(0x23, 3, 6, 5, 0),        # sd x5, 0(x6)
    0x0000006F,                      # jal x0, 0
]
for word in instructions:
    print(hex(word))
text = b"".join(struct.pack("<I", x) for x in instructions)
names = b"\0.text\0.shstrtab\0"
buf = bytearray(0x1200 + 3 * 64)
buf[0:16] = b"\x7fELF\x02\x01\x01" + bytes(9)
struct.pack_into("<HHIQQQIHHHHHH", buf, 16,
                 2, 243, 1, 0x80000000, 64, 0x1200, 0,
                 64, 56, 1, 64, 3, 2)
struct.pack_into("<IIQQQQQQ", buf, 64,
                 1, 5, 0x1000, 0x80000000, 0x80000000,
                 len(text), len(text), 0x1000)
buf[0x1000:0x1000 + len(text)] = text
buf[0x1100:0x1100 + len(names)] = names
struct.pack_into("<IIQQQQIIQQ", buf, 0x1200 + 64,
                 1, 1, 6, 0x80000000, 0x1000, len(text),
                 0, 0, 4, 0)
struct.pack_into("<IIQQQQIIQQ", buf, 0x1200 + 128,
                 7, 3, 0, 0, 0x1100, len(names),
                 0, 0, 1, 0)
with open(sys.argv[1], "wb") as output:
    output.write(buf)
