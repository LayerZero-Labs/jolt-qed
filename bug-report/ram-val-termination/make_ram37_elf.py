import struct
import sys

instructions = [
    0x00000097,  # auipc x1, 0
    0xFF008093,  # addi x1, x1, -16
    0x00100113,  # addi x2, x0, 1
    0x0020B023,  # sd x2, 0(x1)
    0x0000B183,  # ld x3, 0(x1)
    0x0000006F,  # jal x0, 0
]
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
