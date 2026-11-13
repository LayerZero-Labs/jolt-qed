//! A hand-assembled RV64 ELF with a `.text` and a `.data` section, in the
//! shape of the test builder in jolt-program's `image/elf.rs` (no program
//! headers; both Jolt's decoder and its tracer read section headers).

pub const RAM_START: u64 = 0x8000_0000;
pub const TEXT: u64 = RAM_START;
/// `.data` starts here; the register constants come first.
pub const DATA: u64 = RAM_START + 0x400;
/// Buffers start here, inside `.data`.
pub const BUF: u64 = DATA + 0x100;
/// Size of the buffer area. Fixed, so every program has the same layout.
pub const BUF_SIZE: usize = 0x1000;

const SHSTRTAB: &[u8] = b"\0.text\0.data\0.shstrtab\0";
const SHT_PROGBITS: u32 = 1;
const SHT_STRTAB: u32 = 3;
const SHF_WRITE: u64 = 1;
const SHF_ALLOC: u64 = 2;
const SHF_EXECINSTR: u64 = 4;

fn u16le(o: &mut Vec<u8>, v: u16) { o.extend_from_slice(&v.to_le_bytes()) }
fn u32le(o: &mut Vec<u8>, v: u32) { o.extend_from_slice(&v.to_le_bytes()) }
fn u64le(o: &mut Vec<u8>, v: u64) { o.extend_from_slice(&v.to_le_bytes()) }

#[allow(clippy::too_many_arguments)]
fn shdr(o: &mut Vec<u8>, name: u32, ty: u32, flags: u64, addr: u64, off: u64, size: u64) {
    u32le(o, name);
    u32le(o, ty);
    u64le(o, flags);
    u64le(o, addr);
    u64le(o, off);
    u64le(o, size);
    u32le(o, 0);
    u32le(o, 0);
    u64le(o, 8);
    u64le(o, 0);
}

pub fn build_elf(text: &[u8], data: &[u8]) -> Vec<u8> {
    let shnum = 4u64;
    let shstr_off = 64 + shnum * 64;
    let text_off = shstr_off + SHSTRTAB.len() as u64;
    let data_off = text_off + text.len() as u64;
    let mut o = Vec::new();
    o.extend_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0]);
    o.extend_from_slice(&[0u8; 8]);
    u16le(&mut o, 2); // EXEC
    u16le(&mut o, 243); // RISC-V
    u32le(&mut o, 1);
    u64le(&mut o, TEXT); // entry
    u64le(&mut o, 0); // phoff
    u64le(&mut o, 64); // shoff
    u32le(&mut o, 0);
    u16le(&mut o, 64);
    u16le(&mut o, 0);
    u16le(&mut o, 0);
    u16le(&mut o, 64);
    u16le(&mut o, shnum as u16);
    u16le(&mut o, 3); // shstrndx
    shdr(&mut o, 0, 0, 0, 0, 0, 0);
    shdr(&mut o, 1, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, TEXT, text_off, text.len() as u64);
    shdr(&mut o, 7, SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, DATA, data_off, data.len() as u64);
    shdr(&mut o, 13, SHT_STRTAB, 0, 0, shstr_off, SHSTRTAB.len() as u64);
    o.extend_from_slice(SHSTRTAB);
    o.extend_from_slice(text);
    o.extend_from_slice(data);
    o
}

pub fn auipc(rd: u32, imm20: u32) -> u32 { (imm20 << 12) | (rd << 7) | 0x17 }
pub fn ld(rd: u32, rs1: u32, imm: u32) -> u32 { (imm << 20) | (rs1 << 15) | (3 << 12) | (rd << 7) | 0x03 }
pub fn inline_word(f3: u32, f7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | 0x0B
}
pub const JAL_SELF: u32 = 0x0000_006f;

/// A program that loads `regs` (register, value) from `.data`, executes one
/// inline `.insn r 0x0B, f3, f7, rd, rs1, rs2`, then spins on `j .`.
/// `buf` is copied to `BUF`.
pub fn program(regs: &[(u32, u64)], inline: (u32, u32, u32, u32, u32), buf: &[u8]) -> Vec<u8> {
    assert!(buf.len() <= BUF_SIZE);
    let mut text = Vec::new();
    let mut words = vec![auipc(5, 0)];
    for (i, (r, _)) in regs.iter().enumerate() {
        // auipc is at TEXT, so DATA + 8i is TEXT + 0x400 + 8i from x5.
        words.push(ld(*r, 5, 0x400 + 8 * i as u32));
    }
    let (f3, f7, rd, rs1, rs2) = inline;
    words.push(inline_word(f3, f7, rd, rs1, rs2));
    words.push(JAL_SELF);
    for w in words {
        text.extend_from_slice(&w.to_le_bytes());
    }
    assert!(text.len() <= 0x400);
    let mut data = vec![0u8; 0x100 + BUF_SIZE];
    for (i, (_, v)) in regs.iter().enumerate() {
        data[8 * i..8 * i + 8].copy_from_slice(&v.to_le_bytes());
    }
    data[0x100..0x100 + buf.len()].copy_from_slice(buf);
    build_elf(&text, &data)
}

/// Program size as the memory layout sees it: `.data` end minus RAM start.
pub fn program_size() -> u64 { DATA + 0x100 + BUF_SIZE as u64 - RAM_START }
