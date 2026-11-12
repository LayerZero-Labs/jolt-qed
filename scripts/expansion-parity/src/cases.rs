//! Source cases for the T1 groups.
//!
//! Every case for a kind that Jolt's decoder produces is built by encoding a
//! 32-bit word and running it through `jolt_program::image::decode::decode_instruction`,
//! so its normalized operands and immediate are exactly what the decoder
//! emits. Source kinds the decoder never returns (`NoOp`, `Unimpl` and the
//! final-row kinds such as `VirtualXORROT32`) are built directly from a
//! `SourceInstructionRow`; their case names end in `/direct`.

use jolt_program::image::decode::decode_instruction;
use jolt_riscv::{
    NormalizedOperands, SourceInstruction, SourceInstructionKind, SourceInstructionRow,
    RV64IMAC_JOLT_ALL_INLINES,
};

/// One source case of a T1 group.
pub struct Case {
    pub name: String,
    pub input: SourceInstruction,
}

/// How the free fields of an encoding are laid out.
#[derive(Clone, Copy)]
enum Fmt {
    /// rd, rs1, rs2 in their usual fields; `funct7` fixed.
    R,
    /// rd, rs1, imm[11:0].
    I,
    /// rs1, rs2, imm[11:0] split as for stores.
    S,
    /// rs1, rs2, imm[12:1] split as for branches.
    B,
    /// rd, imm[31:12].
    U,
    /// rd, imm[20:1] split as for JAL.
    J,
    /// rd, rs1, shamt[5:0] with a fixed funct6 in imm[11:6].
    Shift6(u32),
    /// rd, rs1, shamt[4:0] with a fixed funct7.
    Shift5,
    /// rd, rs1, rs2, aq/rl free, funct5 fixed; `lr` forces rs2 = 0.
    Amo { funct5: u32, lr: bool },
    /// A fixed word: no free fields.
    Fixed(u32),
    /// VirtualHostIO: rd must be 0; rs1, rs2 and funct7 free.
    HostIo,
}

struct Enc {
    kind: SourceInstructionKind,
    opcode: u32,
    funct3: u32,
    funct7: u32,
    fmt: Fmt,
}

const fn enc(
    kind: SourceInstructionKind,
    opcode: u32,
    funct3: u32,
    funct7: u32,
    fmt: Fmt,
) -> Enc {
    Enc {
        kind,
        opcode,
        funct3,
        funct7,
        fmt,
    }
}

fn encodings() -> Vec<Enc> {
    use Fmt::*;
    use SourceInstructionKind as K;
    let mut v = vec![
        enc(K::LUI, 0x37, 0, 0, U),
        enc(K::AUIPC, 0x17, 0, 0, U),
        enc(K::JAL, 0x6f, 0, 0, J),
        enc(K::JALR, 0x67, 0, 0, I),
        enc(K::BEQ, 0x63, 0, 0, B),
        enc(K::BNE, 0x63, 1, 0, B),
        enc(K::BLT, 0x63, 4, 0, B),
        enc(K::BGE, 0x63, 5, 0, B),
        enc(K::BLTU, 0x63, 6, 0, B),
        enc(K::BGEU, 0x63, 7, 0, B),
        enc(K::LB, 0x03, 0, 0, I),
        enc(K::LH, 0x03, 1, 0, I),
        enc(K::LW, 0x03, 2, 0, I),
        enc(K::LD, 0x03, 3, 0, I),
        enc(K::LBU, 0x03, 4, 0, I),
        enc(K::LHU, 0x03, 5, 0, I),
        enc(K::LWU, 0x03, 6, 0, I),
        enc(K::SB, 0x23, 0, 0, S),
        enc(K::SH, 0x23, 1, 0, S),
        enc(K::SW, 0x23, 2, 0, S),
        enc(K::SD, 0x23, 3, 0, S),
        enc(K::ADDI, 0x13, 0, 0, I),
        enc(K::SLLI, 0x13, 1, 0, Shift6(0)),
        enc(K::SLTI, 0x13, 2, 0, I),
        enc(K::SLTIU, 0x13, 3, 0, I),
        enc(K::XORI, 0x13, 4, 0, I),
        enc(K::SRLI, 0x13, 5, 0, Shift6(0)),
        enc(K::SRAI, 0x13, 5, 0, Shift6(0x10)),
        enc(K::ORI, 0x13, 6, 0, I),
        enc(K::ANDI, 0x13, 7, 0, I),
        enc(K::ADDIW, 0x1b, 0, 0, I),
        enc(K::SLLIW, 0x1b, 1, 0, Shift5),
        enc(K::SRLIW, 0x1b, 5, 0, Shift5),
        enc(K::SRAIW, 0x1b, 5, 0x20, Shift5),
        enc(K::FENCE, 0x0f, 0, 0, I),
        enc(K::ECALL, 0, 0, 0, Fixed(0x0000_0073)),
        enc(K::EBREAK, 0, 0, 0, Fixed(0x0010_0073)),
        enc(K::MRET, 0, 0, 0, Fixed(0x3020_0073)),
        enc(K::CSRRW, 0x73, 1, 0, I),
        enc(K::CSRRS, 0x73, 2, 0, I),
        enc(K::AdviceLB, 0x5b, 0, 0x00, R),
        enc(K::AdviceLH, 0x5b, 0, 0x01, R),
        enc(K::AdviceLW, 0x5b, 0, 0x02, R),
        enc(K::AdviceLD, 0x5b, 0, 0x03, R),
        enc(
            SourceInstructionKind::VirtualRev8W(jolt_riscv::instructions::VirtualRev8W(())),
            0x5b,
            0,
            0x05,
            R,
        ),
        enc(K::VirtualAssertEQ, 0x5b, 1, 0, B),
        enc(
            SourceInstructionKind::VirtualHostIO(jolt_riscv::instructions::VirtualHostIO(())),
            0x5b,
            2,
            0,
            HostIo,
        ),
    ];
    for (kind, f3, f7) in [
        (K::ADD, 0, 0x00),
        (K::SUB, 0, 0x20),
        (K::SLL, 1, 0x00),
        (K::SLT, 2, 0x00),
        (K::SLTU, 3, 0x00),
        (K::XOR, 4, 0x00),
        (K::SRL, 5, 0x00),
        (K::SRA, 5, 0x20),
        (K::OR, 6, 0x00),
        (K::AND, 7, 0x00),
        (K::MUL, 0, 0x01),
        (K::MULH, 1, 0x01),
        (K::MULHSU, 2, 0x01),
        (K::MULHU, 3, 0x01),
        (K::DIV, 4, 0x01),
        (K::DIVU, 5, 0x01),
        (K::REM, 6, 0x01),
        (K::REMU, 7, 0x01),
    ] {
        v.push(enc(kind, 0x33, f3, f7, R));
    }
    for (kind, f3, f7) in [
        (K::ADDW, 0, 0x00),
        (K::SUBW, 0, 0x20),
        (K::SLLW, 1, 0x00),
        (K::SRLW, 5, 0x00),
        (K::SRAW, 5, 0x20),
        (K::MULW, 0, 0x01),
        (K::DIVW, 4, 0x01),
        (K::DIVUW, 5, 0x01),
        (K::REMW, 6, 0x01),
        (K::REMUW, 7, 0x01),
    ] {
        v.push(enc(kind, 0x3b, f3, f7, R));
    }
    for (w, d, funct5) in [
        (K::LRW, K::LRD, 0b00010),
        (K::SCW, K::SCD, 0b00011),
        (K::AMOSWAPW, K::AMOSWAPD, 0b00001),
        (K::AMOADDW, K::AMOADDD, 0b00000),
        (K::AMOANDW, K::AMOANDD, 0b01100),
        (K::AMOORW, K::AMOORD, 0b01000),
        (K::AMOXORW, K::AMOXORD, 0b00100),
        (K::AMOMINW, K::AMOMIND, 0b10000),
        (K::AMOMAXW, K::AMOMAXD, 0b10100),
        (K::AMOMINUW, K::AMOMINUD, 0b11000),
        (K::AMOMAXUW, K::AMOMAXUD, 0b11100),
    ] {
        let lr = funct5 == 0b00010;
        v.push(enc(w, 0x2f, 2, 0, Amo { funct5, lr }));
        v.push(enc(d, 0x2f, 3, 0, Amo { funct5, lr }));
    }
    // CSRRC and the immediate forms, which a16z/jolt#2384 adds to the decoder.
    // The immediate forms carry their five-bit constant in the rs1 field.
    #[cfg(feature = "zicsr-remaining")]
    v.extend([
        enc(K::CSRRC, 0x73, 3, 0, I),
        enc(K::CSRRWI, 0x73, 5, 0, I),
        enc(K::CSRRSI, 0x73, 6, 0, I),
        enc(K::CSRRCI, 0x73, 7, 0, I),
    ]);
    v
}

/// Whether the kind is a Zicsr instruction, whose I-type immediate is a CSR address.
fn is_csr(kind: SourceInstructionKind) -> bool {
    kind.name().starts_with("CSRR")
}

/// Register and immediate choices for one encoding. `imm` holds raw field
/// bits; each format keeps only the bits its field has.
#[derive(Clone, Copy)]
struct Fields {
    rd: u32,
    rs1: u32,
    rs2: u32,
    imm: u32,
}

fn encode(e: &Enc, f: Fields) -> u32 {
    let (rd, rs1, rs2) = (f.rd & 31, f.rs1 & 31, f.rs2 & 31);
    let base = e.opcode | (e.funct3 << 12);
    match e.fmt {
        Fmt::R => base | (rd << 7) | (rs1 << 15) | (rs2 << 20) | (e.funct7 << 25),
        Fmt::I => base | (rd << 7) | (rs1 << 15) | ((f.imm & 0xfff) << 20),
        Fmt::S => {
            let imm = f.imm & 0xfff;
            base | ((imm & 0x1f) << 7) | (rs1 << 15) | (rs2 << 20) | ((imm >> 5) << 25)
        }
        Fmt::B => {
            let imm = f.imm & 0x1ffe;
            base | (((imm >> 11) & 1) << 7)
                | (((imm >> 1) & 0xf) << 8)
                | (rs1 << 15)
                | (rs2 << 20)
                | (((imm >> 5) & 0x3f) << 25)
                | (((imm >> 12) & 1) << 31)
        }
        Fmt::U => e.opcode | (rd << 7) | ((f.imm & 0xfffff) << 12),
        Fmt::J => {
            let imm = f.imm & 0x1f_fffe;
            e.opcode
                | (rd << 7)
                | (((imm >> 12) & 0xff) << 12)
                | (((imm >> 11) & 1) << 20)
                | (((imm >> 1) & 0x3ff) << 21)
                | (((imm >> 20) & 1) << 31)
        }
        Fmt::Shift6(funct6) => {
            base | (rd << 7) | (rs1 << 15) | ((f.imm & 0x3f) << 20) | (funct6 << 26)
        }
        Fmt::Shift5 => base | (rd << 7) | (rs1 << 15) | ((f.imm & 0x1f) << 20) | (e.funct7 << 25),
        Fmt::Amo { funct5, lr } => {
            let rs2 = if lr { 0 } else { rs2 };
            base | (rd << 7) | (rs1 << 15) | (rs2 << 20) | ((f.imm & 3) << 25) | (funct5 << 27)
        }
        Fmt::Fixed(word) => word,
        Fmt::HostIo => base | (rs1 << 15) | (rs2 << 20) | ((f.imm & 0x7f) << 25),
    }
}

/// The representative immediate used by the aliased, rd_zero, rs1_zero and
/// native_kind groups: a nonzero value in the field, negative where the field
/// is signed.
fn fixed_imm(e: &Enc) -> u32 {
    match e.fmt {
        Fmt::I => match e.kind {
            k if is_csr(k) => 0x300,
            k if k == SourceInstructionKind::FENCE => 0x0ff,
            _ => 0xff8, // -8
        },
        Fmt::S => 0xff8,
        Fmt::B => 0x1ff8,
        Fmt::U => 0x12345,
        Fmt::J => 0x1f_fff0,
        Fmt::Shift6(_) => 13,
        Fmt::Shift5 => 13,
        Fmt::Amo { .. } => 0,
        Fmt::R | Fmt::Fixed(_) | Fmt::HostIo => 0,
    }
}

/// splitmix64: a small seeded generator, so the random group is reproducible
/// without extra dependencies.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

const SUPPORTED_CSRS: [u32; 6] = [0x300, 0x305, 0x340, 0x341, 0x342, 0x343];

fn random_imm(e: &Enc, rng: &mut Rng) -> u32 {
    let raw = rng.next_u64() as u32;
    if is_csr(e.kind) && rng.below(4) != 0 {
        return SUPPORTED_CSRS[rng.below(SUPPORTED_CSRS.len() as u64) as usize];
    }
    // One draw in four takes an edge value of the field; encode() masks it.
    if rng.below(4) == 0 {
        return [0u32, 1, 0x7ff, 0x800, 0xffff_ffff, 0x7fff_ffff][rng.below(6) as usize];
    }
    raw
}

fn decode(e: &Enc, f: Fields, address: u64, compressed: bool) -> Result<SourceInstruction, String> {
    let word = encode(e, f);
    let decoded = decode_instruction(word, address, compressed, RV64IMAC_JOLT_ALL_INLINES)
        .map_err(|err| format!("{} word {word:#010x}: decoder error {err:?}", e.kind.name()))?;
    if decoded.kind() != e.kind {
        return Err(format!(
            "word {word:#010x} decodes to {}, not {}",
            decoded.kind().name(),
            e.kind.name()
        ));
    }
    Ok(decoded)
}

fn direct(
    kind: SourceInstructionKind,
    rd: u8,
    rs1: u8,
    rs2: u8,
    imm: i128,
    address: u64,
    compressed: bool,
) -> SourceInstruction {
    SourceInstruction::new(
        kind,
        SourceInstructionRow {
            address: address as usize,
            operands: NormalizedOperands {
                rd: Some(rd),
                rs1: Some(rs1),
                rs2: Some(rs2),
                imm,
            },
            inline: None,
            is_compressed: compressed,
        },
    )
}

/// Source kinds that the decoder produces (from the encoding table) and the
/// remaining kinds, both without `Inline`.
pub fn kind_partition() -> (Vec<SourceInstructionKind>, Vec<SourceInstructionKind>) {
    let decoded: Vec<_> = encodings().iter().map(|e| e.kind).collect();
    let direct = SourceInstructionKind::ALL
        .iter()
        .copied()
        .filter(|k| *k != SourceInstructionKind::Inline && !decoded.contains(k))
        .collect();
    (decoded, direct)
}

pub const RAM_BASE: u64 = 0x8000_0000;

/// Groups `aliased`, `rd_zero`, `rs1_zero` and `native_kind`: one case per
/// source kind except `Inline`, with the given registers.
pub fn register_group(group: &str, rd: u8, rs1: u8, rs2: u8) -> Result<Vec<Case>, String> {
    let mut cases = Vec::new();
    let mut address = RAM_BASE;
    for e in encodings() {
        let f = Fields {
            rd: rd.into(),
            rs1: rs1.into(),
            rs2: rs2.into(),
            imm: fixed_imm(&e),
        };
        // VirtualHostIO's encoding requires rd = 0 whatever the group says.
        let input = decode(&e, f, address, false)?;
        cases.push(Case {
            name: format!("{group}/{}", e.kind.name()),
            input,
        });
        address += 4;
    }
    let (_, others) = kind_partition();
    for kind in others {
        cases.push(Case {
            name: format!("{group}/{}/direct", kind.name()),
            input: direct(kind, rd, rs1, rs2, 0, address, false),
        });
        address += 4;
    }
    Ok(cases)
}

/// Group `csr` (feature `zicsr-remaining` only): every Zicsr kind on each of the
/// six CSRs Jolt models, with rd in {x0, x9} and rs1 (the five-bit constant for
/// the immediate forms) in {0, 2, 3, 8, 9, 31}. The values cover a zero
/// source, the reserved mtvec MODE bit (2), mstatus.MIE (8), rs1 = rd (9) and
/// all five bits set.
#[cfg(feature = "zicsr-remaining")]
pub fn csr_group() -> Result<Vec<Case>, String> {
    let mut cases = Vec::new();
    let mut address = RAM_BASE;
    for e in encodings().into_iter().filter(|e| is_csr(e.kind)) {
        for csr in SUPPORTED_CSRS {
            for rd in [0u32, 9] {
                for rs1 in [0u32, 2, 3, 8, 9, 31] {
                    let f = Fields { rd, rs1, rs2: 0, imm: csr };
                    let input = decode(&e, f, address, false)?;
                    cases.push(Case {
                        name: format!("csr/{}/{csr:#x}/rd{rd}/rs1_{rs1}", e.kind.name()),
                        input,
                    });
                    address += 4;
                }
            }
        }
    }
    Ok(cases)
}

/// Group `random`: `per_kind` decoded cases per decoder kind and one direct
/// case per other kind, with random registers, immediates, compression and
/// addresses (even, at or above 0x8000_0000).
pub fn random_group(seed: u64, per_kind: usize) -> Result<Vec<Case>, String> {
    let mut rng = Rng::new(seed);
    let mut cases = Vec::new();
    let mut n = 0usize;
    let address = |rng: &mut Rng| RAM_BASE + 2 * rng.below(1 << 24);
    for e in encodings() {
        for _ in 0..per_kind {
            let f = Fields {
                rd: rng.below(32) as u32,
                rs1: rng.below(32) as u32,
                rs2: rng.below(32) as u32,
                imm: random_imm(&e, &mut rng),
            };
            let compressed = rng.below(2) == 1;
            let a = address(&mut rng);
            let input = decode(&e, f, a, compressed)?;
            cases.push(Case {
                name: format!("random/{n:04}/{}", e.kind.name()),
                input,
            });
            n += 1;
        }
    }
    let (_, others) = kind_partition();
    for kind in others {
        let imm = rng.below(4096) as i128 - 2048;
        // ANDN is an R-type instruction, and Jolt's decoder never gives it an
        // immediate. The draw stays so that later cases keep their values.
        let imm = if kind == SourceInstructionKind::ANDN { 0 } else { imm };
        let compressed = rng.below(2) == 1;
        let a = address(&mut rng);
        let input = direct(
            kind,
            rng.below(32) as u8,
            rng.below(32) as u8,
            rng.below(32) as u8,
            imm,
            a,
            compressed,
        );
        cases.push(Case {
            name: format!("random/{n:04}/{}/direct", kind.name()),
            input,
        });
        n += 1;
    }
    Ok(cases)
}
