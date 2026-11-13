//! expansion-recipes: T6 symbolic recipes for Jolt's built-in expansions.
//!
//! For every source kind that Lean's `SourceInstruction` models, the binary
//! encodes every instruction word of that kind (all register fields and every
//! immediate value the field can hold), decodes it with Jolt's decoder, and
//! expands it through Jolt's production entry point with a fresh allocator.
//! From the rows of all those words it derives one symbolic recipe per kind:
//!
//! - a decision tree over register-identity predicates (`rd = x0`,
//!   `rd = rs1`, ...) of the registers Lean's constructor carries;
//! - per finite parameter value (the CSR, and the five-bit constant of the
//!   immediate CSR forms) a separate tree;
//! - at each leaf, whether Jolt emits one native row or a stamped sequence,
//!   and each row's kind, its register operands (a source register or a fixed
//!   register) and its immediate (a constant, the source immediate, or a table
//!   indexed by a shift amount).
//!
//! Every recipe is checked against every decoded word it covers: a word whose
//! rows differ from the recipe instantiated at its operands fails the run.
//! The binary writes the recipes as JSON and as Lean:
//! `JoltBytecode/JoltISA/ExpansionsAutomated.lean` (the `*ProgramAuto`
//! definitions), `JoltConstraints/ExpansionGen/Generated.lean` (the recipe of
//! every modelled kind as a function to `ExpandedSource`) and
//! `JoltConstraints/ExpansionGen/Equiv.lean` (one equality theorem per kind
//! between Lean's `SourceInstruction.expand` and the generated recipe).
//! See `scripts/expansion-parity/EXPANSION-RECIPES.md`.
//!
//! Exit status: 0 when every check passes, 1 when a check fails, 2 when the
//! binary cannot run.

#![allow(dead_code)]

#[path = "../cases.rs"]
mod cases;
#[path = "../rows.rs"]
mod rows;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Instant;

use jolt_program::expand::ExpansionAllocator;
use jolt_riscv::{JoltInstructionRow, NormalizedOperands, SourceInstructionKind};
use rayon::prelude::*;
use serde_json::{json, Value};

use crate::cases::{decode, direct, encodings, Enc, Fields, Fmt, RAM_BASE, SUPPORTED_CSRS};

// ---------------------------------------------------------------------------
// Lean-side description of each modelled source kind.

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Reg {
    Rd,
    Rs1,
    Rs2,
}

impl Reg {
    fn name(self) -> &'static str {
        match self {
            Reg::Rd => "rd",
            Reg::Rs1 => "rs1",
            Reg::Rs2 => "rs2",
        }
    }
    fn of(self, ops: &NormalizedOperands) -> Option<u8> {
        match self {
            Reg::Rd => ops.rd,
            Reg::Rs1 => ops.rs1,
            Reg::Rs2 => ops.rs2,
        }
    }
}

/// How Lean's constructor carries the source immediate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ImmKind {
    /// No immediate parameter; every row immediate must be a constant.
    NoImm,
    /// `imm : BitVec 12`; Jolt's immediate is its sign extension.
    I12,
    /// `imm : BitVec 13`; Jolt's immediate is its sign extension.
    B13,
    /// `imm : BitVec 20`; Jolt's immediate is the sign extension of `imm << 12`.
    U20,
    /// `imm : BitVec 21`; Jolt's immediate is its sign extension.
    J21,
    /// `shamt : BitVec w`; Jolt's immediate is `shamt`, or `0x400 | shamt`
    /// for the arithmetic shifts (decode.rs normalization).
    Shamt { width: u32, arith: bool },
    /// `csr : SystemCSR`: a finite parameter, one recipe per supported CSR.
    Csr,
}

impl ImmKind {
    fn lean_type(self) -> Option<String> {
        match self {
            ImmKind::NoImm | ImmKind::Csr => None,
            ImmKind::I12 => Some("BitVec 12".into()),
            ImmKind::B13 => Some("BitVec 13".into()),
            ImmKind::U20 => Some("BitVec 20".into()),
            ImmKind::J21 => Some("BitVec 21".into()),
            ImmKind::Shamt { width, .. } => Some(format!("BitVec {width}")),
        }
    }
    fn name(self) -> &'static str {
        match self {
            ImmKind::NoImm => "none",
            ImmKind::I12 => "i12",
            ImmKind::B13 => "b13",
            ImmKind::U20 => "u20",
            ImmKind::J21 => "j21",
            ImmKind::Shamt { width: 6, arith: false } => "shamt6",
            ImmKind::Shamt { width: 6, arith: true } => "shamt6_arith",
            ImmKind::Shamt { width: 5, arith: false } => "shamt5",
            ImmKind::Shamt { .. } => "shamt5_arith",
            ImmKind::Csr => "csr",
        }
    }
    /// The Lean parameter value (as a natural number) for Jolt's normalized
    /// immediate, used to index tables.
    fn lean_key(self, imm: i128) -> i128 {
        match self {
            ImmKind::Shamt { width, .. } => imm & ((1i128 << width) - 1),
            _ => imm,
        }
    }
    fn table_domain(self) -> Option<u32> {
        match self {
            ImmKind::Shamt { width, .. } => Some(1 << width),
            _ => None,
        }
    }
}

/// One modelled source kind.
struct Spec {
    /// `SourceInstructionKind::name`.
    kind: &'static str,
    /// The Lean `SourceInstruction` pattern with the parameter names the
    /// generated recipe uses.
    pattern: &'static str,
    /// Lean-visible register parameters, in the order of the generated
    /// function's arguments.
    regs: &'static [Reg],
    imm: ImmKind,
    /// The immediate CSR forms carry their five-bit constant in rs1; it is a
    /// finite parameter, one recipe per value.
    uimm_in_rs1: bool,
    /// Lean parameter that supplies the value of `VirtualAdvice` rows.
    advice: Option<&'static str>,
    /// Name and signature of the `ExpansionsAutomated.lean` definition, for
    /// the kinds that file defines.
    auto: Option<Auto>,
    /// Lean name of the generated recipe function.
    gen: &'static str,
}

#[derive(Clone, Copy)]
struct Auto {
    name: &'static str,
    /// Register parameters of the Auto definition (LR's carry an unused rs2).
    regs: &'static [&'static str],
    imm: Option<&'static str>,
    advice: bool,
    /// The Auto program's argument list in `SourceInstruction.expand`.
    call: &'static str,
}

const RD: &[Reg] = &[Reg::Rd];
const RD_RS1: &[Reg] = &[Reg::Rd, Reg::Rs1];
const RD_RS1_RS2: &[Reg] = &[Reg::Rd, Reg::Rs1, Reg::Rs2];
const RS1_RS2: &[Reg] = &[Reg::Rs1, Reg::Rs2];
const NONE: &[Reg] = &[];

const fn spec(
    kind: &'static str,
    pattern: &'static str,
    regs: &'static [Reg],
    imm: ImmKind,
    gen: &'static str,
) -> Spec {
    Spec { kind, pattern, regs, imm, uimm_in_rs1: false, advice: None, auto: None, gen }
}

const fn auto(
    name: &'static str,
    regs: &'static [&'static str],
    imm: Option<&'static str>,
    advice: bool,
    call: &'static str,
) -> Option<Auto> {
    Some(Auto { name, regs, imm, advice, call })
}

const SH6: ImmKind = ImmKind::Shamt { width: 6, arith: false };
const SH6A: ImmKind = ImmKind::Shamt { width: 6, arith: true };
const SH5: ImmKind = ImmKind::Shamt { width: 5, arith: false };
const SH5A: ImmKind = ImmKind::Shamt { width: 5, arith: true };

fn specs() -> Vec<Spec> {
    use ImmKind::*;
    let mut v = vec![
        spec("LUI", ".riscv (.LUI rd imm)", RD, U20, "genLUI"),
        spec("AUIPC", ".riscv (.AUIPC rd imm)", RD, U20, "genAUIPC"),
        spec("JAL", ".riscv (.JAL rd imm)", RD, J21, "genJAL"),
        spec("JALR", ".riscv (.JALR rd rs1 imm)", RD_RS1, I12, "genJALR"),
        spec("BEQ", ".riscv (.BEQ rs1 rs2 imm)", RS1_RS2, B13, "genBEQ"),
        spec("BNE", ".riscv (.BNE rs1 rs2 imm)", RS1_RS2, B13, "genBNE"),
        spec("BLT", ".riscv (.BLT rs1 rs2 imm)", RS1_RS2, B13, "genBLT"),
        spec("BGE", ".riscv (.BGE rs1 rs2 imm)", RS1_RS2, B13, "genBGE"),
        spec("BLTU", ".riscv (.BLTU rs1 rs2 imm)", RS1_RS2, B13, "genBLTU"),
        spec("BGEU", ".riscv (.BGEU rs1 rs2 imm)", RS1_RS2, B13, "genBGEU"),
        spec("LD", ".riscv (.LD rd rs1 imm)", RD_RS1, I12, "genLD"),
        spec("SD", ".riscv (.SD rs2 rs1 imm)", RS1_RS2, I12, "genSD"),
        spec("ADDI", ".riscv (.ADDI rd rs1 imm)", RD_RS1, I12, "genADDI"),
        spec("SLTI", ".riscv (.SLTI rd rs1 imm)", RD_RS1, I12, "genSLTI"),
        spec("SLTIU", ".riscv (.SLTIU rd rs1 imm)", RD_RS1, I12, "genSLTIU"),
        spec("XORI", ".riscv (.XORI rd rs1 imm)", RD_RS1, I12, "genXORI"),
        spec("ORI", ".riscv (.ORI rd rs1 imm)", RD_RS1, I12, "genORI"),
        spec("ANDI", ".riscv (.ANDI rd rs1 imm)", RD_RS1, I12, "genANDI"),
        spec("ADDIW", ".riscv (.ADDIW rd rs1 imm)", RD_RS1, I12, "genADDIW"),
        spec("FENCE", ".riscv .FENCE", NONE, NoImm, "genFENCE"),
        spec("ECALL", ".riscv .ECALL", NONE, NoImm, "genECALL"),
        spec("EBREAK", ".riscv .EBREAK", NONE, NoImm, "genEBREAK"),
        spec("MRET", ".riscv .MRET", NONE, NoImm, "genMRET"),
        spec("CSRRW", ".riscv (.CSRRW rd csr rs1)", RD_RS1, Csr, "genCSRRW"),
        spec("CSRRS", ".riscv (.CSRRS rd csr rs1)", RD_RS1, Csr, "genCSRRS"),
        spec("CSRRC", ".riscv (.CSRRC rd csr rs1)", RD_RS1, Csr, "genCSRRC"),
        Spec { uimm_in_rs1: true, ..spec("CSRRWI", ".riscv (.CSRRWI rd csr uimm)", RD, Csr, "genCSRRWI") },
        Spec { uimm_in_rs1: true, ..spec("CSRRSI", ".riscv (.CSRRSI rd csr uimm)", RD, Csr, "genCSRRSI") },
        Spec { uimm_in_rs1: true, ..spec("CSRRCI", ".riscv (.CSRRCI rd csr uimm)", RD, Csr, "genCSRRCI") },
        spec("VirtualRev8W", ".jolt (.VirtualRev8W rd rs1)", RD_RS1, NoImm, "genVirtualRev8W"),
        spec("VirtualAssertEQ", ".jolt (.VirtualAssertEQ rs1 rs2 imm)", RS1_RS2, B13, "genVirtualAssertEQ"),
        spec("VirtualHostIO", ".jolt .VirtualHostIO", NONE, NoImm, "genVirtualHostIO"),
    ];
    for k in ["ADD", "SUB", "SLT", "SLTU", "XOR", "OR", "AND", "ANDN", "ADDW", "SUBW", "MUL", "MULHU", "MULW"] {
        let pat: &'static str = Box::leak(format!(".riscv (.{k} rd rs1 rs2)").into_boxed_str());
        let gen: &'static str = Box::leak(format!("gen{k}").into_boxed_str());
        v.push(spec(k, pat, RD_RS1_RS2, ImmKind::NoImm, gen));
    }
    // Kinds whose programs ExpansionsAutomated.lean defines.
    let auto_rows: &[(&str, &str, &[Reg], ImmKind, &[&str], Option<&str>, bool, &str)] = &[
        ("LB", ".riscv (.LB rd rs1 imm)", RD_RS1, I12, &["rd", "rs1"], Some("imm"), false, "rd rs1 imm"),
        ("LH", ".riscv (.LH rd rs1 imm)", RD_RS1, I12, &["rd", "rs1"], Some("imm"), false, "rd rs1 imm"),
        ("LW", ".riscv (.LW rd rs1 imm)", RD_RS1, I12, &["rd", "rs1"], Some("imm"), false, "rd rs1 imm"),
        ("LBU", ".riscv (.LBU rd rs1 imm)", RD_RS1, I12, &["rd", "rs1"], Some("imm"), false, "rd rs1 imm"),
        ("LHU", ".riscv (.LHU rd rs1 imm)", RD_RS1, I12, &["rd", "rs1"], Some("imm"), false, "rd rs1 imm"),
        ("LWU", ".riscv (.LWU rd rs1 imm)", RD_RS1, I12, &["rd", "rs1"], Some("imm"), false, "rd rs1 imm"),
        ("SB", ".riscv (.SB rs2 rs1 imm)", RS1_RS2, I12, &["rs1", "rs2"], Some("imm"), false, "rs1 rs2 imm"),
        ("SH", ".riscv (.SH rs2 rs1 imm)", RS1_RS2, I12, &["rs1", "rs2"], Some("imm"), false, "rs1 rs2 imm"),
        ("SW", ".riscv (.SW rs2 rs1 imm)", RS1_RS2, I12, &["rs1", "rs2"], Some("imm"), false, "rs1 rs2 imm"),
        ("SLLI", ".riscv (.SLLI rd rs1 shamt)", RD_RS1, SH6, &["rd", "rs1"], Some("shamt"), false, "rd rs1 shamt"),
        ("SRLI", ".riscv (.SRLI rd rs1 shamt)", RD_RS1, SH6, &["rd", "rs1"], Some("shamt"), false, "rd rs1 shamt"),
        ("SRAI", ".riscv (.SRAI rd rs1 shamt)", RD_RS1, SH6A, &["rd", "rs1"], Some("shamt"), false, "rd rs1 shamt"),
        ("SLLIW", ".riscv (.SLLIW rd rs1 shamt)", RD_RS1, SH5, &["rd", "rs1"], Some("shamt"), false, "rd rs1 shamt"),
        ("SRLIW", ".riscv (.SRLIW rd rs1 shamt)", RD_RS1, SH5, &["rd", "rs1"], Some("shamt"), false, "rd rs1 shamt"),
        ("SRAIW", ".riscv (.SRAIW rd rs1 shamt)", RD_RS1, SH5A, &["rd", "rs1"], Some("shamt"), false, "rd rs1 shamt"),
        ("SLL", ".riscv (.SLL rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("SRL", ".riscv (.SRL rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("SRA", ".riscv (.SRA rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("SLLW", ".riscv (.SLLW rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("SRLW", ".riscv (.SRLW rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("SRAW", ".riscv (.SRAW rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("MULH", ".riscv (.MULH rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("MULHSU", ".riscv (.MULHSU rd rs1 rs2)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
        ("DIV", ".riscv (.DIV rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("DIVU", ".riscv (.DIVU rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("REM", ".riscv (.REM rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("REMU", ".riscv (.REMU rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("DIVW", ".riscv (.DIVW rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("DIVUW", ".riscv (.DIVUW rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("REMW", ".riscv (.REMW rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("REMUW", ".riscv (.REMUW rd rs1 rs2 q)", RD_RS1_RS2, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, true, "rd rs1 rs2 q"),
        ("LRW", ".riscv (.LR_W rd rs1 _ _)", RD_RS1, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 (regidx.Regidx 0)"),
        ("LRD", ".riscv (.LR_D rd rs1 _ _)", RD_RS1, ImmKind::NoImm, &["rd", "rs1", "rs2"], None, false, "rd rs1 (regidx.Regidx 0)"),
        ("AdviceLB", ".jolt (.AdviceLB rd)", RD, ImmKind::NoImm, &["rd"], None, false, "rd"),
        ("AdviceLH", ".jolt (.AdviceLH rd)", RD, ImmKind::NoImm, &["rd"], None, false, "rd"),
        ("AdviceLW", ".jolt (.AdviceLW rd)", RD, ImmKind::NoImm, &["rd"], None, false, "rd"),
        ("AdviceLD", ".jolt (.AdviceLD rd)", RD, ImmKind::NoImm, &["rd"], None, false, "rd"),
    ];
    for &(k, pat, regs, imm, aregs, aimm, adv, call) in auto_rows {
        let name: &'static str = Box::leak(format!("{}ProgramAuto", k.to_ascii_lowercase()).into_boxed_str());
        let gen: &'static str = Box::leak(format!("gen{k}").into_boxed_str());
        let pat: &'static str = Box::leak(pat.to_string().into_boxed_str());
        let call: &'static str = Box::leak(call.to_string().into_boxed_str());
        let aregs: &'static [&'static str] = Box::leak(aregs.to_vec().into_boxed_slice());
        let aimm: Option<&'static str> = aimm.map(|s| &*Box::leak(s.to_string().into_boxed_str()));
        v.push(Spec {
            advice: adv.then_some("q"),
            auto: auto(name, aregs, aimm, adv, call),
            ..spec(k, pat, regs, imm, gen)
        });
    }
    for (k, lean) in [
        ("SCW", "SC_W"), ("SCD", "SC_D"),
        ("AMOSWAPW", "AMOSWAP_W"), ("AMOADDW", "AMOADD_W"), ("AMOANDW", "AMOAND_W"),
        ("AMOORW", "AMOOR_W"), ("AMOXORW", "AMOXOR_W"), ("AMOMINW", "AMOMIN_W"),
        ("AMOMAXW", "AMOMAX_W"), ("AMOMINUW", "AMOMINU_W"), ("AMOMAXUW", "AMOMAXU_W"),
        ("AMOSWAPD", "AMOSWAP_D"), ("AMOADDD", "AMOADD_D"), ("AMOANDD", "AMOAND_D"),
        ("AMOORD", "AMOOR_D"), ("AMOXORD", "AMOXOR_D"), ("AMOMIND", "AMOMIN_D"),
        ("AMOMAXD", "AMOMAX_D"), ("AMOMINUD", "AMOMINU_D"), ("AMOMAXUD", "AMOMAXU_D"),
    ] {
        let name: &'static str = Box::leak(format!("{}ProgramAuto", k.to_ascii_lowercase()).into_boxed_str());
        let gen: &'static str = Box::leak(format!("gen{k}").into_boxed_str());
        let pat: &'static str = Box::leak(format!(".riscv (.{lean} rd rs1 rs2 _ _)").into_boxed_str());
        v.push(Spec {
            auto: auto(name, &["rd", "rs1", "rs2"], None, false, "rd rs1 rs2"),
            ..spec(k, pat, RD_RS1_RS2, ImmKind::NoImm, gen)
        });
    }
    v
}

// ---------------------------------------------------------------------------
// Inputs: every decoded word of a kind.

/// The raw field domains of one encoding: (has rd, has rs1, has rs2, imm values).
fn domain(e: &Enc) -> (bool, bool, bool, Vec<u32>) {
    match e.fmt {
        Fmt::R => (true, true, true, vec![0]),
        Fmt::I => (true, true, false, (0..4096).collect()),
        Fmt::S => (false, true, true, (0..4096).collect()),
        Fmt::B => (false, true, true, (0..4096).map(|k| k << 1).collect()),
        Fmt::U => (true, false, false, (0..1 << 20).collect()),
        Fmt::J => (true, false, false, (0..1 << 20).map(|k| k << 1).collect()),
        Fmt::Shift6(_) => (true, true, false, (0..64).collect()),
        Fmt::Shift5 => (true, true, false, (0..32).collect()),
        Fmt::Amo { lr, .. } => (true, true, !lr, (0..4).collect()),
        Fmt::Fixed(_) => (false, false, false, vec![0]),
        Fmt::HostIo => (false, true, true, (0..128).collect()),
    }
}

/// One decoded input: its normalized operands and Jolt's rows (or error).
struct Input {
    ops: NormalizedOperands,
    result: Result<Vec<JoltInstructionRow>, String>,
}

// ---------------------------------------------------------------------------
// Register predicates and per-class accumulators.

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Pred {
    Zero(Reg),
    Eq(Reg, Reg),
}

impl Pred {
    fn eval(self, ops: &NormalizedOperands) -> bool {
        match self {
            Pred::Zero(r) => r.of(ops) == Some(0),
            Pred::Eq(a, b) => a.of(ops) == b.of(ops),
        }
    }
    fn text(self) -> String {
        match self {
            Pred::Zero(r) => format!("{} = x0", r.name()),
            Pred::Eq(a, b) => format!("{} = {}", a.name(), b.name()),
        }
    }
    fn lean(self) -> String {
        match self {
            Pred::Zero(r) => format!("isX0 {}", r.name()),
            Pred::Eq(a, b) => format!("sameXReg {} {}", a.name(), b.name()),
        }
    }
}

fn preds(regs: &[Reg]) -> Vec<Pred> {
    let mut v: Vec<Pred> = regs.iter().map(|r| Pred::Zero(*r)).collect();
    for i in 0..regs.len() {
        for j in i + 1..regs.len() {
            v.push(Pred::Eq(regs[i], regs[j]));
        }
    }
    v
}

/// What a register field can be, given the inputs seen so far.
#[derive(Clone, Debug)]
struct FieldAcc {
    present: bool,
    /// Bit i: the field equals the i-th Lean-visible register parameter on
    /// every input seen.
    params: u8,
    /// `Some(Some(v))`: every input had value v; `Some(None)`: values differ.
    lit: Option<Option<u8>>,
}

#[derive(Clone, Debug)]
struct ImmAcc {
    lit: Option<Option<i128>>,
    src: bool,
    /// The row immediate equals the source immediate modulo 2^64 (enough for
    /// a `BitVec 64` field; Jolt stores some immediates `u64`-wrapped).
    src64: bool,
    /// Lean key (shift amount) to row immediate; `None` once not functional
    /// or too large.
    table: Option<BTreeMap<i128, i128>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    Rows { native: bool, kinds: Vec<(String, bool, bool, bool)> },
    Error(String),
}

#[derive(Clone, Debug)]
struct Acc {
    shape: Shape,
    fields: Vec<[FieldAcc; 3]>,
    imms: Vec<ImmAcc>,
    count: u64,
    /// The first input that disagreed with the shape, if any.
    conflict: Option<String>,
    example: String,
}

const TABLE_CAP: usize = 64;

fn row_field(row: &JoltInstructionRow, i: usize) -> Option<u8> {
    match i {
        0 => row.operands.rd,
        1 => row.operands.rs1,
        _ => row.operands.rs2,
    }
}

fn shape_of(result: &Result<Vec<JoltInstructionRow>, String>) -> Result<Shape, String> {
    match result {
        Err(e) => Ok(Shape::Error(e.clone())),
        Ok(rows) => {
            let native = rows.len() == 1 && rows[0].virtual_sequence_remaining.is_none();
            if !native && rows.iter().any(|r| r.virtual_sequence_remaining.is_none()) {
                return Err("a multi-row expansion has a row without sequence metadata".into());
            }
            Ok(Shape::Rows {
                native,
                kinds: rows
                    .iter()
                    .map(|r| {
                        (
                            r.instruction_kind.name().to_string(),
                            r.operands.rd.is_some(),
                            r.operands.rs1.is_some(),
                            r.operands.rs2.is_some(),
                        )
                    })
                    .collect(),
            })
        }
    }
}

fn describe(ops: &NormalizedOperands) -> String {
    format!("rd={:?} rs1={:?} rs2={:?} imm={}", ops.rd, ops.rs1, ops.rs2, ops.imm)
}

impl Acc {
    fn new(spec: &Spec, input: &Input) -> Acc {
        let shape = match shape_of(&input.result) {
            Ok(s) => s,
            Err(e) => {
                return Acc {
                    shape: Shape::Error(String::new()),
                    fields: vec![],
                    imms: vec![],
                    count: 1,
                    conflict: Some(format!("{e} at {}", describe(&input.ops))),
                    example: describe(&input.ops),
                }
            }
        };
        let mut acc = Acc {
            shape,
            fields: vec![],
            imms: vec![],
            count: 0,
            conflict: None,
            example: describe(&input.ops),
        };
        if let Ok(rows) = &input.result {
            for row in rows {
                let f = |i: usize| FieldAcc {
                    present: row_field(row, i).is_some(),
                    params: 0xff,
                    lit: None,
                };
                acc.fields.push([f(0), f(1), f(2)]);
                acc.imms.push(ImmAcc {
                    lit: None,
                    src: true,
                    src64: true,
                    table: spec.imm.table_domain().map(|_| BTreeMap::new()),
                });
            }
        }
        acc.add(spec, input);
        acc
    }

    fn add(&mut self, spec: &Spec, input: &Input) {
        self.count += 1;
        if self.conflict.is_some() {
            return;
        }
        match shape_of(&input.result) {
            Ok(s) if s == self.shape => {}
            Ok(s) => {
                self.conflict = Some(format!(
                    "{} gives {} but {} gives {}",
                    self.example,
                    shape_text(&self.shape),
                    describe(&input.ops),
                    shape_text(&s)
                ));
                return;
            }
            Err(e) => {
                self.conflict = Some(format!("{e} at {}", describe(&input.ops)));
                return;
            }
        }
        let Ok(rows) = &input.result else { return };
        for (k, row) in rows.iter().enumerate() {
            for i in 0..3 {
                let fa = &mut self.fields[k][i];
                let Some(v) = row_field(row, i) else { continue };
                for (bit, reg) in spec.regs.iter().enumerate() {
                    if reg.of(&input.ops) != Some(v) {
                        fa.params &= !(1 << bit);
                    }
                }
                fa.lit = match fa.lit {
                    None => Some(Some(v)),
                    Some(Some(w)) if w == v => Some(Some(v)),
                    _ => Some(None),
                };
            }
            let ia = &mut self.imms[k];
            let imm = row.operands.imm;
            ia.lit = match ia.lit {
                None => Some(Some(imm)),
                Some(Some(w)) if w == imm => Some(Some(imm)),
                _ => Some(None),
            };
            if imm != input.ops.imm {
                ia.src = false;
            }
            if umod(imm, 64) != umod(input.ops.imm, 64) {
                ia.src64 = false;
            }
            if let Some(t) = &mut ia.table {
                let key = spec.imm.lean_key(input.ops.imm);
                match t.get(&key) {
                    Some(&w) if w != imm => ia.table = None,
                    Some(_) => {}
                    None if t.len() >= TABLE_CAP => ia.table = None,
                    None => {
                        t.insert(key, imm);
                    }
                }
            }
        }
    }

    /// Merge two accumulators: the result describes the union of their inputs.
    fn merge(mut self, other: &Acc) -> Acc {
        self.count += other.count;
        if self.conflict.is_some() {
            return self;
        }
        if let Some(c) = &other.conflict {
            self.conflict = Some(c.clone());
            return self;
        }
        if self.shape != other.shape {
            self.conflict = Some(format!(
                "{} gives {} but {} gives {}",
                self.example,
                shape_text(&self.shape),
                other.example,
                shape_text(&other.shape)
            ));
            return self;
        }
        for (a, b) in self.fields.iter_mut().zip(&other.fields) {
            for i in 0..3 {
                a[i].params &= b[i].params;
                a[i].lit = match (a[i].lit, b[i].lit) {
                    (None, x) | (x, None) => x,
                    (Some(Some(x)), Some(Some(y))) if x == y => Some(Some(x)),
                    _ => Some(None),
                };
            }
        }
        for (a, b) in self.imms.iter_mut().zip(&other.imms) {
            a.lit = match (a.lit, b.lit) {
                (None, x) | (x, None) => x,
                (Some(Some(x)), Some(Some(y))) if x == y => Some(Some(x)),
                _ => Some(None),
            };
            a.src &= b.src;
            a.src64 &= b.src64;
            a.table = match (a.table.take(), &b.table) {
                (Some(mut t), Some(u)) => {
                    let mut ok = true;
                    for (k, v) in u {
                        match t.get(k) {
                            Some(w) if w != v => ok = false,
                            Some(_) => {}
                            None => {
                                t.insert(*k, *v);
                            }
                        }
                    }
                    (ok && t.len() <= TABLE_CAP).then_some(t)
                }
                _ => None,
            };
        }
        self
    }
}

fn shape_text(s: &Shape) -> String {
    match s {
        Shape::Error(e) => format!("error {e}"),
        Shape::Rows { native, kinds } => format!(
            "{} [{}]",
            if *native { "native" } else { "sequence" },
            kinds.iter().map(|k| k.0.as_str()).collect::<Vec<_>>().join(", ")
        ),
    }
}

// ---------------------------------------------------------------------------
// Templates.

#[derive(Clone, Debug, PartialEq, Eq)]
enum RegT {
    Param(Reg),
    Lit(u8),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ImmT {
    Lit(i128),
    Src,
    /// Index into the table list.
    Table(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RowT {
    kind: String,
    regs: [Option<RegT>; 3],
    imm: ImmT,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Leaf {
    Rows { native: bool, rows: Vec<RowT> },
    Error(String),
}

#[derive(Clone, Debug)]
enum Tree {
    Leaf(Leaf),
    If(Pred, Box<Tree>, Box<Tree>),
}

/// Tables shared across recipes: (Lean key type width, row field kind, values by key).
#[derive(Default)]
struct Tables {
    list: Vec<(u32, String, Vec<i128>)>,
}

impl Tables {
    fn intern(&mut self, width: u32, row_kind: &str, values: Vec<i128>) -> usize {
        if let Some(i) = self
            .list
            .iter()
            .position(|(w, k, v)| *w == width && k == row_kind && *v == values)
        {
            return i;
        }
        self.list.push((width, row_kind.to_string(), values));
        self.list.len() - 1
    }
}

/// The template an accumulator describes, or why there is none.
fn template(spec: &Spec, acc: &Acc, tables: &mut Tables) -> Result<Leaf, String> {
    if let Some(c) = &acc.conflict {
        return Err(c.clone());
    }
    let (native, kinds) = match &acc.shape {
        Shape::Error(e) => return Ok(Leaf::Error(e.clone())),
        Shape::Rows { native, kinds } => (*native, kinds),
    };
    let mut rows = Vec::new();
    for (k, (kind, ..)) in kinds.iter().enumerate() {
        let mut regs: [Option<RegT>; 3] = [None, None, None];
        for i in 0..3 {
            let fa = &acc.fields[k][i];
            if !fa.present {
                continue;
            }
            regs[i] = Some(if let Some(Some(v)) = fa.lit {
                RegT::Lit(v)
            } else if let Some(bit) = (0..spec.regs.len()).find(|b| fa.params & (1 << b) != 0) {
                RegT::Param(spec.regs[bit])
            } else {
                return Err(format!(
                    "row {k} ({kind}) field {} is neither a fixed register nor a source register",
                    ["rd", "rs1", "rs2"][i]
                ));
            });
        }
        let ia = &acc.imms[k];
        let imm = if let Some(Some(v)) = ia.lit {
            ImmT::Lit(v)
        } else if (ia.src || (ia.src64 && layout(kind).and_then(imm_field) == Some(FieldTy::B64)))
            && spec.imm != ImmKind::NoImm
            && spec.imm != ImmKind::Csr
        {
            ImmT::Src
        } else if let (Some(t), Some(n)) = (&ia.table, spec.imm.table_domain()) {
            if t.len() as u32 != n {
                return Err(format!(
                    "row {k} ({kind}): the immediate table has {} of {n} entries",
                    t.len()
                ));
            }
            let width = match spec.imm {
                ImmKind::Shamt { width, .. } => width,
                _ => unreachable!(),
            };
            ImmT::Table(tables.intern(width, kind, t.values().copied().collect()))
        } else {
            return Err(format!(
                "row {k} ({kind}): the immediate is neither a constant, the source immediate, \
                 nor a function of the shift amount"
            ));
        };
        rows.push(RowT { kind: kind.clone(), regs, imm });
    }
    Ok(Leaf::Rows { native, rows })
}

/// Builds the decision tree for one finite-parameter value from its classes
/// (keyed by the truth values of all predicates).
fn build_tree(
    spec: &Spec,
    classes: &BTreeMap<Vec<bool>, Acc>,
    all: &[Pred],
    tables: &mut Tables,
) -> Result<Tree, String> {
    // Smallest predicate subset (by size, then priority order) on whose
    // values the rows depend.
    let n = all.len();
    let mut subsets: Vec<Vec<usize>> = (0u32..1 << n)
        .map(|m| (0..n).filter(|i| m & (1 << i) != 0).collect())
        .collect();
    subsets.sort_by_key(|s: &Vec<usize>| (s.len(), s.clone()));
    let merge_ok = |group: &[&Acc]| -> bool {
        let mut it = group.iter();
        let first = (*it.next().unwrap()).clone();
        let m = it.fold(first, |a, b| a.merge(b));
        let mut scratch = Tables::default();
        template(spec, &m, &mut scratch).is_ok()
    };
    let mut chosen = None;
    for s in &subsets {
        let mut groups: BTreeMap<Vec<bool>, Vec<&Acc>> = BTreeMap::new();
        for (key, acc) in classes {
            groups.entry(s.iter().map(|&i| key[i]).collect()).or_default().push(acc);
        }
        if groups.values().all(|g| merge_ok(g)) {
            chosen = Some(s.clone());
            break;
        }
    }
    let Some(chosen) = chosen else {
        // Report the first class whose own template fails.
        for (key, acc) in classes {
            if let Err(e) = template(spec, acc, &mut Tables::default()) {
                let pattern: Vec<String> = all
                    .iter()
                    .zip(key)
                    .map(|(p, b)| format!("{}{}", if *b { "" } else { "not " }, p.text()))
                    .collect();
                return Err(format!("register pattern [{}]: {e}", pattern.join(", ")));
            }
        }
        return Err("the rows depend on something other than register identity".into());
    };
    fn go(
        spec: &Spec,
        classes: Vec<(&Vec<bool>, &Acc)>,
        preds: &[usize],
        all: &[Pred],
        tables: &mut Tables,
    ) -> Result<Tree, String> {
        let mut it = classes.iter();
        let first = it.next().unwrap().1.clone();
        let merged = it.fold(first, |a, b| a.merge(b.1));
        if let Ok(leaf) = template(spec, &merged, &mut Tables::default()) {
            let _ = leaf;
            return Ok(Tree::Leaf(template(spec, &merged, tables)?));
        }
        for (pos, &p) in preds.iter().enumerate() {
            let (yes, no): (Vec<_>, Vec<_>) = classes.iter().partition(|(k, _)| k[p]);
            if yes.is_empty() || no.is_empty() {
                continue;
            }
            let rest: Vec<usize> = preds[pos + 1..].to_vec();
            return Ok(Tree::If(
                all[p],
                Box::new(go(spec, yes, &rest, all, tables)?),
                Box::new(go(spec, no, &rest, all, tables)?),
            ));
        }
        Err("no predicate separates the register patterns".into())
    }
    go(spec, classes.iter().collect(), &chosen, all, tables)
}

// ---------------------------------------------------------------------------
// Sweeping one kind.

/// Finite-parameter key: (CSR address, uimm) for the CSR forms, none otherwise.
type FiniteKey = (Option<i128>, Option<u8>);

struct KindResult {
    inputs: u64,
    decode_errors: u64,
    /// Per finite key: decision tree (or failure), and input count.
    trees: BTreeMap<FiniteKey, (Result<Tree, String>, u64)>,
    /// Inputs per unsupported finite key (CSR addresses Lean does not model):
    /// all must be rejected.
    unsupported_accepted: Vec<String>,
    unsupported_rejected: u64,
}

fn finite_key(spec: &Spec, ops: &NormalizedOperands) -> FiniteKey {
    let csr = (spec.imm == ImmKind::Csr).then_some(ops.imm);
    let uimm = if spec.uimm_in_rs1 { ops.rs1 } else { None };
    (csr, uimm)
}

fn supported(key: &FiniteKey) -> bool {
    match key.0 {
        None => true,
        Some(c) => SUPPORTED_CSRS.iter().any(|&s| s as i128 == c),
    }
}

fn sweep(spec: &Spec, enc: Option<&Enc>, tables: &mut Tables) -> KindResult {
    let all = preds(spec.regs);
    // Index space of raw fields.
    let (has_rd, has_rs1, has_rs2, imms) = match enc {
        Some(e) => domain(e),
        None => (true, true, true, vec![0]), // ANDN: built directly
    };
    let nr = |b: bool| if b { 32u64 } else { 1 };
    let total = nr(has_rd) * nr(has_rs1) * nr(has_rs2) * imms.len() as u64;
    type Map = BTreeMap<FiniteKey, BTreeMap<Vec<bool>, Acc>>;
    #[derive(Default)]
    struct Part {
        map: Map,
        decode_errors: u64,
        unsupported_accepted: Vec<String>,
        unsupported_rejected: u64,
    }
    let make_input = |idx: u64| -> Option<Input> {
        let mut i = idx;
        let mut take = |b: bool| -> u32 {
            if b {
                let v = (i % 32) as u32;
                i /= 32;
                v
            } else {
                0
            }
        };
        let rd = take(has_rd);
        let rs1 = take(has_rs1);
        let rs2 = take(has_rs2);
        let imm = imms[i as usize];
        let address = RAM_BASE + 2 * (idx % (1 << 16));
        let compressed = idx % 2 == 1;
        let source = match enc {
            Some(e) => match decode(e, Fields { rd, rs1, rs2, imm }, address, compressed) {
                Ok(s) => s,
                Err(_) => return None,
            },
            None => direct(
                SourceInstructionKind::ANDN,
                rd as u8,
                rs1 as u8,
                rs2 as u8,
                0,
                address,
                compressed,
            ),
        };
        let mut allocator = ExpansionAllocator::new();
        let result = rows::expand(&source, &mut allocator).map_err(|e| format!("{e:?}"));
        Some(Input { ops: source.row().operands, result })
    };
    let part = (0..total)
        .into_par_iter()
        .fold(Part::default, |mut part, idx| {
            match make_input(idx) {
                None => part.decode_errors += 1,
                Some(input) => {
                    let fk = finite_key(spec, &input.ops);
                    if !supported(&fk) {
                        if input.result.is_ok() {
                            if part.unsupported_accepted.len() < 4 {
                                part.unsupported_accepted.push(describe(&input.ops));
                            }
                        } else {
                            part.unsupported_rejected += 1;
                        }
                        return part;
                    }
                    let key: Vec<bool> = all.iter().map(|p| p.eval(&input.ops)).collect();
                    let classes = part.map.entry(fk).or_default();
                    match classes.get_mut(&key) {
                        Some(acc) => acc.add(spec, &input),
                        None => {
                            classes.insert(key, Acc::new(spec, &input));
                        }
                    }
                }
            }
            part
        })
        .reduce(Part::default, |mut a, b| {
            a.decode_errors += b.decode_errors;
            a.unsupported_rejected += b.unsupported_rejected;
            a.unsupported_accepted.extend(b.unsupported_accepted);
            for (fk, classes) in b.map {
                let into = a.map.entry(fk).or_default();
                for (key, acc) in classes {
                    match into.remove(&key) {
                        Some(x) => {
                            into.insert(key, x.merge(&acc));
                        }
                        None => {
                            into.insert(key, acc);
                        }
                    }
                }
            }
            a
        });
    let mut trees = BTreeMap::new();
    for (fk, classes) in &part.map {
        let count = classes.values().map(|a| a.count).sum();
        trees.insert(*fk, (build_tree(spec, classes, &all, tables), count));
    }
    KindResult {
        inputs: total,
        decode_errors: part.decode_errors,
        trees,
        unsupported_accepted: part.unsupported_accepted,
        unsupported_rejected: part.unsupported_rejected,
    }
}

// ---------------------------------------------------------------------------
// JSON.

fn reg_json(r: &Option<RegT>) -> Value {
    match r {
        None => Value::Null,
        Some(RegT::Param(p)) => json!({ "param": p.name() }),
        Some(RegT::Lit(v)) => json!({ "lit": v }),
    }
}

fn imm_json(i: &ImmT) -> Value {
    match i {
        ImmT::Lit(v) => json!({ "lit": v.to_string() }),
        ImmT::Src => json!({ "src": true }),
        ImmT::Table(t) => json!({ "table": t }),
    }
}

fn tree_json(t: &Tree) -> Value {
    match t {
        Tree::If(p, a, b) => json!({ "if": p.text(), "then": tree_json(a), "else": tree_json(b) }),
        Tree::Leaf(Leaf::Error(e)) => json!({ "error": e }),
        Tree::Leaf(Leaf::Rows { native, rows }) => json!({
            "dispatch": if *native { "native" } else { "sequence" },
            "rows": rows.iter().map(|r| json!({
                "kind": r.kind,
                "rd": reg_json(&r.regs[0]),
                "rs1": reg_json(&r.regs[1]),
                "rs2": reg_json(&r.regs[2]),
                "imm": imm_json(&r.imm),
            })).collect::<Vec<_>>(),
        }),
    }
}

fn csr_name(addr: i128) -> &'static str {
    match addr {
        0x300 => "mstatus",
        0x305 => "mtvec",
        0x340 => "mscratch",
        0x341 => "mepc",
        0x342 => "mcause",
        0x343 => "mtval",
        _ => "unsupported",
    }
}

// ---------------------------------------------------------------------------
// Lean rendering shared by both files.

/// How Lean's `Instr` constructor of a row kind lays out its fields.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Layout {
    /// dst lhs rhs
    R3,
    /// dst src (imm : BitVec 64)
    I64,
    /// dst src (imm : Nat)
    INat,
    /// dst (imm : Nat)
    DNat,
    /// dst (imm : BitVec 64)
    D64,
    /// lhs rhs (imm : BitVec 128)
    B128,
    /// faultClass dst base (imm : BitVec 64) fault
    Load,
    /// faultClass dst base (imm : BitVec 64)
    LD,
    /// base value (imm : BitVec 64) fault
    Store,
    /// base value (imm : BitVec 64)
    SD,
    /// dst value address (imm : BitVec 64)
    ShiftData,
    /// dst (value : BitVec 64) (imm : BitVec 64)
    Advice,
    /// no fields
    Bare,
}

fn layout(kind: &str) -> Option<Layout> {
    use Layout::*;
    Some(match kind {
        "ADD" | "ADDW" | "SUB" | "SUBW" | "MUL" | "MULW" | "MULHU" | "ANDN" | "OR" | "XOR"
        | "AND" | "SLT" | "SLTU" | "VirtualNegateIf" | "VirtualSRL" | "VirtualSRA"
        | "VirtualSRLW" | "VirtualSRAW" | "VirtualPext" | "VirtualPextSigned"
        | "VirtualXORROT32" | "VirtualXORROT24" | "VirtualXORROT16" | "VirtualXORROT63"
        | "VirtualXORROTL1" | "VirtualXORROTW16" | "VirtualXORROTW12" | "VirtualXORROTW8"
        | "VirtualXORROTW7" | "VirtualXORROTW22" | "VirtualXORROTW19" | "VirtualXORROTW6" => R3,
        "ADDI" | "ADDIW" | "ANDI" | "ORI" | "XORI" | "SLTI" | "SLTIU" | "VirtualMULI"
        | "VirtualMULIW" | "VirtualPow2" | "VirtualPow2W" | "VirtualShiftRightBitmask"
        | "VirtualShiftRightBitmaskW" | "VirtualRev8W" | "VirtualWindowMaskB"
        | "VirtualWindowMaskH" | "VirtualWindowMaskW" | "VirtualSignExtendWord"
        | "VirtualZeroExtendWord" | "VirtualMovsign" | "JALR" => I64,
        "VirtualSRLI" | "VirtualSRAI" | "VirtualSRLIW" | "VirtualSRAIW" | "VirtualROTRI"
        | "VirtualROTRIW" => INat,
        "VirtualPow2I" | "VirtualPow2IW" | "VirtualShiftRightBitmaskI" => DNat,
        "LUI" | "AUIPC" | "JAL" | "VirtualAdviceLoad" => D64,
        "BEQ" | "BNE" | "BLT" | "BGE" | "BLTU" | "BGEU" | "VirtualAssertEQ"
        | "VirtualAssertValidDiv0" | "VirtualAssertValidUnsignedRemainder"
        | "VirtualAssertMulUNoOverflow" | "VirtualAssertLTE" => B128,
        "VirtualLoadB" | "VirtualLoadH" | "VirtualLoadW" => Load,
        "LD" => LD,
        "VirtualStoreB" | "VirtualStoreH" | "VirtualStoreW" => Store,
        "SD" => SD,
        "VirtualShiftDataB" | "VirtualShiftDataH" | "VirtualShiftDataW" => ShiftData,
        "VirtualAdvice" => Advice,
        "FENCE" | "VirtualHostIO" => Bare,
        _ => return None,
    })
}

/// Which register fields a layout uses (rd, rs1, rs2).
fn layout_fields(l: Layout) -> [bool; 3] {
    use Layout::*;
    match l {
        R3 | ShiftData => [true, true, true],
        I64 | INat | Load | LD => [true, true, false],
        DNat | D64 | Advice => [true, false, false],
        B128 | Store | SD => [false, true, true],
        Bare => [false, false, false],
    }
}

/// The Lean-only fault class and alignment exception of a memory row, a rule
/// of the Lean model (Jolt's rows carry neither): atomics, LR and SC use the
/// `.amo` class; stores, SC and atomics fault with `E_SAMO_Addr_Align`.
fn load_class_and_fault(source: &str) -> (&'static str, &'static str) {
    let amo = source.starts_with("AMO") || source.starts_with("LR") || source.starts_with("SC");
    let samo = amo || matches!(source, "SB" | "SH" | "SW" | "SD");
    (
        if amo { "amo" } else { "normal" },
        if samo { "(ExceptionType.E_SAMO_Addr_Align ())" } else { "(ExceptionType.E_Load_Addr_Align ())" },
    )
}

fn lean_reg(r: &RegT) -> String {
    match r {
        RegT::Param(p) => format!("(.xreg {})", p.name()),
        RegT::Lit(v) if *v < 32 => format!("(.xreg (regidx.Regidx {v}))"),
        RegT::Lit(v) => format!("(.vreg (BitVec.ofNat 7 {v}))"),
    }
}

fn umod(v: i128, bits: u32) -> u128 {
    (v as u128) & ((1u128 << bits) - 1)
}

/// Field type of a row immediate.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FieldTy {
    B64,
    B128,
    Nat,
}

fn imm_field(l: Layout) -> Option<FieldTy> {
    use Layout::*;
    match l {
        R3 | Bare => None,
        INat | DNat => Some(FieldTy::Nat),
        B128 => Some(FieldTy::B128),
        _ => Some(FieldTy::B64),
    }
}

// ---------------------------------------------------------------------------
// Generated.lean: one function per kind returning `Option ExpandedSource`.

fn gen_imm(spec: &Spec, ty: FieldTy, imm: &ImmT) -> Result<String, String> {
    match (imm, ty) {
        (ImmT::Lit(v), FieldTy::B64) => Ok(format!("({} : BitVec 64)", umod(*v, 64))),
        (ImmT::Lit(v), FieldTy::B128) => Ok(format!("({} : BitVec 128)", umod(*v, 128))),
        (ImmT::Lit(v), FieldTy::Nat) if *v >= 0 => Ok(format!("({v} : Nat)")),
        (ImmT::Lit(v), FieldTy::Nat) => Err(format!("negative Nat immediate {v}")),
        (ImmT::Src, ty) => {
            let m = match ty {
                FieldTy::B64 => 64,
                FieldTy::B128 => 128,
                FieldTy::Nat => return Err("source immediate in a Nat field".into()),
            };
            match spec.imm {
                ImmKind::I12 | ImmKind::B13 | ImmKind::J21 => Ok(format!("(sign_extend (m := {m}) imm)")),
                ImmKind::U20 => Ok(format!("(sign_extend (m := {m}) (imm +++ (0 : BitVec 12)))")),
                k => Err(format!("source immediate of kind {}", k.name())),
            }
        }
        (ImmT::Table(t), _) => Ok(format!("(immTable{t} {})", spec.auto.and_then(|a| a.imm).unwrap_or("imm"))),
    }
}

fn gen_row(spec: &Spec, row: &RowT, advice: &mut usize) -> Result<String, String> {
    let l = layout(&row.kind).ok_or_else(|| format!("no Lean layout for row kind {}", row.kind))?;
    let used = layout_fields(l);
    for i in 0..3 {
        if used[i] != row.regs[i].is_some() {
            return Err(format!(
                "row kind {}: field {} is {} but Lean's constructor {} it",
                row.kind,
                ["rd", "rs1", "rs2"][i],
                if row.regs[i].is_some() { "present" } else { "absent" },
                if used[i] { "needs" } else { "has no place for" }
            ));
        }
    }
    let r = |i: usize| lean_reg(row.regs[i].as_ref().unwrap());
    let imm = match imm_field(l) {
        Some(ty) => gen_imm(spec, ty, &row.imm)?,
        None => {
            if row.imm != ImmT::Lit(0) {
                return Err(format!("row kind {} has immediate {:?} but no immediate field", row.kind, row.imm));
            }
            String::new()
        }
    };
    let (class, fault) = load_class_and_fault(spec.kind);
    use Layout::*;
    let args = match l {
        R3 => format!("{} {} {}", r(0), r(1), r(2)),
        I64 | INat => format!("{} {} {imm}", r(0), r(1)),
        DNat | D64 => format!("{} {imm}", r(0)),
        B128 => format!("{} {} {imm}", r(1), r(2)),
        Load => format!(".{class} {} {} {imm} {fault}", r(0), r(1)),
        LD => format!(".{class} {} {} {imm}", r(0), r(1)),
        Store => format!("{} {} {imm} {fault}", r(1), r(2)),
        SD => format!("{} {} {imm}", r(1), r(2)),
        ShiftData => format!("{} {} {} {imm}", r(0), r(1), r(2)),
        Advice => {
            let name = spec.advice.ok_or_else(|| format!("{} has a VirtualAdvice row but no advice parameter", spec.kind))?;
            *advice += 1;
            if *advice > 1 {
                return Err(format!("{} has more than one VirtualAdvice row", spec.kind));
            }
            format!("{} {name} {imm}", r(0))
        }
        Bare => String::new(),
    };
    Ok(if args.is_empty() { format!("JoltISA.Instr.{}", row.kind) } else { format!("JoltISA.Instr.{} {args}", row.kind) })
}

fn gen_tree(spec: &Spec, t: &Tree, indent: usize, out: &mut String) -> Result<(), String> {
    let pad = " ".repeat(indent);
    match t {
        Tree::If(p, a, b) => {
            writeln!(out, "{pad}if {} then", p.lean()).unwrap();
            gen_tree(spec, a, indent + 2, out)?;
            writeln!(out, "{pad}else").unwrap();
            gen_tree(spec, b, indent + 2, out)?;
        }
        Tree::Leaf(Leaf::Error(e)) => {
            writeln!(out, "{pad}-- Jolt: {e}").unwrap();
            writeln!(out, "{pad}none").unwrap();
        }
        Tree::Leaf(Leaf::Rows { native, rows }) => {
            let mut advice = 0;
            let rendered: Result<Vec<String>, String> = rows.iter().map(|r| gen_row(spec, r, &mut advice)).collect();
            let rendered = rendered?;
            if *native {
                writeln!(out, "{pad}some (.native ({}))", rendered[0]).unwrap();
            } else {
                writeln!(out, "{pad}some (.sequence [").unwrap();
                for (i, r) in rendered.iter().enumerate() {
                    let sep = if i + 1 < rendered.len() { "," } else { "" };
                    writeln!(out, "{pad}  {r}{sep}").unwrap();
                }
                writeln!(out, "{pad}])").unwrap();
            }
        }
    }
    Ok(())
}

/// The generated function's parameter list (Lean names and types).
fn gen_params(spec: &Spec) -> Vec<(String, String)> {
    let mut v = Vec::new();
    for r in spec.regs {
        v.push((r.name().to_string(), "regidx".to_string()));
    }
    if spec.imm == ImmKind::Csr {
        v.push(("csr".into(), "JoltISA.SystemCSR".into()));
    }
    if spec.uimm_in_rs1 {
        v.push(("uimm".into(), "BitVec 5".into()));
    }
    if let Some(t) = spec.imm.lean_type() {
        let name = spec.auto.and_then(|a| a.imm).unwrap_or("imm");
        v.push((name.to_string(), t));
    }
    if let Some(a) = spec.advice {
        v.push((a.to_string(), "BitVec 64".into()));
    }
    v
}

fn group_params(params: &[(String, String)]) -> String {
    let mut out = Vec::new();
    let mut i = 0;
    while i < params.len() {
        let ty = &params[i].1;
        let mut names = vec![params[i].0.clone()];
        let mut j = i + 1;
        while j < params.len() && params[j].1 == *ty {
            names.push(params[j].0.clone());
            j += 1;
        }
        out.push(format!("({} : {ty})", names.join(" ")));
        i = j;
    }
    out.join(" ")
}

const CSR_ORDER: [(i128, &str); 6] = [
    (0x300, "mstatus"),
    (0x305, "mtvec"),
    (0x340, "mscratch"),
    (0x341, "mepc"),
    (0x342, "mcause"),
    (0x343, "mtval"),
];

fn gen_def(spec: &Spec, r: &KindResult) -> Result<String, String> {
    let mut out = String::new();
    let params = gen_params(spec);
    writeln!(out, "/-- Jolt's `{}` recipe at the pin, generated from every decoded instruction word. -/", spec.kind).unwrap();
    writeln!(out, "def {} {} : Option ExpandedSource :=", spec.gen, group_params(&params)).unwrap();
    let tree = |fk: &FiniteKey| -> Result<&Tree, String> {
        match r.trees.get(fk) {
            Some((Ok(t), _)) => Ok(t),
            Some((Err(e), _)) => Err(e.clone()),
            None => Err(format!("no inputs for {fk:?}")),
        }
    };
    if spec.imm == ImmKind::Csr {
        writeln!(out, "  match csr with").unwrap();
        for (addr, name) in CSR_ORDER {
            writeln!(out, "  | .{name} =>").unwrap();
            if spec.uimm_in_rs1 {
                writeln!(out, "    match uimm.toNat with").unwrap();
                for u in 0u8..32 {
                    writeln!(out, "    | {u} =>").unwrap();
                    gen_tree(spec, tree(&(Some(addr), Some(u)))?, 6, &mut out)?;
                }
                writeln!(out, "    | _ => none").unwrap();
            } else {
                gen_tree(spec, tree(&(Some(addr), None))?, 4, &mut out)?;
            }
        }
    } else {
        gen_tree(spec, tree(&(None, None))?, 2, &mut out)?;
    }
    writeln!(out).unwrap();
    Ok(out)
}

fn lean_nat_ty(ty: &str) -> &'static str {
    match ty {
        "Nat" => "Nat",
        "B128" => "BitVec 128",
        _ => "BitVec 64",
    }
}

fn table_field(row_kind: &str) -> FieldTy {
    imm_field(layout(row_kind).unwrap_or(Layout::I64)).unwrap_or(FieldTy::B64)
}

fn render_generated(specs: &[Spec], results: &[KindResult], tables: &Tables, header: &str) -> Result<String, String> {
    let mut out = String::new();
    out.push_str(header);
    out.push_str(
        "import JoltConstraints.expansions

/-!
# Jolt's built-in expansion recipes (generated)

Generated by `scripts/expansion-parity/run-expansion-recipes.sh` (T6) from Jolt's
production expansion entry point. Do not edit by hand.

For each source kind that Lean's `SourceInstruction` models, the generator
decoded every instruction word of that kind (every register field and every
immediate value), expanded it with a fresh allocator, and derived the recipe
below: a decision tree over register identity (`isX0`, `sameXReg`), one tree
per CSR and per five-bit constant for the CSR forms, and at each leaf the native
row or the stamped sequence. A leaf `none` is an expansion Jolt rejects.
Every decoded word's rows equal its recipe instantiated at its operands.

Two parts of each row are Lean-only and follow the model's rules, not Jolt's
data: the fault class and alignment exception of memory rows, and the value of
the `VirtualAdvice` row (the division's advice parameter `q`).

`JoltConstraints/ExpansionGen/Equiv.lean` proves `SourceInstruction.expand`
equal to `ExpansionGen.expand`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions\nopen JoltISA

set_option autoImplicit false

namespace ExpansionGen

",
    );
    for (i, (w, kind, values)) in tables.list.iter().enumerate() {
        let ty = match table_field(kind) {
            FieldTy::Nat => "Nat",
            FieldTy::B64 => "BitVec 64",
            FieldTy::B128 => "BitVec 128",
        };
        writeln!(out, "/-- Immediate of a `{kind}` row as a function of the {w}-bit shift amount. -/").unwrap();
        writeln!(out, "def immTable{i} (s : BitVec {w}) : {ty} :=").unwrap();
        writeln!(out, "  match s.toNat with").unwrap();
        for (k, v) in values.iter().enumerate() {
            let v = match table_field(kind) {
                FieldTy::Nat => {
                    if *v < 0 {
                        return Err(format!("table {i}: negative Nat {v}"));
                    }
                    v.to_string()
                }
                FieldTy::B64 => umod(*v, 64).to_string(),
                FieldTy::B128 => umod(*v, 128).to_string(),
            };
            writeln!(out, "  | {k} => {v}").unwrap();
        }
        writeln!(out, "  | _ => 0").unwrap();
        writeln!(out).unwrap();
        let _ = lean_nat_ty;
    }
    for (spec, r) in specs.iter().zip(results) {
        out.push_str(&gen_def(spec, r).map_err(|e| format!("{}: {e}", spec.kind))?);
    }
    writeln!(out, "/-- The generated recipe of every modelled source instruction. -/").unwrap();
    writeln!(out, "def expand : SourceInstruction → Option ExpandedSource").unwrap();
    for spec in specs {
        let args: Vec<String> = gen_params(spec).into_iter().map(|(n, _)| n).collect();
        let pat = spec.pattern.to_string();
        writeln!(out, "  | {pat} => {} {}", spec.gen, args.join(" ")).unwrap();
    }
    writeln!(out).unwrap();
    writeln!(out, "end ExpansionGen").unwrap();
    Ok(out)
}

// ---------------------------------------------------------------------------
// ExpansionsAutomated.lean, in the format the Lean model already uses.

fn auto_imm(spec: &Spec, row: &RowT, tables: &Tables) -> Result<(String, bool), String> {
    // Returns the rendered immediate and whether the `JoltISA.Encoded.`
    // constructor is used.
    let l = layout(&row.kind).ok_or_else(|| format!("no layout for {}", row.kind))?;
    let encoded12 = matches!(
        row.kind.as_str(),
        "ADDI" | "ADDIW" | "ANDI" | "ORI" | "XORI" | "SLTI" | "SLTIU" | "JALR" | "VirtualWindowMaskB"
            | "VirtualWindowMaskH" | "VirtualWindowMaskW" | "VirtualLoadB" | "VirtualLoadH"
            | "VirtualLoadW" | "VirtualStoreB" | "VirtualStoreH" | "VirtualStoreW"
            | "VirtualShiftDataB" | "VirtualShiftDataH" | "VirtualShiftDataW" | "LD" | "SD"
    );
    match &row.imm {
        ImmT::Src => {
            if encoded12 && spec.imm == ImmKind::I12 {
                Ok((spec.auto.and_then(|a| a.imm).unwrap_or("imm").to_string(), true))
            } else {
                Err(format!("{}: source immediate in a {} row", spec.kind, row.kind))
            }
        }
        ImmT::Table(t) => {
            let (_, _, values) = &tables.list[*t];
            let s = spec.auto.and_then(|a| a.imm).unwrap_or("shamt");
            // The Lean expressions the model uses; Equiv.lean proves each
            // equal to its table.
            let expr = match (spec.kind, row.kind.as_str()) {
                ("SLLI", "VirtualMULI") => format!("(slliMultiplier {s})"),
                ("SRLI", "VirtualSRLI") => format!("(srliBitmask {s})"),
                ("SRAI", "VirtualSRAI") => format!("(sraiBitmask {s})"),
                ("SLLIW", "VirtualMULIW") => format!("(BitVec.ofNat 64 (2 ^ {s}.toNat))"),
                ("SRLIW", "VirtualSRLIW") | ("SRAIW", "VirtualSRAIW") => {
                    format!("((1 <<< 32) - (1 <<< {s}.toNat))")
                }
                _ => return Err(format!("{}: no Lean expression for the {} table {values:?}", spec.kind, row.kind)),
            };
            Ok((expr, false))
        }
        ImmT::Lit(v) => {
            let v = *v;
            // Constants the 12-bit encoded constructors can hold.
            if encoded12 {
                let low = umod(v, 12) as i128;
                let signed = if low & 0x800 != 0 { low - 0x1000 } else { low };
                if signed as i64 as i128 == v || (signed as i64) as u64 as i128 == v {
                    if (signed as i64) == (v as i64) {
                        return Ok((format!("({signed} : BitVec 12)"), true));
                    }
                }
            }
            let bits = v as u64;
            let out = match row.kind.as_str() {
                "VirtualSRAI" => format!("(sraiBitmask {})", bits.trailing_zeros()),
                "VirtualSRLI" => format!("(srliBitmask {})", bits.trailing_zeros()),
                "VirtualMULI" if bits.is_power_of_two() => format!("(slliMultiplier {})", bits.trailing_zeros()),
                _ => match imm_field(l) {
                    Some(FieldTy::Nat) => format!("{bits}"),
                    Some(FieldTy::B128) => format!("({v} : BitVec 128)"),
                    Some(FieldTy::B64) => format!("({} : BitVec 64)", v as i64),
                    None => String::new(),
                },
            };
            Ok((out, false))
        }
    }
}

fn auto_row(spec: &Spec, row: &RowT, tables: &Tables, advice: &mut usize) -> Result<String, String> {
    let l = layout(&row.kind).ok_or_else(|| format!("no layout for {}", row.kind))?;
    let r = |i: usize| lean_reg(row.regs[i].as_ref().unwrap());
    let (imm, encoded) = auto_imm(spec, row, tables)?;
    let (class, fault) = load_class_and_fault(spec.kind);
    use Layout::*;
    let args = match l {
        R3 => format!("{} {} {}", r(0), r(1), r(2)),
        I64 | INat => format!("{} {} {imm}", r(0), r(1)),
        DNat | D64 => format!("{} {imm}", r(0)),
        B128 => format!("{} {} {imm}", r(1), r(2)),
        Load => format!(".{class} {} {} {imm} {fault}", r(0), r(1)),
        LD => format!(".{class} {} {} {imm}", r(0), r(1)),
        Store => format!("{} {} {imm} {fault}", r(1), r(2)),
        SD => format!("{} {} {imm}", r(1), r(2)),
        ShiftData => format!("{} {} {} {imm}", r(0), r(1), r(2)),
        Advice => {
            let a = format!("advice{advice}");
            *advice += 1;
            format!("{} {a} {imm}", r(0))
        }
        Bare => String::new(),
    };
    let ctor = if encoded { format!("JoltISA.Encoded.{}", row.kind) } else { format!(".{}", row.kind) };
    Ok(if args.is_empty() { format!(".instr (.{}) <|", row.kind) } else { format!(".instr ({ctor} {args}) <|") })
}

fn auto_leaf(spec: &Spec, leaf: &Leaf, tables: &Tables, indent: usize, out: &mut String) -> Result<(), String> {
    let pad = " ".repeat(indent);
    match leaf {
        Leaf::Error(e) => Err(format!("{}: an Auto program cannot express Jolt's error {e}", spec.kind)),
        Leaf::Rows { rows, .. } => {
            let mut advice = 0;
            for row in rows {
                writeln!(out, "{pad}{}", auto_row(spec, row, tables, &mut advice)?).unwrap();
            }
            writeln!(out, "{pad}.done RETIRE_SUCCESS").unwrap();
            Ok(())
        }
    }
}

fn auto_tree(spec: &Spec, t: &Tree, tables: &Tables, indent: usize, out: &mut String) -> Result<(), String> {
    match t {
        Tree::Leaf(l) => auto_leaf(spec, l, tables, indent, out),
        Tree::If(p, a, b) => {
            let pad = " ".repeat(indent);
            writeln!(out, "{pad}if {} then", p.lean()).unwrap();
            auto_tree(spec, a, tables, indent + 2, out)?;
            writeln!(out, "{pad}else").unwrap();
            auto_tree(spec, b, tables, indent + 2, out)
        }
    }
}

fn advice_rows(t: &Tree) -> usize {
    match t {
        Tree::If(_, a, b) => advice_rows(a).max(advice_rows(b)),
        Tree::Leaf(Leaf::Rows { rows, .. }) => rows.iter().filter(|r| r.kind == "VirtualAdvice").count(),
        Tree::Leaf(_) => 0,
    }
}

const AUTO_ORDER: [&str; 57] = [
    "divProgramAuto",
    "divuProgramAuto",
    "lbProgramAuto",
    "lbuProgramAuto",
    "lhProgramAuto",
    "lhuProgramAuto",
    "lwProgramAuto",
    "mulhProgramAuto",
    "mulhsuProgramAuto",
    "remProgramAuto",
    "remuProgramAuto",
    "sbProgramAuto",
    "shProgramAuto",
    "sllProgramAuto",
    "slliProgramAuto",
    "sraProgramAuto",
    "sraiProgramAuto",
    "srlProgramAuto",
    "srliProgramAuto",
    "swProgramAuto",
    "slliwProgramAuto",
    "srliwProgramAuto",
    "sraiwProgramAuto",
    "sllwProgramAuto",
    "srlwProgramAuto",
    "srawProgramAuto",
    "lwuProgramAuto",
    "divuwProgramAuto",
    "divwProgramAuto",
    "remuwProgramAuto",
    "remwProgramAuto",
    "lrwProgramAuto",
    "scwProgramAuto",
    "amoswapwProgramAuto",
    "amoaddwProgramAuto",
    "amoandwProgramAuto",
    "amoorwProgramAuto",
    "amoxorwProgramAuto",
    "amominwProgramAuto",
    "amomaxwProgramAuto",
    "amominuwProgramAuto",
    "amomaxuwProgramAuto",
    "lrdProgramAuto",
    "scdProgramAuto",
    "amoswapdProgramAuto",
    "amoadddProgramAuto",
    "amoanddProgramAuto",
    "amoordProgramAuto",
    "amoxordProgramAuto",
    "amomindProgramAuto",
    "amomaxdProgramAuto",
    "amominudProgramAuto",
    "amomaxudProgramAuto",
    "advicelbProgramAuto",
    "adviceldProgramAuto",
    "advicelhProgramAuto",
    "advicelwProgramAuto",
];

fn render_auto(specs: &[Spec], results: &[KindResult], tables: &Tables, header: &str) -> Result<String, String> {
    let mut out = String::new();
    out.push_str(header);
    out.push_str(
        "import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.VirtualRegisters
import JoltBytecode.JoltISA.Expansions.ALU

open LeanRV64D

/-!
# Auto-generated Jolt-ISA expansion programs

Generated by `scripts/expansion-parity/run-expansion-recipes.sh` (T6) from the
symbolic recipes that the expansion-parity driver derives from Jolt's production
expansion entry point over every decoded instruction word. Do not edit by hand;
regenerate instead. Each `...ProgramAuto` is the recipe of its source kind,
including its branch on `rd = x0`; `JoltConstraints/ExpansionGen/Equiv.lean`
proves `SourceInstruction.expand` equal to the generated recipes.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace JoltISA

",
    );
    let mut n = 0;
    // The order of the definitions in the file before T6, kept so that diffs
    // stay small.
    let mut order: Vec<(usize, &Spec, &KindResult)> = specs
        .iter()
        .zip(results)
        .filter_map(|(spec, r)| {
            let a = spec.auto?;
            let pos = AUTO_ORDER.iter().position(|&x| x == a.name).unwrap_or(usize::MAX);
            Some((pos, spec, r))
        })
        .collect();
    order.sort_by_key(|x| x.0);
    for (_, spec, r) in order {
        let Some(a) = spec.auto else { continue };
        let Some((Ok(tree), _)) = r.trees.get(&(None, None)) else {
            return Err(format!("{}: no recipe", spec.kind));
        };
        let mut groups = vec![format!("({} : regidx)", a.regs.join(" "))];
        if let Some(imm) = a.imm {
            let ty = spec.imm.lean_type().unwrap();
            groups.push(format!("({imm} : {ty})"));
        }
        let advice = advice_rows(tree);
        if advice > 0 {
            let names: Vec<String> = (0..advice).map(|i| format!("advice{i}")).collect();
            groups.push(format!("({} : BitVec 64)", names.join(" ")));
        }
        writeln!(out, "/-- Auto-generated from the Rust `{}` expansion. -/", spec.kind).unwrap();
        writeln!(out, "def {} {} : Program :=", a.name, groups.join(" ")).unwrap();
        auto_tree(spec, tree, tables, 2, &mut out)?;
        writeln!(out).unwrap();
        n += 1;
    }
    out.push_str("end JoltISA\n\n");
    writeln!(out, "-- generated {n} expansion program(s)").unwrap();
    Ok(out)
}

// ---------------------------------------------------------------------------
// Equiv.lean: one theorem per kind.

/// The Lean expression that `SourceInstruction.expand` uses for each table,
/// keyed by (source kind, row kind), as in `auto_imm`.
fn table_expr(kind: &str, row: &str) -> Option<&'static str> {
    Some(match (kind, row) {
        ("SLLI", "VirtualMULI") => "slliMultiplier s",
        ("SRLI", "VirtualSRLI") => "srliBitmask s",
        ("SRAI", "VirtualSRAI") => "sraiBitmask s",
        ("SLLIW", "VirtualMULIW") => "BitVec.ofNat 64 (2 ^ s.toNat)",
        ("SRLIW", "VirtualSRLIW") | ("SRAIW", "VirtualSRAIW") => "(1 <<< 32) - (1 <<< s.toNat)",
        _ => return None,
    })
}

fn tables_used(t: &Tree, out: &mut BTreeSet<(usize, String)>) {
    match t {
        Tree::If(_, a, b) => {
            tables_used(a, out);
            tables_used(b, out);
        }
        Tree::Leaf(Leaf::Rows { rows, .. }) => {
            for r in rows {
                if let ImmT::Table(i) = r.imm {
                    out.insert((i, r.kind.clone()));
                }
            }
        }
        Tree::Leaf(_) => {}
    }
}

fn render_equiv(specs: &[Spec], results: &[KindResult], tables: &Tables, header: &str) -> Result<String, String> {
    let mut out = String::new();
    out.push_str(header);
    out.push_str(
        "import JoltConstraints.ExpansionGen.Generated
import JoltConstraints.ExpansionGen.Tactic

/-!
# Lean's expansions equal Jolt's generated recipes

Generated by `scripts/expansion-parity/run-expansion-recipes.sh` (T6). Do not
edit by hand.

One theorem per modelled source kind states that `SourceInstruction.expand`
equals the recipe that `JoltConstraints/ExpansionGen/Generated.lean` derives from
Jolt; `expand_eq_generated` collects them. The table lemmas prove the shift
helpers of the model equal Jolt's immediate for every shift amount.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions\nopen JoltISA

set_option autoImplicit false

namespace ExpansionGen

",
    );
    // Table lemmas.
    let mut seen: BTreeMap<(usize, &str), String> = BTreeMap::new();
    let mut table_lemmas: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for (spec, r) in specs.iter().zip(results) {
        for (tree, _) in r.trees.values() {
            let Ok(tree) = tree else { continue };
            let mut used = BTreeSet::new();
            tables_used(tree, &mut used);
            for (i, row) in used {
                let expr = table_expr(spec.kind, &row)
                    .ok_or_else(|| format!("{}: no Lean expression for table {i} ({row})", spec.kind))?;
                if let Some(lemma) = seen.get(&(i, expr)) {
                    let lemma: String = lemma.clone();
                    table_lemmas.entry(spec.kind).or_default().push(lemma);
                    continue;
                }
                let (w, ..) = &tables.list[i];
                let ty = match table_field(&row) {
                    FieldTy::Nat => "Nat",
                    FieldTy::B64 => "BitVec 64",
                    FieldTy::B128 => "BitVec 128",
                };
                writeln!(out, "/-- `{expr}` is Jolt's `{row}` immediate for every shift amount `s`. -/").unwrap();
                let lemma = format!("immTable{i}_eq_{}", spec.kind.to_ascii_lowercase());
                seen.insert((i, expr), lemma.clone());
                table_lemmas.entry(spec.kind).or_default().push(lemma.clone());
                writeln!(out, "theorem {lemma} (s : BitVec {w}) : ({expr} : {ty}) = immTable{i} s := by").unwrap();
                writeln!(out, "  bitvec_cases s <;> rfl").unwrap();
                writeln!(out).unwrap();
            }
        }
    }
    for spec in specs {
        let params = gen_params(spec);
        let args: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        // The pattern with its wildcards named, so the statement can quantify them.
        let mut pat = spec.pattern.to_string();
        let mut extra = Vec::new();
        let mut k = 0;
        while let Some(pos) = pat.find(" _") {
            let name = format!("b{k}");
            pat.replace_range(pos..pos + 2, &format!(" {name}"));
            extra.push(name);
            k += 1;
        }
        let mut binders = group_params(&params);
        if !extra.is_empty() {
            binders = format!("{binders} ({} : Bool)", extra.join(" "));
        }
        let pat = pat.trim_start_matches('.').to_string();
        // Definitions to unfold: the generated recipe, the model's program
        // and its helpers, and the table lemmas of the shift kinds.
        let mut unfold = vec![spec.gen.to_string()];
        if let Some(a) = spec.auto {
            unfold.push(a.name.to_string());
        }
        let extra: &[&str] = match spec.kind {
            "LUI" => &["JoltISA.luiValue"],
            "ECALL" => &["ecallProgram"],
            "EBREAK" => &["ebreakProgram"],
            "MRET" => &["mretProgram"],
            "CSRRW" => &["csrrwProgram", "csrReadInto", "csrSwapWrite"],
            "CSRRS" => &["csrrsProgram", "csrBitUpdateProgram", "csrReadInto"],
            "CSRRC" => &["csrrcProgram", "csrBitUpdateProgram", "csrReadInto"],
            "CSRRWI" => &["csrrwiProgram", "csrReadInto"],
            "CSRRSI" => &["csrrsiProgram", "csrImmediateBitUpdateProgram", "csrImmediateMask", "csrReadInto"],
            "CSRRCI" => &["csrrciProgram", "csrImmediateBitUpdateProgram", "csrImmediateMask", "csrReadInto"],
            _ => &[],
        };
        unfold.extend(extra.iter().map(|s| s.to_string()));
        unfold.extend(table_lemmas.get(spec.kind).cloned().unwrap_or_default());
        let mut prefix = String::new();
        if spec.imm == ImmKind::Csr {
            prefix.push_str("cases csr <;> ");
        }
        let lower = spec.kind.to_ascii_lowercase();
        if spec.uimm_in_rs1 {
            // One lemma per CSR keeps each declaration within the default
            // heartbeat limit. For each of the 32 constants both sides are
            // closed terms apart from `isX0 rd` and `rd` itself, so the proof
            // unfolds both sides, abstracts `isX0 rd` and closes each case by
            // `rfl`; `simp` on the closed bit-vector arithmetic is far slower.
            for (_, csr) in CSR_ORDER {
                let pat_csr = pat.replace(" csr ", &format!(" .{csr} "));
                writeln!(out, "/-- `{}` at `{csr}` is Jolt's `{}` recipe at `{csr}`. -/", spec.pattern, spec.kind).unwrap();
                writeln!(out, "theorem expand_{lower}_{csr} (rd : regidx) (uimm : BitVec 5) :").unwrap();
                writeln!(out, "    SourceInstruction.expand (.{pat_csr}) = {} rd .{csr} uimm := by", spec.gen).unwrap();
                writeln!(out, "  bitvec_cases uimm <;>").unwrap();
                writeln!(out, "  ( simp only [SourceInstruction.expand]").unwrap();
                writeln!(out, "    unfold ExpandedSource.ofProgram {}", unfold.join(" ")).unwrap();
                writeln!(out, "    generalize isX0 rd = b").unwrap();
                writeln!(out, "    cases b <;> rfl)").unwrap();
                writeln!(out).unwrap();
            }
            writeln!(out, "/-- `SourceInstruction.expand` on `{}` is Jolt's `{}` recipe. -/", spec.pattern, spec.kind).unwrap();
            writeln!(out, "theorem expand_{lower} {binders} :").unwrap();
            writeln!(out, "    SourceInstruction.expand (.{pat}) = {} {} := by", spec.gen, args.join(" ")).unwrap();
            let cases: Vec<String> = CSR_ORDER.iter().map(|(_, c)| format!("expand_{lower}_{c} rd uimm")).collect();
            writeln!(out, "  cases csr
  exacts [{}]", cases.join(", ")).unwrap();
            writeln!(out).unwrap();
            continue;
        }
        writeln!(out, "/-- `SourceInstruction.expand` on `{}` is Jolt's `{}` recipe. -/", spec.pattern, spec.kind).unwrap();
        writeln!(out, "theorem expand_{} {binders} :", spec.kind.to_ascii_lowercase()).unwrap();
        writeln!(out, "    SourceInstruction.expand (.{pat}) = {} {} := by", spec.gen, args.join(" ")).unwrap();
        writeln!(out, "  {prefix}recipe [{}]", unfold.join(", ")).unwrap();
        writeln!(out).unwrap();
    }
    writeln!(out, "/-- `SourceInstruction.expand` is Jolt's generated recipe for every source instruction. -/").unwrap();
    writeln!(out, "theorem expand_eq_generated (i : SourceInstruction) : i.expand = expand i := by").unwrap();
    writeln!(out, "  rcases i with (i | i) <;> cases i <;>").unwrap();
    let names: Vec<String> = specs.iter().map(|s| format!("expand_{}", s.kind.to_ascii_lowercase())).collect();
    writeln!(out, "    simp only [expand, {}]", names.join(", ")).unwrap();
    writeln!(out).unwrap();
    writeln!(out, "end ExpansionGen").unwrap();
    Ok(out)
}

// ---------------------------------------------------------------------------
// Driver.

struct Args {
    jolt_dir: PathBuf,
    out: PathBuf,
    lean_root: Option<PathBuf>,
    only: Option<String>,
}

fn parse_args() -> Result<Args, String> {
    let mut jolt = std::env::var_os("JOLT_DIR").map(PathBuf::from);
    let mut out = None;
    let mut lean_root = None;
    let mut only = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        let mut val = || it.next().ok_or_else(|| format!("{a} needs a value"));
        match a.as_str() {
            "--jolt-dir" => jolt = Some(PathBuf::from(val()?)),
            "--out" => out = Some(PathBuf::from(val()?)),
            "--lean-root" => lean_root = Some(PathBuf::from(val()?)),
            "--only" => only = Some(val()?),
            _ => return Err(format!("unknown argument {a}")),
        }
    }
    Ok(Args {
        jolt_dir: jolt.ok_or("--jolt-dir or JOLT_DIR is required")?,
        out: out.ok_or("--out is required")?,
        lean_root,
        only,
    })
}

fn jolt_commit(dir: &Path) -> String {
    std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

fn write(path: &Path, text: &str) -> Result<(), String> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    }
    std::fs::write(path, text).map_err(|e| format!("{}: {e}", path.display()))
}

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    rows::check_flag_lists()?;
    let commit = jolt_commit(&args.jolt_dir);
    let encs = encodings();
    let mut specs = specs();
    if let Some(only) = &args.only {
        let keep: BTreeSet<&str> = only.split(',').collect();
        specs.retain(|s| keep.contains(s.kind));
    }
    let mut tables = Tables::default();
    let mut results = Vec::new();
    let mut ok = true;
    let mut kinds_json = Vec::new();
    let mut checks = Vec::new();
    let start = Instant::now();
    for spec in &specs {
        let enc = encs.iter().find(|e| e.kind.name() == spec.kind);
        if enc.is_none() && spec.kind != "ANDN" {
            return Err(format!("{}: no encoding (build with feature zicsr-remaining for the CSR forms)", spec.kind));
        }
        let t0 = Instant::now();
        let r = sweep(spec, enc, &mut tables);
        let secs = t0.elapsed().as_secs_f64();
        let mut failures = Vec::new();
        for (fk, (t, _)) in &r.trees {
            if let Err(e) = t {
                failures.push(format!("{fk:?}: {e}"));
            }
        }
        // Every supported finite value must have a recipe.
        if spec.imm == ImmKind::Csr {
            for (addr, _) in CSR_ORDER {
                let us: Vec<Option<u8>> = if spec.uimm_in_rs1 { (0..32).map(Some).collect() } else { vec![None] };
                for u in us {
                    if !r.trees.contains_key(&(Some(addr), u)) {
                        failures.push(format!("no decoded input for CSR {addr:#x} uimm {u:?}"));
                    }
                }
            }
        }
        let non_csr_decode_errors = spec.imm != ImmKind::Csr && r.decode_errors > 0;
        if non_csr_decode_errors {
            failures.push(format!("{} words did not decode to {}", r.decode_errors, spec.kind));
        }
        if !r.unsupported_accepted.is_empty() {
            failures.push(format!("Jolt accepts unsupported CSRs: {:?}", r.unsupported_accepted));
        }
        let pass = failures.is_empty();
        ok &= pass;
        println!(
            "{:<16} {:>9} words {:>7.1}s  {}",
            spec.kind,
            r.inputs,
            secs,
            if pass { "ok".to_string() } else { format!("FAIL: {}", failures.join("; ")) }
        );
        checks.push(json!({
            "kind": spec.kind,
            "words": r.inputs,
            "decode_errors": r.decode_errors,
            "unsupported_csr_rejected": r.unsupported_rejected,
            "pass": pass,
            "failures": failures,
        }));
        let cases: Vec<Value> = r
            .trees
            .iter()
            .map(|(fk, (t, n))| {
                json!({
                    "csr": fk.0.map(csr_name),
                    "uimm": fk.1,
                    "words": n,
                    "tree": match t { Ok(t) => tree_json(t), Err(e) => json!({ "failure": e }) },
                })
            })
            .collect();
        kinds_json.push(json!({
            "kind": spec.kind,
            "lean": spec.pattern,
            "registers": spec.regs.iter().map(|r| r.name()).collect::<Vec<_>>(),
            "immediate": spec.imm.name(),
            "uimm_in_rs1": spec.uimm_in_rs1,
            "cases": cases,
        }));
        results.push(r);
    }
    println!("swept {} kinds in {:.1}s", specs.len(), start.elapsed().as_secs_f64());
    let tables_json: Vec<Value> = tables
        .list
        .iter()
        .map(|(w, k, v)| json!({ "width": w, "row_kind": k, "values": v.iter().map(|x| x.to_string()).collect::<Vec<_>>() }))
        .collect();
    write(
        &args.out.join("recipes.json"),
        &serde_json::to_string_pretty(&json!({ "jolt_commit": commit, "tables": tables_json, "kinds": kinds_json }))
            .unwrap(),
    )?;
    write(
        &args.out.join("summary.json"),
        &serde_json::to_string_pretty(&json!({ "jolt_commit": commit, "pass": ok, "checks": checks })).unwrap(),
    )?;
    if !ok {
        println!("FAIL: some recipes could not be derived; see {}", args.out.join("summary.json").display());
        return Ok(false);
    }
    if let Some(root) = &args.lean_root {
        if args.only.is_some() {
            println!("--only given: not writing Lean");
            return Ok(true);
        }
        let header = format!("-- Generated from a16z/jolt {commit}.\n");
        let gen = render_generated(&specs, &results, &tables, &header)?;
        let auto = render_auto(&specs, &results, &tables, &header)?;
        let equiv = render_equiv(&specs, &results, &tables, &header)?;
        write(&root.join("JoltConstraints/ExpansionGen/Generated.lean"), &gen)?;
        write(&root.join("JoltConstraints/ExpansionGen/Equiv.lean"), &equiv)?;
        write(&root.join("JoltBytecode/JoltISA/ExpansionsAutomated.lean"), &auto)?;
        println!("wrote the generated Lean under {}", root.display());
    }
    Ok(true)
}

fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(e) => {
            eprintln!("expansion-recipes: {e}");
            std::process::exit(2);
        }
    }
}
