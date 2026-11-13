//! I0(a): registered inline checks.
//!
//! * fixture hashes, recomputed exactly as Jolt's `compute_cases` does;
//! * operand templates and the exhaustive operand-uniformity check;
//! * write-before-read on the virtual register pool and per-inline write sets.

use std::collections::BTreeMap;
use std::time::Instant;

use jolt_program::expand::ExpansionAllocator;
use jolt_riscv::{
    CircuitFlags, Flags, JoltInstruction, JoltInstructionRow, NormalizedOperands, SourceInlineKey,
    SourceInstruction, SourceInstructionKind, SourceInstructionRow,
};
use rayon::prelude::*;
use serde::Deserialize;
use serde_json::{json, Value};
use tracer::InlineRegistration;

use crate::rows::{allocator_is_fresh, allocator_state, expand, rows_sha256};

/// The registrations in fixture order: sorted by (opcode, funct7, funct3, name).
pub fn registrations() -> Vec<&'static InlineRegistration> {
    let mut regs: Vec<_> = inventory::iter::<InlineRegistration>.into_iter().collect();
    regs.sort_by_key(|r| (r.opcode, r.funct7, r.funct3, r.name));
    regs
}

#[derive(Clone, Copy)]
pub struct Scenario {
    pub name: &'static str,
    pub address: usize,
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub is_compressed: bool,
}

/// The four scenarios of `jolt-inlines/fixtures/src/lib.rs`.
pub const SCENARIOS: [Scenario; 4] = [
    Scenario {
        name: "normal",
        address: 0x8000_0000,
        rd: 3,
        rs1: 1,
        rs2: 2,
        is_compressed: false,
    },
    Scenario {
        name: "compressed",
        address: 0x8000_0010,
        rd: 3,
        rs1: 1,
        rs2: 2,
        is_compressed: true,
    },
    Scenario {
        name: "rd_zero",
        address: 0x8000_0020,
        rd: 0,
        rs1: 1,
        rs2: 2,
        is_compressed: false,
    },
    Scenario {
        name: "aliased_operands",
        address: 0x8000_0030,
        rd: 5,
        rs1: 5,
        rs2: 5,
        is_compressed: false,
    },
];

pub fn inline_source(
    reg: &InlineRegistration,
    address: usize,
    rd: u8,
    rs1: u8,
    rs2: u8,
    is_compressed: bool,
) -> SourceInstruction {
    SourceInstruction::new(
        SourceInstructionKind::Inline,
        SourceInstructionRow {
            address,
            operands: NormalizedOperands {
                rd: Some(rd),
                rs1: Some(rs1),
                rs2: Some(rs2),
                imm: 0,
            },
            inline: Some(SourceInlineKey {
                opcode: reg.opcode as u8,
                funct3: reg.funct3 as u8,
                funct7: reg.funct7 as u8,
            }),
            is_compressed,
        },
    )
}

pub fn scenario_source(reg: &InlineRegistration, s: &Scenario) -> SourceInstruction {
    inline_source(reg, s.address, s.rd, s.rs1, s.rs2, s.is_compressed)
}

/// One fixture line. `error` exists from a16z/jolt#2414 on; it is absent
/// at the pin.
#[derive(Deserialize)]
pub struct FixtureCase {
    pub name: String,
    pub inline_name: String,
    pub opcode: u8,
    pub funct3: u8,
    pub funct7: u8,
    pub extension: String,
    pub row_count: usize,
    pub output_sha256: String,
    #[serde(default)]
    pub error: Option<String>,
}

pub fn parse_fixture(text: &str) -> Result<Vec<FixtureCase>, String> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).map_err(|e| format!("fixture line: {e}")))
        .collect()
}

/// Recomputes every fixture line and compares it field by field.
/// Returns (failures, rd_zero acceptance per inline name).
pub fn check_fixture(
    expected: &[FixtureCase],
) -> (Vec<String>, BTreeMap<String, Result<(), String>>, usize) {
    let mut failures = Vec::new();
    let mut rd_zero = BTreeMap::new();
    let mut computed = 0usize;
    let mut by_name: BTreeMap<&str, &FixtureCase> = BTreeMap::new();
    for c in expected {
        by_name.insert(c.name.as_str(), c);
    }
    let mut seen = 0usize;
    for reg in registrations() {
        for s in &SCENARIOS {
            let name = format!("{}::{}", reg.name, s.name);
            let mut alloc = ExpansionAllocator::new();
            let result = expand(&scenario_source(reg, s), &mut alloc);
            computed += 1;
            if s.name == "rd_zero" {
                rd_zero.insert(
                    reg.name.to_string(),
                    result.as_ref().map(|_| ()).map_err(|e| e.to_string()),
                );
            }
            let Some(exp) = by_name.get(name.as_str()) else {
                failures.push(format!("{name}: no fixture line"));
                continue;
            };
            seen += 1;
            let meta_ok = exp.inline_name == reg.name
                && u32::from(exp.opcode) == reg.opcode
                && u32::from(exp.funct3) == reg.funct3
                && u32::from(exp.funct7) == reg.funct7
                && exp.extension == format!("{:?}", reg.extension);
            if !meta_ok {
                failures.push(format!("{name}: registration metadata differs from fixture"));
            }
            match (&result, &exp.error) {
                (Ok(rows), None) => match rows_sha256(rows) {
                    Ok(h) if h == exp.output_sha256 && rows.len() == exp.row_count => {}
                    Ok(h) => failures.push(format!(
                        "{name}: sha256 {h} rows {} differ from fixture {} rows {}",
                        rows.len(),
                        exp.output_sha256,
                        exp.row_count
                    )),
                    Err(e) => failures.push(format!("{name}: hashing failed: {e}")),
                },
                (Ok(rows), Some(err)) => failures.push(format!(
                    "{name}: fixture expects error {err:?}, Jolt returned {} rows",
                    rows.len()
                )),
                (Err(e), None) => failures.push(format!(
                    "{name}: Jolt returned error {e}, fixture expects rows"
                )),
                (Err(e), Some(err)) => {
                    if e.to_string() != *err || exp.row_count != 0 || !exp.output_sha256.is_empty()
                    {
                        failures.push(format!(
                            "{name}: error text {:?} differs from fixture {err:?}",
                            e.to_string()
                        ));
                    }
                }
            }
            if result.is_ok() && !allocator_is_fresh(&alloc) {
                failures.push(format!(
                    "{name}: allocator not restored: {}",
                    allocator_state(&alloc)
                ));
            }
        }
    }
    if seen != expected.len() {
        failures.push(format!(
            "fixture has {} lines, the driver matched {seen}",
            expected.len()
        ));
    }
    (failures, rd_zero, computed)
}

/// A register field of a template row.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reg {
    Param(u8), // 1 = rs1, 2 = rs2, 3 = rs3
    Lit(u8),
}

impl Reg {
    pub fn json(self) -> Value {
        match self {
            Reg::Param(i) => json!({ "param": format!("rs{i}") }),
            Reg::Lit(n) => json!({ "lit": n }),
        }
    }
    fn instantiate(self, triple: [u8; 3]) -> u8 {
        match self {
            Reg::Param(i) => triple[usize::from(i) - 1],
            Reg::Lit(n) => n,
        }
    }
}

#[derive(Clone)]
pub struct TemplateRow {
    pub row: JoltInstructionRow, // the row for triple A; registers replaced below
    pub rd: Option<Reg>,
    pub rs1: Option<Reg>,
    pub rs2: Option<Reg>,
}

impl TemplateRow {
    pub fn instantiate(&self, triple: [u8; 3]) -> JoltInstructionRow {
        let mut row = self.row;
        row.operands = NormalizedOperands {
            rd: self.rd.map(|r| r.instantiate(triple)),
            rs1: self.rs1.map(|r| r.instantiate(triple)),
            rs2: self.rs2.map(|r| r.instantiate(triple)),
            imm: self.row.operands.imm,
        };
        row
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AllocCase {
    Normal,
    RdZero,
}

impl AllocCase {
    pub fn name(self) -> &'static str {
        match self {
            AllocCase::Normal => "normal",
            AllocCase::RdZero => "rd_zero",
        }
    }
}

pub const TRIPLE_A: [u8; 3] = [11, 12, 13];
pub const TRIPLE_B: [u8; 3] = [21, 22, 23];
pub const TEMPLATE_ADDRESS: usize = 0x8000_0000;

/// The source operands for a triple: in the rd_zero case the third entry is
/// ignored and rd is x0.
fn source_for(reg: &InlineRegistration, case: AllocCase, t: [u8; 3]) -> SourceInstruction {
    let rd = match case {
        AllocCase::Normal => t[2],
        AllocCase::RdZero => 0,
    };
    inline_source(reg, TEMPLATE_ADDRESS, rd, t[0], t[1], false)
}

fn expand_checked(
    reg: &InlineRegistration,
    case: AllocCase,
    t: [u8; 3],
) -> Result<Vec<JoltInstructionRow>, String> {
    let mut alloc = ExpansionAllocator::new();
    let rows = expand(&source_for(reg, case, t), &mut alloc).map_err(|e| format!("{e:?}"))?;
    if !allocator_is_fresh(&alloc) {
        return Err(format!(
            "allocator not restored: {}",
            allocator_state(&alloc)
        ));
    }
    Ok(rows)
}

fn classify(
    a: Option<u8>,
    b: Option<u8>,
    case: AllocCase,
    row: usize,
    field: &str,
) -> Result<Option<Reg>, String> {
    match (a, b) {
        (None, None) => Ok(None),
        (Some(a), Some(b)) => {
            for i in 0..3u8 {
                if case == AllocCase::RdZero && i == 2 {
                    continue;
                }
                let idx = usize::from(i);
                if a == TRIPLE_A[idx] && b == TRIPLE_B[idx] {
                    return Ok(Some(Reg::Param(i + 1)));
                }
            }
            if a == b {
                Ok(Some(Reg::Lit(a)))
            } else {
                Err(format!(
                    "row {row} field {field}: {a} under triple A, {b} under triple B; neither a parameter nor a literal"
                ))
            }
        }
        _ => Err(format!("row {row} field {field}: present under one triple only")),
    }
}

pub fn build_template(
    reg: &InlineRegistration,
    case: AllocCase,
) -> Result<Vec<TemplateRow>, String> {
    let a = expand_checked(reg, case, TRIPLE_A)?;
    let b = expand_checked(reg, case, TRIPLE_B)?;
    if a.len() != b.len() {
        return Err(format!("{} rows under triple A, {} under triple B", a.len(), b.len()));
    }
    let mut out = Vec::with_capacity(a.len());
    for (i, (ra, rb)) in a.iter().zip(&b).enumerate() {
        let same_meta = ra.instruction_kind == rb.instruction_kind
            && ra.operands.imm == rb.operands.imm
            && ra.address == rb.address
            && ra.virtual_sequence_remaining == rb.virtual_sequence_remaining
            && ra.is_first_in_sequence == rb.is_first_in_sequence
            && ra.is_compressed == rb.is_compressed;
        if !same_meta {
            return Err(format!("row {i}: kind, imm or metadata differ between triples"));
        }
        out.push(TemplateRow {
            row: *ra,
            rd: classify(ra.operands.rd, rb.operands.rd, case, i, "rd")?,
            rs1: classify(ra.operands.rs1, rb.operands.rs1, case, i, "rs1")?,
            rs2: classify(ra.operands.rs2, rb.operands.rs2, case, i, "rs2")?,
        });
    }
    Ok(out)
}

pub fn all_triples(case: AllocCase) -> Vec<[u8; 3]> {
    let mut v = Vec::new();
    for rs1 in 0..32u8 {
        for rs2 in 0..32u8 {
            match case {
                AllocCase::Normal => {
                    for rs3 in 1..32u8 {
                        v.push([rs1, rs2, rs3]);
                    }
                }
                AllocCase::RdZero => v.push([rs1, rs2, 0]),
            }
        }
    }
    v
}

/// The first triple whose expansion differs from the template, if any.
pub fn check_uniform(
    reg: &InlineRegistration,
    case: AllocCase,
    template: &[TemplateRow],
) -> (usize, Option<Value>) {
    let triples = all_triples(case);
    let n = triples.len();
    let first_bad = triples
        .par_iter()
        .filter_map(|t| {
            let rows = match expand_checked(reg, case, *t) {
                Ok(r) => r,
                Err(e) => return Some(json!({"triple": t, "error": e})),
            };
            if rows.len() != template.len() {
                return Some(json!({
                    "triple": t,
                    "detail": format!("{} rows, template has {}", rows.len(), template.len())
                }));
            }
            for (i, (row, tr)) in rows.iter().zip(template).enumerate() {
                let want = tr.instantiate(*t);
                if *row != want {
                    return Some(json!({
                        "triple": t,
                        "row": i,
                        "detail": format!("got {row:?}, template gives {want:?}")
                    }));
                }
            }
            None
        })
        .find_first(|_| true);
    (n, first_bad)
}

pub const POOL: std::ops::RangeInclusive<u8> = 48..=127;
pub const INSTRUCTION_TEMPS: std::ops::RangeInclusive<u8> = 40..=47;
pub const RESERVED: std::ops::RangeInclusive<u8> = 32..=39;

/// Write-before-read over one row sequence. A present rs1 or rs2 is a read
/// and a present rd is a write (see the README table).
pub fn write_before_read(rows: &[JoltInstructionRow]) -> Value {
    let mut written = [false; 128];
    let mut pool_violations = Vec::new();
    let mut temp_reads_before_write = Vec::new();
    for (i, row) in rows.iter().enumerate() {
        for (field, r) in [("rs1", row.operands.rs1), ("rs2", row.operands.rs2)] {
            let Some(r) = r else { continue };
            if written[usize::from(r)] {
                continue;
            }
            if POOL.contains(&r) {
                pool_violations.push(json!({"row": i, "field": field, "register": r,
                                            "kind": row.instruction_kind.name()}));
            } else if INSTRUCTION_TEMPS.contains(&r) {
                temp_reads_before_write.push(json!({"row": i, "field": field, "register": r,
                                                    "kind": row.instruction_kind.name()}));
            }
        }
        if let Some(rd) = row.operands.rd {
            written[usize::from(rd)] = true;
        }
    }
    json!({
        "pool_reads_before_write": pool_violations,
        "instruction_temp_reads_before_write": temp_reads_before_write,
    })
}

/// Registers a template writes, by class, and whether it has store rows.
pub fn write_sets(template: &[TemplateRow]) -> Value {
    let mut arch_params = std::collections::BTreeSet::new();
    let mut arch_lits = std::collections::BTreeSet::new();
    let mut reserved = std::collections::BTreeSet::new();
    let mut temps = std::collections::BTreeSet::new();
    let mut pool = std::collections::BTreeSet::new();
    let mut stores = 0usize;
    let mut loads = 0usize;
    for tr in template {
        let cf = JoltInstruction::from(tr.row).circuit_flags();
        if cf.get(CircuitFlags::Store) {
            stores += 1;
        }
        if cf.get(CircuitFlags::Load) {
            loads += 1;
        }
        match tr.rd {
            None => {}
            Some(Reg::Param(i)) => {
                arch_params.insert(format!("rs{i}"));
            }
            Some(Reg::Lit(n)) if n < 32 => {
                arch_lits.insert(n);
            }
            Some(Reg::Lit(n)) if RESERVED.contains(&n) => {
                reserved.insert(n);
            }
            Some(Reg::Lit(n)) if INSTRUCTION_TEMPS.contains(&n) => {
                temps.insert(n);
            }
            Some(Reg::Lit(n)) => {
                pool.insert(n);
            }
        }
    }
    json!({
        "architectural_params": arch_params,
        "architectural_literals": arch_lits,
        "vr32_39": reserved,
        "vr40_47": temps,
        "pool_vr48_127_count": pool.len(),
        "pool_vr48_127_min": pool.iter().next(),
        "pool_vr48_127_max": pool.iter().next_back(),
        "store_rows": stores,
        "load_rows": loads,
    })
}

pub fn template_json(template: &[TemplateRow]) -> Vec<Value> {
    let r = |x: Option<Reg>| x.map_or(Value::Null, Reg::json);
    template
        .iter()
        .map(|tr| {
            json!({
                "kind": tr.row.instruction_kind.name(),
                "address": tr.row.address as u64,
                "rd": r(tr.rd),
                "rs1": r(tr.rs1),
                "rs2": r(tr.rs2),
                "imm": tr.row.operands.imm.to_string(),
                "vsr": tr.row.virtual_sequence_remaining,
                "first": tr.row.is_first_in_sequence,
                "compressed": tr.row.is_compressed,
            })
        })
        .collect()
}

/// The twelve inlines that the write-before-read check gates (spec section 7).
pub const IN_SCOPE: [&str; 12] = [
    "SHA256_INLINE",
    "SHA256_INIT_INLINE",
    "KECCAK256_INLINE",
    "KECCAK256_ABSORB_PERMUTE_INLINE",
    "BLAKE2_INLINE",
    "SECP256K1_MULQ",
    "SECP256K1_SQUAREQ",
    "SECP256K1_DIVQ",
    "SECP256K1_MULR",
    "SECP256K1_SQUARER",
    "SECP256K1_DIVR",
    "SECP256K1_GLVR_ADV",
];

pub fn timed<T>(f: impl FnOnce() -> T) -> (T, f64) {
    let start = Instant::now();
    let v = f();
    (v, start.elapsed().as_secs_f64())
}
