//! constraint-gen: T3 constraint data generated from a Jolt checkout.
//!
//! The binary reads, from Jolt's own code,
//!
//! - the RV64 R1CS rows (`rv64::rv64_trace_constraints` in jolt-claims),
//! - the four per-cycle relations that `zklean-extractor` also exports
//!   (RAM and register read/write checking, instruction input virtualization,
//!   and the Spartan shift), from their `unbatched_relation` functions,
//! - per instruction kind, the circuit flags, instruction flags, lookup table
//!   and RAF flag (`jolt_riscv::Flags`, `InstructionLookupTable`,
//!   `InstructionRafFlag::extract`),
//!
//! and writes them as Lean data under `JoltConstraints/ConstraintGen/Generated/`.
//! It also writes `summary.json` with every check it ran. See
//! `scripts/expansion-parity/CONSTRAINT-GEN.md`.
//!
//! Exit status: 0 when every check passes, 1 when a check fails, 2 when the
//! binary cannot run.

#![allow(dead_code)]

#[path = "../rows.rs"]
mod rows;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use jolt_claims::protocols::composed::r1cs::rv64::{
    self, NUM_CONSTRAINTS_PER_CYCLE, NUM_EQ_CONSTRAINTS, NUM_VARS_PER_CYCLE,
    RV64_CONSTRAINT_NAMES, RV64_VARIABLE_NAMES, V_CONST,
};
use jolt_claims::protocols::jolt::relations::{
    instruction::InputVirtualization, ram::ReadWriteChecking as RamReadWriteChecking,
    registers::ReadWriteChecking as RegistersReadWriteChecking, spartan::Shift,
};
use jolt_claims::protocols::jolt::{
    JoltPolynomialId, UnbatchedClaimExpr, UnbatchedRelation,
};
use jolt_field::{Fr, Ring};
use jolt_lookup_tables::{InstructionLookupTable, LookupTableKind};
use jolt_r1cs::SparseRow;
use jolt_riscv::{
    Flags, JoltInstruction, JoltInstructionKind, JoltInstructionRow,
    NormalizedOperands, CIRCUIT_FLAGS,
};
use serde_json::{json, Value};

use crate::rows::{check_flag_lists, Annotator, INSTRUCTION_FLAGS};

struct Args {
    jolt_dir: PathBuf,
    out: PathBuf,
    lean_root: Option<PathBuf>,
}

fn parse_args() -> Result<Args, String> {
    let mut jolt = None;
    let mut out = None;
    let mut lean_root = None;
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        let mut val = || it.next().ok_or(format!("{flag} needs a value"));
        match flag.as_str() {
            "--jolt-dir" => jolt = Some(PathBuf::from(val()?)),
            "--out" => out = Some(PathBuf::from(val()?)),
            "--lean-root" => lean_root = Some(PathBuf::from(val()?)),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    Ok(Args {
        jolt_dir: jolt
            .or_else(|| std::env::var_os("JOLT_DIR").map(PathBuf::from))
            .ok_or("--jolt-dir or JOLT_DIR is required")?,
        out: out.ok_or("--out is required")?,
        lean_root,
    })
}

/// Checks recorded in summary.json; any failure makes the exit status 1.
#[derive(Default)]
struct Checks {
    entries: Vec<Value>,
    failed: bool,
}

impl Checks {
    fn record(&mut self, name: &str, ok: bool, detail: Value) {
        if !ok {
            self.failed = true;
            eprintln!("constraint-gen: check {name} FAILED: {detail}");
        }
        self.entries.push(json!({ "name": name, "ok": ok, "detail": detail }));
    }
}

// ---------------------------------------------------------------------------
// R1CS rows
// ---------------------------------------------------------------------------

/// The integer a field coefficient stands for. Fr's `Display` prints the
/// canonical representative; the result is confirmed with `Fr::from_i128`.
fn coefficient(value: Fr) -> Result<i128, String> {
    let positive = format!("{value}");
    let negative = format!("-{}", -value);
    for text in [positive, negative] {
        if let Ok(c) = text.parse::<i128>() {
            if Fr::from_i128(c) == value {
                return Ok(c);
            }
        }
    }
    Err(format!("coefficient {value} is not a small integer"))
}

struct LcTerm {
    var: &'static str,
    coeff: i128,
}

fn linear_combination(row: &SparseRow<Fr>) -> Result<Vec<LcTerm>, String> {
    row.iter()
        .map(|&(var, c)| {
            let name = RV64_VARIABLE_NAMES
                .get(var)
                .copied()
                .ok_or(format!("variable index {var} out of range"))?;
            Ok(LcTerm { var: name, coeff: coefficient(c)? })
        })
        .collect()
}

struct R1csRow {
    name: &'static str,
    a: Vec<LcTerm>,
    b: Vec<LcTerm>,
    c: Vec<LcTerm>,
}

fn r1cs_rows(checks: &mut Checks) -> Result<Vec<R1csRow>, String> {
    let full = rv64::rv64_trace_constraints::<Fr>();
    let outer = rv64::rv64_spartan_outer_constraints::<Fr>();
    checks.record(
        "r1cs_shape",
        full.num_constraints == NUM_CONSTRAINTS_PER_CYCLE
            && full.num_vars == NUM_VARS_PER_CYCLE
            && full.a.len() == NUM_CONSTRAINTS_PER_CYCLE
            && full.b.len() == NUM_CONSTRAINTS_PER_CYCLE
            && full.c.len() == NUM_CONSTRAINTS_PER_CYCLE
            && RV64_CONSTRAINT_NAMES.len() == NUM_CONSTRAINTS_PER_CYCLE,
        json!({
            "constraints": full.num_constraints,
            "vars": full.num_vars,
            "eq_constraints": NUM_EQ_CONSTRAINTS,
        }),
    );
    // The Spartan outer matrices are the first NUM_EQ_CONSTRAINTS rows.
    let prefix = outer.num_constraints == NUM_EQ_CONSTRAINTS
        && outer.a[..] == full.a[..NUM_EQ_CONSTRAINTS]
        && outer.b[..] == full.b[..NUM_EQ_CONSTRAINTS]
        && outer.c[..] == full.c[..NUM_EQ_CONSTRAINTS];
    checks.record("r1cs_outer_is_prefix", prefix, json!(null));
    let names: BTreeSet<_> = RV64_VARIABLE_NAMES.iter().collect();
    checks.record(
        "r1cs_variable_names_unique",
        names.len() == NUM_VARS_PER_CYCLE && RV64_VARIABLE_NAMES[V_CONST] == "One",
        json!({ "vars": RV64_VARIABLE_NAMES.to_vec() }),
    );
    let mut rows = Vec::new();
    for i in 0..full.num_constraints {
        rows.push(R1csRow {
            name: RV64_CONSTRAINT_NAMES[i],
            a: linear_combination(&full.a[i])?,
            b: linear_combination(&full.b[i])?,
            c: linear_combination(&full.c[i])?,
        });
    }
    Ok(rows)
}

fn lean_lc(terms: &[LcTerm]) -> String {
    let items: Vec<String> = terms
        .iter()
        .map(|t| format!("(.{}, {})", t.var, t.coeff))
        .collect();
    format!("[{}]", items.join(", "))
}

fn header(commit: &str, what: &str) -> String {
    format!(
        "-- Generated by scripts/expansion-parity/src/bin/constraint-gen.rs from\n\
         -- a16z/jolt {commit}. Do not edit; rerun\n\
         -- scripts/expansion-parity/run-constraint-gen.sh and commit the result.\n\
         -- {what}\n"
    )
}

fn r1cs_lean(commit: &str, rows: &[R1csRow]) -> String {
    let mut s = header(commit, "R1CS rows: crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs.");
    s.push_str(
        "import JoltConstraints.ConstraintGen.Types\n\n\
         set_option autoImplicit false\n\n\
         namespace JoltConstraints.ConstraintGen.Generated\n\n",
    );
    s.push_str(
        "/-- Jolt's per-cycle R1CS variables, `RV64_VARIABLE_NAMES` in column order. -/\n\
         inductive R1CSVar where\n",
    );
    for (i, name) in RV64_VARIABLE_NAMES.iter().enumerate() {
        let _ = writeln!(s, "  /-- Column {i}. -/\n  | {name}");
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");
    let mut defs = Vec::new();
    for (i, row) in rows.iter().enumerate() {
        let def = format!("rv64Row{i:02}");
        let _ = writeln!(
            s,
            "/-- Row {i}, `{}`. -/\ndef {def} : R1CSRow R1CSVar where\n  \
             name := \"{}\"\n  a := {}\n  b := {}\n  c := {}\n",
            row.name,
            row.name,
            lean_lc(&row.a),
            lean_lc(&row.b),
            lean_lc(&row.c)
        );
        defs.push(def);
    }
    let _ = writeln!(
        s,
        "/-- All {} rows, in Jolt's order. -/\ndef rv64Rows : List (R1CSRow R1CSVar) :=\n  [{}]\n",
        rows.len(),
        defs.join(", ")
    );
    s.push_str("end JoltConstraints.ConstraintGen.Generated\n");
    s
}

// ---------------------------------------------------------------------------
// The four relations
// ---------------------------------------------------------------------------

/// `Foo(Bar)` -> `Foo_Bar`, as `zklean-extractor` names identifiers.
fn ident(debug: String) -> String {
    debug.replace('(', "_").replace(')', "")
}

fn poly_ident(p: JoltPolynomialId) -> (String, &'static str) {
    match p {
        JoltPolynomialId::Committed(c) => (ident(format!("{c:?}")), "committed"),
        JoltPolynomialId::Virtual(v) => (ident(format!("{v:?}")), "virtual"),
    }
}

struct RelationNames {
    relations: BTreeSet<String>,
    polys: BTreeMap<String, &'static str>,
    weights: BTreeSet<String>,
}

fn collect_polys(e: &UnbatchedClaimExpr, names: &mut RelationNames) -> Result<(), String> {
    match e {
        UnbatchedClaimExpr::Constant(_) => Ok(()),
        UnbatchedClaimExpr::Polynomial(p) => {
            let (id, kind) = poly_ident(*p);
            if let Some(prev) = names.polys.insert(id.clone(), kind) {
                if prev != kind {
                    return Err(format!("polynomial name {id} is both committed and virtual"));
                }
            }
            Ok(())
        }
        UnbatchedClaimExpr::Add(l, r) | UnbatchedClaimExpr::Mul(l, r) | UnbatchedClaimExpr::Sub(l, r) => {
            collect_polys(l, names)?;
            collect_polys(r, names)
        }
    }
}

fn lean_expr(e: &UnbatchedClaimExpr) -> String {
    match e {
        UnbatchedClaimExpr::Constant(c) => format!("(.const ({c}))"),
        UnbatchedClaimExpr::Polynomial(p) => format!("(.poly .{})", poly_ident(*p).0),
        UnbatchedClaimExpr::Add(l, r) => format!("(.add {} {})", lean_expr(l), lean_expr(r)),
        UnbatchedClaimExpr::Mul(l, r) => format!("(.mul {} {})", lean_expr(l), lean_expr(r)),
        UnbatchedClaimExpr::Sub(l, r) => format!("(.sub {} {})", lean_expr(l), lean_expr(r)),
    }
}

/// The relations in the order `zklean-extractor`'s `extracted_claims` lists them,
/// with the Lean definition name of each.
fn relations() -> Vec<(&'static str, UnbatchedRelation)> {
    vec![
        ("ramReadWriteChecking", RamReadWriteChecking::unbatched_relation()),
        ("registersReadWriteChecking", RegistersReadWriteChecking::unbatched_relation()),
        ("instructionInputVirtualization", InputVirtualization::unbatched_relation()),
        ("spartanShift", Shift::unbatched_relation()),
    ]
}

/// The Jolt types whose `unbatched_relation` `relations()` calls, in order.
const RELATION_TYPES: [&str; 4] =
    ["RamReadWriteChecking", "RegistersReadWriteChecking", "InputVirtualization", "Shift"];

/// The `X::unbatched_relation()` calls in the body of `extracted_claims` in
/// `zklean-extractor/src/sumchecks.rs`, in order. The generator cannot link
/// the extractor (a binary crate), so it reads the selection from its source.
fn extractor_relation_types(jolt_dir: &Path) -> Result<Vec<String>, String> {
    let path = jolt_dir.join("zklean-extractor/src/sumchecks.rs");
    let src = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let start = src
        .find("fn extracted_claims()")
        .ok_or_else(|| format!("{}: no fn extracted_claims()", path.display()))?;
    let body = &src[start..];
    let open = body.find('{').ok_or("extracted_claims: no body")?;
    let mut depth = 0usize;
    let mut end = None;
    for (i, ch) in body[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = Some(open + i);
                    break;
                }
            }
            _ => {}
        }
    }
    let body = &body[open..end.ok_or("extracted_claims: unbalanced braces")?];
    // Every piece before a `::unbatched_relation()` call ends with the type name.
    let pieces: Vec<&str> = body.split("::unbatched_relation()").collect();
    let types = pieces[..pieces.len() - 1]
        .iter()
        .map(|piece| {
            let start = piece
                .rfind(|c: char| !(c.is_alphanumeric() || c == '_'))
                .map_or(0, |i| i + 1);
            piece[start..].to_string()
        })
        .collect();
    Ok(types)
}

fn relations_lean(
    commit: &str,
    jolt_dir: &Path,
    checks: &mut Checks,
) -> Result<(String, Value), String> {
    let rels = relations();
    let extractor = extractor_relation_types(jolt_dir)?;
    checks.record(
        "relations_match_extractor",
        extractor == RELATION_TYPES,
        json!({ "extractor": extractor, "generated": RELATION_TYPES }),
    );
    let mut names = RelationNames {
        relations: BTreeSet::new(),
        polys: BTreeMap::new(),
        weights: BTreeSet::new(),
    };
    for (_, rel) in &rels {
        names.relations.insert(ident(format!("{:?}", rel.output_relation)));
        for claim in &rel.claims {
            names.relations.insert(ident(format!("{:?}", claim.input_relation)));
            names.weights.insert(ident(format!("{:?}", claim.output_weight)));
            collect_polys(&claim.input, &mut names)?;
            collect_polys(&claim.output, &mut names)?;
        }
    }
    let mut s = header(
        commit,
        "The four relations of zklean-extractor/src/sumchecks.rs (`extracted_claims`):\n\
         -- crates/jolt-claims/src/protocols/jolt/relations/{ram,registers}/read_write_checking.rs,\n\
         -- instruction/input_virtualization.rs and spartan/shift.rs (`unbatched_relation`).",
    );
    s.push_str(
        "import JoltConstraints.ConstraintGen.Types\n\n\
         set_option autoImplicit false\n\n\
         namespace JoltConstraints.ConstraintGen.Generated\n\n",
    );
    s.push_str("/-- The `JoltRelationId`s the four relations name. -/\ninductive RelationId where\n");
    for r in &names.relations {
        let _ = writeln!(s, "  | {r}");
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");
    s.push_str(
        "/-- The `JoltPolynomialId`s the four relations name, without the\n\
         `Committed`/`Virtual` wrapper (the docstring says which). -/\ninductive RelationPoly where\n",
    );
    for (p, kind) in &names.polys {
        let _ = writeln!(s, "  /-- A {kind} polynomial. -/\n  | {p}");
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");
    s.push_str("/-- The `JoltDerivedId`s the claims use as output weights. -/\ninductive RelationWeight where\n");
    for w in &names.weights {
        let _ = writeln!(s, "  | {w}");
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");
    let mut summary = Vec::new();
    for (lean_name, rel) in &rels {
        let _ = writeln!(
            s,
            "/-- `{:?}`, {} claims. -/\ndef {lean_name} : Relation RelationId RelationPoly RelationWeight where\n  \
             outputRelation := .{}\n  claims := [",
            rel.output_relation,
            rel.claims.len(),
            ident(format!("{:?}", rel.output_relation))
        );
        for (k, claim) in rel.claims.iter().enumerate() {
            let sep = if k + 1 == rel.claims.len() { "]" } else { "," };
            let _ = writeln!(
                s,
                "    {{ inputRelation := .{}\n      input := {}\n      output := {}\n      \
                 outputWeight := .{}\n      offset := {} }}{sep}",
                ident(format!("{:?}", claim.input_relation)),
                lean_expr(&claim.input),
                lean_expr(&claim.output),
                ident(format!("{:?}", claim.output_weight)),
                claim.offset
            );
        }
        s.push('\n');
        summary.push(json!({ "relation": lean_name, "claims": rel.claims.len() }));
    }
    s.push_str("end JoltConstraints.ConstraintGen.Generated\n");
    checks.record(
        "relations_count",
        rels.len() == 4,
        json!({ "relations": summary.clone() }),
    );
    Ok((s, json!(summary)))
}

// ---------------------------------------------------------------------------
// Per-kind flags, lookup table and RAF flag
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Stamp {
    vsr: Option<u16>,
    first: bool,
    compressed: bool,
}

const CANONICAL: Stamp = Stamp { vsr: None, first: false, compressed: false };

/// The stamps written to Lean: every combination of four sequence positions
/// (outside a sequence, last row, and two interior rows) with the two booleans.
fn emitted_stamps() -> Vec<Stamp> {
    let mut v = Vec::new();
    for vsr in [None, Some(0u16), Some(1), Some(u16::MAX)] {
        for first in [false, true] {
            for compressed in [false, true] {
                v.push(Stamp { vsr, first, compressed });
            }
        }
    }
    v
}

/// The stamps the uniformity check runs on: no sequence, every
/// `virtual_sequence_remaining` up to 1024 and the maximum, with both booleans.
fn checked_stamps() -> Vec<Stamp> {
    let mut vsrs: Vec<Option<u16>> = vec![None];
    vsrs.extend((0..=1024u16).map(Some));
    vsrs.push(Some(u16::MAX));
    let mut v = Vec::new();
    for vsr in vsrs {
        for first in [false, true] {
            for compressed in [false, true] {
                v.push(Stamp { vsr, first, compressed });
            }
        }
    }
    v
}

/// The stamp whose flags Lean uses for `stamp`: a nonzero sequence count
/// becomes 1, everything else stays.
fn representative(stamp: Stamp) -> Stamp {
    Stamp { vsr: stamp.vsr.map(|n| if n == 0 { 0 } else { 1 }), ..stamp }
}

fn row_of(kind: JoltInstructionKind, stamp: Stamp) -> JoltInstructionRow {
    JoltInstructionRow {
        instruction_kind: kind,
        address: 0x8000_0000,
        operands: NormalizedOperands { rd: Some(5), rs1: Some(6), rs2: Some(7), imm: 0 },
        virtual_sequence_remaining: stamp.vsr,
        is_first_in_sequence: stamp.first,
        is_compressed: stamp.compressed,
        ..Default::default()
    }
}

fn circuit_set(row: &JoltInstructionRow) -> BTreeSet<usize> {
    let cf = JoltInstruction::from(*row).circuit_flags();
    CIRCUIT_FLAGS.iter().enumerate().filter(|(_, f)| cf.get(**f)).map(|(i, _)| i).collect()
}

fn instruction_set(row: &JoltInstructionRow) -> BTreeSet<usize> {
    let inf = JoltInstruction::from(*row).instruction_flags();
    INSTRUCTION_FLAGS.iter().enumerate().filter(|(_, f)| inf.get(**f)).map(|(i, _)| i).collect()
}

fn table_of(row: &JoltInstructionRow) -> Option<&'static str> {
    let t: Option<LookupTableKind<64>> = JoltInstruction::from(*row).lookup_table();
    t.map(<&'static str>::from)
}

struct KindData {
    name: &'static str,
    circuit: BTreeSet<usize>,
    instruction: BTreeSet<usize>,
    table: Option<&'static str>,
    raf: bool,
}

fn circuit_names(set: &BTreeSet<usize>) -> Vec<String> {
    set.iter().map(|i| format!("{:?}", CIRCUIT_FLAGS[*i])).collect()
}

fn instruction_names(set: &BTreeSet<usize>) -> Vec<String> {
    set.iter().map(|i| format!("{:?}", INSTRUCTION_FLAGS[*i])).collect()
}

fn kind_tables(
    checks: &mut Checks,
) -> Result<(Vec<KindData>, Vec<(Stamp, BTreeSet<usize>)>), String> {
    let annotator = Annotator::new()?;
    let mut data = Vec::new();
    for &kind in JoltInstructionKind::ALL {
        let row = row_of(kind, CANONICAL);
        data.push(KindData {
            name: kind.name(),
            circuit: circuit_set(&row),
            instruction: instruction_set(&row),
            table: table_of(&row),
            raf: annotator.raf(&row)?,
        });
    }
    let names: BTreeSet<_> = data.iter().map(|d| d.name).collect();
    checks.record(
        "kind_names_unique",
        names.len() == data.len(),
        json!({ "kinds": data.len() }),
    );

    // Stamp flags: for each stamp, the flags it adds beyond the canonical ones,
    // over all kinds except NoOp (whose flags Jolt fixes regardless of stamp).
    // The check below requires every kind's flags to be exactly its canonical
    // flags plus these, and its other outputs not to depend on the stamp.
    let mut failures = Vec::new();
    let mut stamp_sets: BTreeMap<Stamp, BTreeSet<usize>> = BTreeMap::new();
    let stamps = checked_stamps();
    for &stamp in &stamps {
        let mut added = BTreeSet::new();
        for (&kind, d) in JoltInstructionKind::ALL.iter().zip(&data) {
            if kind == JoltInstructionKind::NoOp {
                continue;
            }
            let cs = circuit_set(&row_of(kind, stamp));
            added.extend(cs.difference(&d.circuit).copied());
        }
        stamp_sets.insert(stamp, added);
    }
    for &stamp in &stamps {
        let added = &stamp_sets[&stamp];
        for (&kind, d) in JoltInstructionKind::ALL.iter().zip(&data) {
            let row = row_of(kind, stamp);
            let expected: BTreeSet<usize> = if kind == JoltInstructionKind::NoOp {
                d.circuit.clone()
            } else {
                d.circuit.union(added).copied().collect()
            };
            let cs = circuit_set(&row);
            let same_rest = instruction_set(&row) == d.instruction && table_of(&row) == d.table;
            if cs != expected || !same_rest {
                if failures.len() < 20 {
                    failures.push(json!({
                        "kind": d.name,
                        "stamp": format!("{stamp:?}"),
                        "flags": circuit_names(&cs),
                        "expected": circuit_names(&expected),
                        "other_outputs_equal": same_rest,
                    }));
                }
            }
        }
    }
    // Lean reads a nonzero sequence count as 1 (`stampClass` in
    // ConstraintGen/Semantics.lean), so each stamp must add exactly the flags of
    // its representative: the same stamp with a nonzero count replaced by 1.
    for &stamp in &stamps {
        let rep = representative(stamp);
        if stamp_sets[&stamp] != stamp_sets[&rep] && failures.len() < 20 {
            failures.push(json!({
                "stamp": format!("{stamp:?}"),
                "flags": circuit_names(&stamp_sets[&stamp]),
                "representative": format!("{rep:?}"),
                "representative_flags": circuit_names(&stamp_sets[&rep]),
            }));
        }
    }
    checks.record(
        "stamp_uniformity",
        failures.is_empty(),
        json!({ "stamps": stamps.len(), "kinds": data.len(), "failures": failures }),
    );
    // RAF depends on the stamp only through the circuit flags; check it too.
    let mut raf_failures = Vec::new();
    for stamp in stamps.iter().copied() {
        for (&kind, d) in JoltInstructionKind::ALL.iter().zip(&data) {
            if kind == JoltInstructionKind::NoOp && stamp != CANONICAL {
                // JoltTraceRow::new rejects a NoOp carrying sequence metadata.
                continue;
            }
            let raf = annotator.raf(&row_of(kind, stamp))?;
            if raf != d.raf && raf_failures.len() < 20 {
                raf_failures.push(json!({ "kind": d.name, "stamp": format!("{stamp:?}") }));
            }
        }
    }
    checks.record(
        "raf_stamp_independent",
        raf_failures.is_empty(),
        json!({ "failures": raf_failures }),
    );
    let emitted = emitted_stamps()
        .into_iter()
        .map(|st| (st, stamp_sets[&st].clone()))
        .collect();
    Ok((data, emitted))
}

fn lean_list(items: &[String]) -> String {
    let v: Vec<String> = items.iter().map(|s| format!(".{s}")).collect();
    format!("[{}]", v.join(", "))
}

fn kinds_lean(commit: &str, data: &[KindData], stamps: &[(Stamp, BTreeSet<usize>)]) -> String {
    let mut s = header(
        commit,
        "Per-kind flags, lookup table and RAF flag: crates/jolt-riscv (`Flags`),\n\
         -- crates/jolt-lookup-tables (`InstructionLookupTable`) and crates/jolt-witness\n\
         -- (`InstructionRafFlag::extract`).",
    );
    s.push_str(
        "import JoltConstraints.witness\n\n\
         set_option autoImplicit false\n\n\
         namespace JoltConstraints.ConstraintGen.Generated\n\n",
    );
    s.push_str("/-- Jolt's `JoltInstructionKind::ALL`, by `name()`. -/\ninductive JoltKind where\n");
    for d in data {
        let _ = writeln!(s, "  | {}", d.name);
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");
    let circuit_order: Vec<String> = CIRCUIT_FLAGS.iter().map(|f| format!("{f:?}")).collect();
    let instruction_order: Vec<String> = INSTRUCTION_FLAGS.iter().map(|f| format!("{f:?}")).collect();
    let _ = writeln!(
        s,
        "/-- Jolt's `CIRCUIT_FLAGS`, in order. -/\ndef circuitFlagOrder : List CircuitFlags :=\n  {}\n",
        lean_list(&circuit_order)
    );
    let _ = writeln!(
        s,
        "/-- Jolt's `InstructionFlags`, in enum order. -/\n\
         def instructionFlagOrder : List InstructionFlags :=\n  {}\n",
        lean_list(&instruction_order)
    );
    s.push_str(
        "/-- The circuit flags of a row of this kind with no sequence stamp\n\
         (`virtual_sequence_remaining = None`, not first, not compressed), in\n\
         `circuitFlagOrder`. -/\ndef kindCircuitFlags : JoltKind → List CircuitFlags\n",
    );
    for d in data {
        let _ = writeln!(s, "  | .{} => {}", d.name, lean_list(&circuit_names(&d.circuit)));
    }
    s.push_str(
        "\n/-- The instruction flags of a row of this kind, in `instructionFlagOrder`. -/\n\
         def kindInstructionFlags : JoltKind → List InstructionFlags\n",
    );
    for d in data {
        let _ = writeln!(s, "  | .{} => {}", d.name, lean_list(&instruction_names(&d.instruction)));
    }
    s.push_str("\n/-- The lookup table of a row of this kind. -/\ndef kindLookupTable : JoltKind → Option LookupTableKind\n");
    for d in data {
        let t = d.table.map_or("none".to_string(), |t| format!("some .{t}"));
        let _ = writeln!(s, "  | .{} => {t}", d.name);
    }
    s.push_str("\n/-- The RAF flag of a row of this kind. -/\ndef kindRafFlag : JoltKind → Bool\n");
    for d in data {
        let _ = writeln!(s, "  | .{} => {}", d.name, d.raf);
    }
    s.push_str(
        "\n/-- For each listed stamp `(virtual_sequence_remaining, is_first_in_sequence,\n\
         is_compressed)`, the circuit flags it adds to every kind except `NoOp`. -/\n\
         def stampCircuitFlags : List ((Option Nat × Bool × Bool) × List CircuitFlags) :=\n  [",
    );
    let items: Vec<String> = stamps
        .iter()
        .map(|(st, set)| {
            let vsr = st.vsr.map_or("none".to_string(), |v| format!("some {v}"));
            format!(
                "(({vsr}, {}, {}), {})",
                st.first,
                st.compressed,
                lean_list(&circuit_names(set))
            )
        })
        .collect();
    s.push_str(&items.join(",\n   "));
    s.push_str("]\n\nend JoltConstraints.ConstraintGen.Generated\n");
    s
}

// ---------------------------------------------------------------------------

fn write(path: &Path, text: &str) -> Result<(), String> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    }
    std::fs::write(path, text).map_err(|e| format!("{}: {e}", path.display()))
}

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    check_flag_lists()?;
    let commit = std::process::Command::new("git")
        .arg("-C")
        .arg(&args.jolt_dir)
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .ok_or("cannot read the Jolt commit")?;
    let mut checks = Checks::default();

    let rows = r1cs_rows(&mut checks)?;
    let r1cs = r1cs_lean(&commit, &rows);
    let (relations, relation_summary) = relations_lean(&commit, &args.jolt_dir, &mut checks)?;
    let (kinds, stamps) = kind_tables(&mut checks)?;
    let kind_text = kinds_lean(&commit, &kinds, &stamps);

    if let Some(root) = &args.lean_root {
        let dir = root.join("JoltConstraints/ConstraintGen/Generated");
        write(&dir.join("R1CS.lean"), &r1cs)?;
        write(&dir.join("Relations.lean"), &relations)?;
        write(&dir.join("KindTables.lean"), &kind_text)?;
    }
    let summary = json!({
        "jolt_commit": commit,
        "r1cs_rows": rows.iter().map(|r| r.name).collect::<Vec<_>>(),
        "relations": relation_summary,
        "kinds": kinds.iter().map(|d| json!({
            "kind": d.name,
            "circuit_flags": circuit_names(&d.circuit),
            "instruction_flags": instruction_names(&d.instruction),
            "lookup_table": d.table,
            "raf": d.raf,
        })).collect::<Vec<_>>(),
        "checks": checks.entries,
    });
    write(
        &args.out.join("constraint_summary.json"),
        &serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())?,
    )?;
    println!(
        "constraint-gen: {} R1CS rows, 4 relations, {} kinds; checks {}",
        rows.len(),
        kinds.len(),
        if checks.failed { "FAILED" } else { "passed" }
    );
    Ok(!checks.failed)
}

fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(e) => {
            eprintln!("constraint-gen: {e}");
            std::process::exit(2);
        }
    }
}
