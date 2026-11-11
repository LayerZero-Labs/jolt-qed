//! Lean generation: `JoltBytecode/Inlines/Generated/<Name>.lean` from the
//! operand templates.
//!
//! Rows render as raw `JoltISA.Instr` constructors. Operands are positional,
//! as in `ExpansionsAutomated.lean`: `rd` is the destination, `rs1` the first
//! source and `rs2` the second. Immediates take the constructor's type:
//! `BitVec 64` gets `imm mod 2^64`, `BitVec 128` gets `imm mod 2^128`, and
//! `Nat` requires `imm >= 0`.

use std::fmt::Write as _;
use std::path::Path;

use crate::inlines::{AllocCase, Reg, TemplateRow};

/// `SHA256_INIT_INLINE` -> `Sha256Init`; `SECP256K1_GLVR_ADV` -> `Secp256k1GlvrAdv`.
pub fn upper_camel(name: &str) -> String {
    let base = name.strip_suffix("_INLINE").unwrap_or(name);
    base.split('_')
        .filter(|p| !p.is_empty())
        .map(|p| {
            let lower = p.to_ascii_lowercase();
            let mut c = lower.chars();
            match c.next() {
                Some(f) => f.to_ascii_uppercase().to_string() + c.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

pub fn lower_camel(name: &str) -> String {
    let u = upper_camel(name);
    let mut c = u.chars();
    match c.next() {
        Some(f) => f.to_ascii_lowercase().to_string() + c.as_str(),
        None => u,
    }
}

#[derive(Clone, Copy)]
enum Shape {
    /// dst, src, BitVec 64
    DstSrcImm64,
    /// dst, BitVec 64
    DstImm64,
    /// src, src, BitVec 128
    SrcSrcImm128,
    /// dst, src, src
    DstSrcSrc,
    /// dst, Nat
    DstNat,
    /// dst, src, Nat
    DstSrcNat,
    /// dst, src, src, BitVec 64
    DstSrcSrcImm64,
    /// faultClass, dst, base, BitVec 64, fault
    VirtualLoad,
    /// base, value, BitVec 64, fault
    VirtualStore,
    /// faultClass, dst, base, BitVec 64
    Ld,
    /// base, value, BitVec 64
    Sd,
    /// dst, advice value, BitVec 64
    Advice,
    /// no operands
    Bare,
}

fn shape(kind: &str) -> Option<Shape> {
    use Shape::*;
    Some(match kind {
        "ADDI" | "ADDIW" | "ANDI" | "ORI" | "XORI" | "SLTI" | "SLTIU" | "JALR" | "VirtualMULI"
        | "VirtualMULIW" | "VirtualPow2" | "VirtualPow2W" | "VirtualShiftRightBitmask"
        | "VirtualShiftRightBitmaskW" | "VirtualRev8W" | "VirtualSignExtendWord"
        | "VirtualZeroExtendWord" | "VirtualMovsign" | "VirtualWindowMaskB"
        | "VirtualWindowMaskH" | "VirtualWindowMaskW" => DstSrcImm64,
        "LUI" | "AUIPC" | "JAL" | "VirtualAdviceLoad" => DstImm64,
        "BEQ" | "BNE" | "BLT" | "BGE" | "BLTU" | "BGEU" | "VirtualAssertEQ"
        | "VirtualAssertValidDiv0" | "VirtualAssertValidUnsignedRemainder"
        | "VirtualAssertMulUNoOverflow" | "VirtualAssertLTE" => SrcSrcImm128,
        "ADD" | "ADDW" | "SUB" | "SUBW" | "MUL" | "MULW" | "MULHU" | "ANDN" | "OR" | "XOR"
        | "AND" | "SLT" | "SLTU" | "VirtualSRL" | "VirtualSRA" | "VirtualSRLW" | "VirtualSRAW"
        | "VirtualXORROT32" | "VirtualXORROT24" | "VirtualXORROT16" | "VirtualXORROT63"
        | "VirtualXORROTL1" | "VirtualXORROTW16" | "VirtualXORROTW12" | "VirtualXORROTW8"
        | "VirtualXORROTW7" | "VirtualXORROTW22" | "VirtualXORROTW19" | "VirtualXORROTW6"
        | "VirtualPext" | "VirtualPextSigned" | "VirtualNegateIf" => DstSrcSrc,
        "VirtualPow2I" | "VirtualPow2IW" | "VirtualShiftRightBitmaskI" => DstNat,
        "VirtualSRLI" | "VirtualSRAI" | "VirtualSRLIW" | "VirtualSRAIW" | "VirtualROTRI"
        | "VirtualROTRIW" => DstSrcNat,
        "VirtualShiftDataB" | "VirtualShiftDataH" | "VirtualShiftDataW" => DstSrcSrcImm64,
        "VirtualLoadB" | "VirtualLoadH" | "VirtualLoadW" => VirtualLoad,
        "VirtualStoreB" | "VirtualStoreH" | "VirtualStoreW" => VirtualStore,
        "LD" => Ld,
        "SD" => Sd,
        "VirtualAdvice" => Advice,
        "FENCE" | "VirtualHostIO" => Bare,
        _ => return None,
    })
}

fn reg(r: Option<Reg>, field: &str, row: usize) -> Result<String, String> {
    match r {
        None => Err(format!("row {row}: {field} missing")),
        Some(Reg::Param(i)) => Ok(format!("(.xreg rs{i})")),
        Some(Reg::Lit(n)) if n < 32 => Ok(format!("(.xreg (regidx.Regidx {n}))")),
        Some(Reg::Lit(n)) => Ok(format!("(.vreg (BitVec.ofNat 7 {n}))")),
    }
}

fn bv(imm: i128, width: u32) -> String {
    let modulus: u128 = if width == 128 { 0 } else { 1u128 << width };
    let v = if width == 128 {
        imm as u128
    } else {
        imm.rem_euclid(modulus as i128) as u128
    };
    if v < 4096 {
        format!("({v} : BitVec {width})")
    } else {
        format!("(0x{v:x} : BitVec {width})")
    }
}

fn nat(imm: i128, row: usize) -> Result<String, String> {
    if imm < 0 {
        return Err(format!("row {row}: negative immediate {imm} for a Nat field"));
    }
    Ok(format!("{imm}"))
}

/// Renders one row as an `Instr` term. `advice_index` numbers the
/// `VirtualAdvice` rows.
fn render_row(tr: &TemplateRow, i: usize, advice_index: &mut usize) -> Result<String, String> {
    let kind = tr.row.instruction_kind.name();
    let imm = tr.row.operands.imm;
    let sh = shape(kind).ok_or_else(|| format!("row {i}: no Lean constructor for {kind}"))?;
    let d = || reg(tr.rd, "rd", i);
    let s1 = || reg(tr.rs1, "rs1", i);
    let s2 = || reg(tr.rs2, "rs2", i);
    // Inline loads and stores are ordinary memory accesses, so they take the
    // `.normal` class and the alignment faults of the plain load and store
    // helpers in ExpansionsAutomated.lean.
    let load_fault = "(ExceptionType.E_Load_Addr_Align ())";
    let store_fault = "(ExceptionType.E_SAMO_Addr_Align ())";
    Ok(match sh {
        Shape::DstSrcImm64 => format!(".{kind} {} {} {}", d()?, s1()?, bv(imm, 64)),
        Shape::DstImm64 => format!(".{kind} {} {}", d()?, bv(imm, 64)),
        Shape::SrcSrcImm128 => format!(".{kind} {} {} {}", s1()?, s2()?, bv(imm, 128)),
        Shape::DstSrcSrc => format!(".{kind} {} {} {}", d()?, s1()?, s2()?),
        Shape::DstNat => format!(".{kind} {} {}", d()?, nat(imm, i)?),
        Shape::DstSrcNat => format!(".{kind} {} {} {}", d()?, s1()?, nat(imm, i)?),
        Shape::DstSrcSrcImm64 => {
            format!(".{kind} {} {} {} {}", d()?, s1()?, s2()?, bv(imm, 64))
        }
        Shape::VirtualLoad => format!(
            ".{kind} .normal {} {} {} {load_fault}",
            d()?,
            s1()?,
            bv(imm, 64)
        ),
        Shape::VirtualStore => format!(
            ".{kind} {} {} {} {store_fault}",
            s1()?,
            s2()?,
            bv(imm, 64)
        ),
        Shape::Ld => format!(".LD .normal {} {} {}", d()?, s1()?, bv(imm, 64)),
        Shape::Sd => format!(".SD {} {} {}", s1()?, s2()?, bv(imm, 64)),
        Shape::Advice => {
            let k = *advice_index;
            *advice_index += 1;
            format!(".VirtualAdvice {} (advice {k}) {}", d()?, bv(imm, 64))
        }
        Shape::Bare => format!(".{kind}"),
    })
}

pub struct Rendered {
    pub file_name: String,
    pub module: String,
    pub text: String,
    pub rows: usize,
}

pub struct CaseInput<'a> {
    pub case: AllocCase,
    pub template: &'a [TemplateRow],
}

fn uses_param(t: &[TemplateRow], i: u8) -> bool {
    t.iter()
        .any(|r| [r.rd, r.rs1, r.rs2].contains(&Some(Reg::Param(i))))
}

/// Renders one definition (normal or rd_zero) and returns its Lean text.
fn render_case(
    base: &str,
    reg_name: &str,
    input: &CaseInput,
    chunk: usize,
) -> Result<String, String> {
    let t = input.template;
    let suffix = match input.case {
        AllocCase::Normal => "RowsAuto",
        AllocCase::RdZero => "RowsAutoRdZero",
    };
    let def_name = format!("{base}{suffix}");
    let params: Vec<u8> = match input.case {
        AllocCase::Normal => vec![1, 2, 3],
        AllocCase::RdZero => vec![1, 2],
    };
    let binder = |names: &[u8]| -> String {
        names
            .iter()
            .map(|i| {
                if uses_param(t, *i) {
                    format!("rs{i}")
                } else {
                    format!("_rs{i}")
                }
            })
            .collect::<Vec<_>>()
            .join(" ")
    };
    // In chunked mode the list and program definitions pass every parameter
    // on to the chunks, so they bind plain names.
    let plain = |names: &[u8]| -> String {
        names.iter().map(|i| format!("rs{i}")).collect::<Vec<_>>().join(" ")
    };
    let has_advice = t
        .iter()
        .any(|r| r.row.instruction_kind.name() == "VirtualAdvice");
    let advice_binder = if has_advice {
        " (advice : Nat → BitVec 64)"
    } else {
        ""
    };
    let args = |names: &[u8]| -> String {
        let mut s: String = names
            .iter()
            .map(|i| format!(" rs{i}"))
            .collect::<String>();
        if has_advice {
            s.push_str(" advice");
        }
        s
    };
    let mut advice_index = 0usize;
    let mut rendered = Vec::with_capacity(t.len());
    for (i, tr) in t.iter().enumerate() {
        rendered.push(render_row(tr, i, &mut advice_index).map_err(|e| format!("{reg_name}: {e}"))?);
    }
    let case_label = match input.case {
        AllocCase::Normal => "rd != x0; `rs3` is the source rd".to_string(),
        AllocCase::RdZero => {
            "rd = x0; Jolt rewrites rd to an instruction temporary, which appears as a literal"
                .to_string()
        }
    };
    let mut out = String::new();
    if chunk == 0 {
        writeln!(
            out,
            "/-- The {} final rows of `{reg_name}` ({case_label}). -/\ndef {def_name} ({} : regidx){advice_binder} : JoltISA.Program :=",
            t.len(),
            binder(&params)
        )
        .unwrap();
        for r in &rendered {
            writeln!(out, "  .instr ({r}) <|").unwrap();
        }
        writeln!(out, "  .done RETIRE_SUCCESS\n").unwrap();
    } else {
        let chunks: Vec<&[String]> = rendered.chunks(chunk).collect();
        for (k, c) in chunks.iter().enumerate() {
            let used: Vec<u8> = params.clone();
            // Each chunk takes all parameters so the composition is uniform;
            // parameters a chunk does not mention are named with `_`.
            let lo = k * chunk;
            let sub = &t[lo..lo + c.len()];
            let b: String = used
                .iter()
                .map(|i| {
                    if uses_param(sub, *i) {
                        format!("rs{i}")
                    } else {
                        format!("_rs{i}")
                    }
                })
                .collect::<Vec<_>>()
                .join(" ");
            let sub_advice = sub
                .iter()
                .any(|r| r.row.instruction_kind.name() == "VirtualAdvice");
            let ab = if has_advice {
                if sub_advice {
                    " (advice : Nat → BitVec 64)"
                } else {
                    " (_advice : Nat → BitVec 64)"
                }
            } else {
                ""
            };
            writeln!(
                out,
                "/-- Rows {lo}..{} of `{def_name}`. -/\ndef {def_name}Chunk{k} ({b} : regidx){ab} : List JoltISA.Instr := [",
                lo + c.len() - 1
            )
            .unwrap();
            for (j, r) in c.iter().enumerate() {
                let sep = if j + 1 == c.len() { "" } else { "," };
                writeln!(out, "  {r}{sep}").unwrap();
            }
            writeln!(out, "]\n").unwrap();
        }
        let parts: Vec<String> = (0..chunks.len())
            .map(|k| format!("{def_name}Chunk{k}{}", args(&params)))
            .collect();
        writeln!(
            out,
            "/-- The {} final rows of `{reg_name}` ({case_label}), as a list. -/\ndef {def_name}List ({} : regidx){advice_binder} : List JoltISA.Instr :=\n  {}\n",
            t.len(),
            plain(&params),
            parts.join(" ++\n  ")
        )
        .unwrap();
        writeln!(
            out,
            "/-- The {} final rows of `{reg_name}` ({case_label}). -/\ndef {def_name} ({} : regidx){advice_binder} : JoltISA.Program :=\n  JoltISA.Program.seq ({def_name}List{})\n",
            t.len(),
            plain(&params),
            args(&params)
        )
        .unwrap();
    }
    Ok(out)
}

pub fn render_inline(
    reg_name: &str,
    cases: &[CaseInput],
    jolt_commit: &str,
    regenerate: &str,
    chunk: usize,
) -> Result<Rendered, String> {
    let upper = upper_camel(reg_name);
    let base = lower_camel(reg_name);
    let mut text = String::new();
    let has_advice = cases.iter().any(|c| {
        c.template
            .iter()
            .any(|r| r.row.instruction_kind.name() == "VirtualAdvice")
    });
    let rows = cases.first().map_or(0, |c| c.template.len());
    writeln!(
        text,
        "import JoltBytecode.JoltISA.Instruction\n\n\
/-!\n\
# Final rows of the registered inline `{reg_name}`\n\n\
Generated by `scripts/expansion-parity` (the expansion-parity driver) from\n\
Jolt's production expansion (`expand_instruction_with_provider` with\n\
`TracerInlineExpansionProvider` and `RV64IMAC_JOLT_ALL_INLINES`) at a16z/jolt\n\
commit `{jolt_commit}`.\n\
Do not edit this file by hand; regenerate it with\n\
`{regenerate}`.\n\n\
The driver checked that every operand triple gives the same rows up to the\n\
register parameters, so each definition below covers all register choices.\n\
`rs1` and `rs2` are the source operands and `rs3` is the source `rd`.\n\
Pool and instruction-temporary registers are literals `(.vreg n)` in Jolt's\n\
flat numbering.\n"
    )
    .unwrap();
    if has_advice {
        writeln!(
            text,
            "The inline has `VirtualAdvice` rows. Their values are runtime advice, so\n\
each definition takes `advice : Nat → BitVec 64`, and the k-th `VirtualAdvice`\n\
row (counting from 0 in row order) writes `advice k`.\n"
        )
        .unwrap();
    }
    writeln!(
        text,
        "Load and store rows use the `.normal` fault class with\n\
`E_Load_Addr_Align` for loads and `E_SAMO_Addr_Align` for stores, as the\n\
plain load and store helpers in `ExpansionsAutomated.lean` do.\n-/\n\n\
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions\n\n\
namespace JoltISA.Inlines.Generated\n"
    )
    .unwrap();
    for c in cases {
        text.push_str(&render_case(&base, reg_name, c, chunk)?);
    }
    writeln!(text, "end JoltISA.Inlines.Generated").unwrap();
    Ok(Rendered {
        file_name: format!("{upper}.lean"),
        module: format!("JoltBytecode.Inlines.Generated.{upper}"),
        text,
        rows,
    })
}

pub fn write_all(
    lean_root: &Path,
    files: &[Rendered],
    jolt_commit: &str,
    regenerate: &str,
) -> Result<(), String> {
    let dir = lean_root.join("JoltBytecode/Inlines/Generated");
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    for f in files {
        std::fs::write(dir.join(&f.file_name), &f.text).map_err(|e| e.to_string())?;
    }
    let mut index = String::new();
    for f in files {
        writeln!(index, "import {}", f.module).unwrap();
    }
    writeln!(
        index,
        "\n/-!\n# Generated final rows of all registered inlines\n\n\
Generated by `scripts/expansion-parity` from a16z/jolt commit `{jolt_commit}`.\n\
Do not edit this file by hand; regenerate it with\n`{regenerate}`.\n-/"
    )
    .unwrap();
    std::fs::write(lean_root.join("JoltBytecode/Inlines/Generated.lean"), index)
        .map_err(|e| e.to_string())?;
    Ok(())
}
