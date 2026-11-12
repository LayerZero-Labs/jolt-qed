//! decoder-sweep: T2 raw decoder sweep of Jolt's program-image decoder.
//!
//! Runs `jolt_riscv::uncompress_rv64_instruction` and
//! `jolt_program::image::decode::decode_instruction` (the decoder that
//! `decode_elf` uses to build the committed bytecode, not the tracer's decoder)
//! on every 16-bit parcel and on a per-opcode-class sweep of 32-bit words, and
//! writes the results for the Lean comparator. It also sweeps all 2^30 words
//! whose low two bits are 0b11 in Rust alone and checks that, inside each
//! selector class, Jolt's result is determined by the sweep's words. See
//! DECODER-SWEEP.md next to build.sh.

use std::collections::BTreeMap;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use jolt_program::image::decode::decode_instruction;
use jolt_riscv::{uncompress_rv64_instruction, SourceInstruction, RV64IMAC_JOLT};
use rayon::prelude::*;
use serde_json::{json, Value};

/// Address every swept instruction is decoded at. `RV64IMAC_JOLT` contains
/// Rv64C, so `decode_instruction` does not check alignment; the address only
/// reaches the source row.
const ADDRESS: u64 = 0x8000_0000;

/// SYSTEM: the CSR address is bits 31..20, so the rs2 field selects too.
const OP_SYSTEM: u32 = 0x73;

struct Args {
    jolt_dir: PathBuf,
    out: PathBuf,
    seed: u64,
    random_patterns: usize,
    skip_exhaustive: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        jolt_dir: PathBuf::new(),
        out: PathBuf::new(),
        seed: 0x7432_5eed,
        random_patterns: 4,
        skip_exhaustive: false,
    };
    let mut it = std::env::args().skip(1);
    let mut jolt = None;
    let mut out = None;
    while let Some(flag) = it.next() {
        let mut val = || it.next().ok_or(format!("{flag} needs a value"));
        match flag.as_str() {
            "--jolt-dir" => jolt = Some(PathBuf::from(val()?)),
            "--out" => out = Some(PathBuf::from(val()?)),
            "--seed" => a.seed = val()?.parse().map_err(|e| format!("--seed: {e}"))?,
            "--random-patterns" => {
                a.random_patterns =
                    val()?.parse().map_err(|e| format!("--random-patterns: {e}"))?
            }
            "--skip-exhaustive" => a.skip_exhaustive = true,
            other => return Err(format!("unknown argument {other}")),
        }
    }
    a.jolt_dir = jolt
        .or_else(|| std::env::var_os("JOLT_DIR").map(PathBuf::from))
        .ok_or("--jolt-dir or JOLT_DIR is required")?;
    a.out = out.ok_or("--out is required")?;
    Ok(a)
}

/// Jolt's decode result in a comparable form.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Decoded {
    Err(String),
    Ok {
        kind: String,
        rd: Option<u8>,
        rs1: Option<u8>,
        rs2: Option<u8>,
        imm: i128,
    },
}

fn decode(word: u32, compressed: bool) -> Decoded {
    match decode_instruction(word, ADDRESS, compressed, RV64IMAC_JOLT) {
        Err(e) => Decoded::Err(e.to_string()),
        Ok(s) => of_source(&s),
    }
}

fn of_source(s: &SourceInstruction) -> Decoded {
    let ops = s.row().operands;
    Decoded::Ok {
        kind: s.kind().name().to_string(),
        rd: ops.rd,
        rs1: ops.rs1,
        rs2: ops.rs2,
        imm: ops.imm,
    }
}

fn opt(r: Option<u8>) -> String {
    r.map_or("-".to_string(), |v| v.to_string())
}

/// One TSV line: the input, then `E <message>` or `K kind rd rs1 rs2 imm`.
fn render(d: &Decoded) -> String {
    match d {
        Decoded::Err(m) => format!("E\t{}", m.replace(['\t', '\n'], " ")),
        Decoded::Ok { kind, rd, rs1, rs2, imm } => {
            format!("K\t{kind}\t{}\t{}\t{}\t{imm}", opt(*rd), opt(*rs1), opt(*rs2))
        }
    }
}

fn kind_of(d: &Decoded) -> String {
    match d {
        Decoded::Err(m) => format!("error: {m}"),
        Decoded::Ok { kind, .. } => kind.clone(),
    }
}

/// Operand bits: rd (11..7), rs1 (19..15), rs2 (24..20).
const OPERAND_BITS: [u32; 15] = [7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];
const OPERAND_MASK: u32 = 0x01ff_8f80;

/// The selector class of a word: every bit that is not an operand bit, and for
/// SYSTEM also the rs2 field (part of the CSR address and of the exact
/// ECALL/EBREAK/MRET words).
fn class_mask(opcode: u32) -> u32 {
    if opcode == OP_SYSTEM {
        !(0x000f_8f80)
    } else {
        !OPERAND_MASK
    }
}

/// The operand patterns the Lean comparator sees in a class.
/// Non-SYSTEM classes: zero, all ones, every combination of zero and all-ones
/// fields, each operand bit alone, each operand bit clear with the others set,
/// and `random` seeded values (15 free bits).
/// SYSTEM: the free bits are rd and rs1 (10 bits), with the same shapes.
fn patterns(opcode: u32, seed: u64, random: usize) -> Vec<u32> {
    let bits: Vec<u32> = if opcode == OP_SYSTEM {
        OPERAND_BITS[..10].to_vec()
    } else {
        OPERAND_BITS.to_vec()
    };
    let all: u32 = bits.iter().map(|b| 1u32 << b).sum();
    let mut p = vec![0, all];
    // Every combination of zero and all-ones operand fields, so that each
    // pattern of zero fields (the only way the kind depends on operands, as
    // the exhaustive check verifies) appears in the sweep.
    let fields: &[u32] = if opcode == OP_SYSTEM {
        &[0x1f << 7, 0x1f << 15]
    } else {
        &[0x1f << 7, 0x1f << 15, 0x1f << 20]
    };
    for subset in 0..1u32 << fields.len() {
        p.push(fields.iter().enumerate().filter(|(i, _)| subset >> i & 1 == 1).map(|(_, f)| f).sum());
    }
    for b in &bits {
        p.push(1 << b);
        p.push(all & !(1 << b));
    }
    let mut x = seed ^ u64::from(opcode).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    for _ in 0..random {
        // splitmix64
        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^= z >> 31;
        p.push((z as u32) & all);
    }
    p.sort_unstable();
    p.dedup();
    p
}

/// The 32-bit words of the Lean sweep, in a fixed order: every opcode with low
/// bits 0b11, every value of the class bits (funct3 and bits 31..25; for SYSTEM
/// also bits 24..20), and each operand pattern.
fn sweep_words(seed: u64, random: usize) -> Vec<u32> {
    let mut words = Vec::new();
    for hi in 0..32u32 {
        let opcode = hi << 2 | 0b11;
        let pats = patterns(opcode, seed, random);
        let rs2_values: Vec<u32> = if opcode == OP_SYSTEM { (0..32).collect() } else { vec![0] };
        for f7 in 0..128u32 {
            for f3 in 0..8u32 {
                for &r2 in &rs2_values {
                    let base = opcode | f3 << 12 | r2 << 20 | f7 << 25;
                    for &p in &pats {
                        words.push(base | p);
                    }
                }
            }
        }
    }
    words
}

/// Rust-only exhaustive check over the 2^30 words with low bits 0b11.
///
/// For each selector class it decodes all operand values and checks two facts
/// that make the Lean sweep's words determine Jolt's result on the whole class:
/// 1. the kind or error depends on the operand bits only through which of the
///    fields rd, rs1, rs2 (rd, rs1 for SYSTEM) are zero;
/// 2. for words of the class's majority kind, each output field is a GF(2)-affine
///    function of the operand bits (rd, rs1, rs2 as 8-bit values and the
///    immediate as a 128-bit two's-complement value): it is the XOR of its value
///    at the base word and its single-bit differences, where the base word and
///    every single-bit word used have that same kind.
struct Exhaustive {
    words: u64,
    accepted: u64,
    per_opcode: BTreeMap<u32, BTreeMap<String, u64>>,
    kind_violations: Vec<Value>,
    affine_violations: Vec<Value>,
    affine_checked: u64,
    affine_skipped: u64,
}

fn exhaustive() -> Exhaustive {
    let classes: Vec<(u32, u32)> = (0..32u32)
        .flat_map(|hi| {
            let opcode = hi << 2 | 0b11;
            let mask = class_mask(opcode);
            let free = (!mask).count_ones();
            // Enumerate the class bits above the opcode.
            let class_bits: Vec<u32> = (7..32).filter(|b| mask >> b & 1 == 1).collect();
            let n = 1u32 << class_bits.len();
            (0..n).map(move |c| {
                let mut w = opcode;
                for (i, b) in class_bits.iter().enumerate() {
                    if c >> i & 1 == 1 {
                        w |= 1 << b;
                    }
                }
                let _ = free;
                (opcode, w)
            })
        })
        .collect();
    let words = AtomicU64::new(0);
    let accepted = AtomicU64::new(0);
    let results: Vec<_> = classes
        .par_iter()
        .map(|&(opcode, base)| {
            let free_bits: Vec<u32> = (7..32).filter(|b| !class_mask(opcode) >> b & 1 == 1).collect();
            let n = 1u32 << free_bits.len();
            let place = |v: u32| -> u32 {
                let mut w = base;
                for (i, b) in free_bits.iter().enumerate() {
                    if v >> i & 1 == 1 {
                        w |= 1 << b;
                    }
                }
                w
            };
            let zero_key = |w: u32| -> u8 {
                let rd = (w >> 7) & 0x1f == 0;
                let rs1 = (w >> 15) & 0x1f == 0;
                let rs2 = opcode != OP_SYSTEM && (w >> 20) & 0x1f == 0;
                u8::from(rd) | u8::from(rs1) << 1 | u8::from(rs2) << 2
            };
            let decoded: Vec<Decoded> = (0..n).map(|v| decode(place(v), false)).collect();
            let mut counts: BTreeMap<String, u64> = BTreeMap::new();
            let mut by_zero: BTreeMap<u8, String> = BTreeMap::new();
            let mut kind_viol = Vec::new();
            let mut acc = 0u64;
            for (v, d) in decoded.iter().enumerate() {
                let k = kind_of(d);
                if matches!(d, Decoded::Ok { .. }) {
                    acc += 1;
                }
                *counts.entry(k.clone()).or_default() += 1;
                let z = zero_key(place(v as u32));
                match by_zero.get(&z) {
                    None => {
                        by_zero.insert(z, k);
                    }
                    Some(prev) if *prev != k && kind_viol.len() < 4 => {
                        kind_viol.push(json!({
                            "word": format!("{:08x}", place(v as u32)),
                            "kind": k,
                            "same_zero_fields_kind": prev,
                        }));
                    }
                    Some(_) => {}
                }
            }
            // Affine check on the majority accepted kind.
            let majority = counts
                .iter()
                .filter(|(k, _)| !k.starts_with("error"))
                .max_by_key(|(_, c)| **c)
                .map(|(k, _)| k.clone());
            let mut affine_viol = Vec::new();
            let (mut checked, mut skipped) = (0u64, 0u64);
            if let Some(maj) = majority {
                // Base: the first word of that kind; differences from it.
                let base_v = decoded.iter().position(|d| kind_of(d) == maj).unwrap() as u32;
                let fields = |d: &Decoded| -> [i128; 4] {
                    match d {
                        Decoded::Ok { rd, rs1, rs2, imm, .. } => [
                            rd.map_or(-1, i128::from),
                            rs1.map_or(-1, i128::from),
                            rs2.map_or(-1, i128::from),
                            *imm,
                        ],
                        Decoded::Err(_) => [0; 4],
                    }
                };
                let fb = fields(&decoded[base_v as usize]);
                // Single-bit differences, when the flipped word has the same kind.
                let diffs: Vec<Option<[i128; 4]>> = (0..free_bits.len())
                    .map(|i| {
                        let d = &decoded[(base_v ^ 1 << i) as usize];
                        (kind_of(d) == maj).then(|| {
                            let f = fields(d);
                            [f[0] ^ fb[0], f[1] ^ fb[1], f[2] ^ fb[2], f[3] ^ fb[3]]
                        })
                    })
                    .collect();
                for (v, d) in decoded.iter().enumerate() {
                    if kind_of(d) != maj {
                        continue;
                    }
                    let delta = v as u32 ^ base_v;
                    let mut pred = fb;
                    let mut ok = true;
                    for i in 0..free_bits.len() {
                        if delta >> i & 1 == 1 {
                            match diffs[i] {
                                Some(df) => {
                                    for j in 0..4 {
                                        pred[j] ^= df[j];
                                    }
                                }
                                None => ok = false,
                            }
                        }
                    }
                    if !ok {
                        skipped += 1;
                        continue;
                    }
                    checked += 1;
                    if pred != fields(d) && affine_viol.len() < 4 {
                        affine_viol.push(json!({
                            "word": format!("{:08x}", place(v as u32)),
                            "kind": maj,
                            "decoded": render(d),
                        }));
                    }
                }
            }
            words.fetch_add(u64::from(n), Ordering::Relaxed);
            accepted.fetch_add(acc, Ordering::Relaxed);
            (opcode, counts, kind_viol, affine_viol, checked, skipped)
        })
        .collect();
    let mut ex = Exhaustive {
        words: words.into_inner(),
        accepted: accepted.into_inner(),
        per_opcode: BTreeMap::new(),
        kind_violations: Vec::new(),
        affine_violations: Vec::new(),
        affine_checked: 0,
        affine_skipped: 0,
    };
    for (opcode, counts, kv, av, c, s) in results {
        let e = ex.per_opcode.entry(opcode).or_default();
        for (k, n) in counts {
            *e.entry(k).or_default() += n;
        }
        ex.kind_violations.extend(kv);
        ex.affine_violations.extend(av);
        ex.affine_checked += c;
        ex.affine_skipped += s;
    }
    ex
}

fn jolt_commit(dir: &PathBuf) -> String {
    std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

fn write_lines(path: &PathBuf, lines: impl Iterator<Item = String>) -> Result<usize, String> {
    let f = std::fs::File::create(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut w = BufWriter::new(f);
    let mut n = 0;
    for l in lines {
        w.write_all(l.as_bytes()).map_err(|e| e.to_string())?;
        w.write_all(b"\n").map_err(|e| e.to_string())?;
        n += 1;
    }
    w.flush().map_err(|e| e.to_string())?;
    Ok(n)
}

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    std::fs::create_dir_all(&args.out).map_err(|e| e.to_string())?;
    let commit = jolt_commit(&args.jolt_dir);

    // Parcels: every u16, uncompressed by Jolt and decoded as a compressed row.
    let parcels: Vec<String> = (0..=u16::MAX)
        .into_par_iter()
        .map(|h| {
            let w = uncompress_rv64_instruction(h);
            format!("{h:04x}\t{w:08x}\t{}", render(&decode(w, true)))
        })
        .collect();
    let n_parcels = write_lines(&args.out.join("decoder_parcels.tsv"), parcels.into_iter())?;

    // Words: the per-opcode-class sweep.
    let words = sweep_words(args.seed, args.random_patterns);
    let lines: Vec<String> = words
        .par_iter()
        .map(|&w| format!("{w:08x}\t{}", render(&decode(w, false))))
        .collect();
    let n_words = write_lines(&args.out.join("decoder_words.tsv"), lines.into_iter())?;

    let mut pass = true;
    let exhaustive_json = if args.skip_exhaustive {
        Value::Null
    } else {
        let t = std::time::Instant::now();
        let ex = exhaustive();
        pass &= ex.kind_violations.is_empty() && ex.affine_violations.is_empty();
        let per_opcode: BTreeMap<String, &BTreeMap<String, u64>> = ex
            .per_opcode
            .iter()
            .map(|(op, m)| (format!("0x{op:02x}"), m))
            .collect();
        json!({
            "words": ex.words,
            "accepted": ex.accepted,
            "seconds": t.elapsed().as_secs_f64(),
            "kind_depends_only_on_zero_fields": ex.kind_violations.is_empty(),
            "kind_violations": ex.kind_violations,
            "affine": ex.affine_violations.is_empty(),
            "affine_violations": ex.affine_violations,
            "affine_words_checked": ex.affine_checked,
            "affine_words_skipped": ex.affine_skipped,
            "per_opcode": per_opcode,
        })
    };
    let summary = json!({
        "jolt_dir": args.jolt_dir,
        "jolt_commit": commit,
        "profile": "RV64IMAC_JOLT",
        "address": format!("{ADDRESS:#x}"),
        "seed": args.seed,
        "random_patterns": args.random_patterns,
        "parcels": n_parcels,
        "words": n_words,
        "exhaustive": exhaustive_json,
        "pass": pass,
    });
    std::fs::write(
        args.out.join("decoder_summary.json"),
        serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())? + "\n",
    )
    .map_err(|e| e.to_string())?;
    println!("decoder-sweep: Jolt {commit}");
    println!("decoder-sweep: {n_parcels} parcels, {n_words} words written to {}", args.out.display());
    if let Some(ex) = summary["exhaustive"].as_object() {
        println!(
            "decoder-sweep: exhaustive {} words, {} accepted, kind check {}, affine check {} ({} checked, {} skipped), {:.1}s",
            ex["words"], ex["accepted"],
            if ex["kind_depends_only_on_zero_fields"] == true { "pass" } else { "FAIL" },
            if ex["affine"] == true { "pass" } else { "FAIL" },
            ex["affine_words_checked"], ex["affine_words_skipped"], ex["seconds"].as_f64().unwrap_or(0.0)
        );
    }
    Ok(pass)
}

fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(e) => {
            eprintln!("decoder-sweep: {e}");
            std::process::exit(2);
        }
    }
}
