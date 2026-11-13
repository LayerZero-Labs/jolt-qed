//! lookup-tables: `materialize_entry` vectors of every `LookupTableKind<64>`
//! (track T, phase T4). See ../../LOOKUP-TABLES.md.
//!
//! For every table the binary evaluates Jolt's
//! `LookupTableKind::<64>::materialize_entry` at
//!
//! * edge indices: a common set (0, 1, 2, 2^64 - 1, 2^64, 2^127, 2^128 - 1,
//!   every 2^i for i < 128, and `interleave_bits(x, y)` for x, y in
//!   `EDGE_OPERANDS`) plus indices that exercise the table's case split
//!   (`family`);
//! * a seeded random sample: uniform `u128` indices, and for the six shift and
//!   rotate tables whose Jolt tests override `random_lookup_index` every second
//!   index from a reimplementation of that override.
//!
//! It writes `OUT/lookup_vectors.jsonl` (one line per table and index) and
//! `OUT/lookup_summary.json`. The values are those of this release build,
//! whose arithmetic wraps on overflow as in Jolt's own release profile.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufWriter, Write};
use std::path::PathBuf;

use jolt_lookup_tables::{interleave_bits, LookupTableKind};
use serde_json::json;

type Table = LookupTableKind<64>;

/// Operands for the `interleave_bits(x, y)` edge indices.
const EDGE_OPERANDS: [u64; 10] = [
    0,
    1,
    2,
    (1 << 31) - 1,
    1 << 31,
    (1 << 32) - 1,
    1 << 32,
    (1 << 63) - 1,
    1 << 63,
    u64::MAX,
];

/// Left operands paired with a shift amount or mask in the right operand.
const PATTERN_OPERANDS: [u64; 5] = [
    u64::MAX,
    0x8000_0000_0000_0001,
    0x0123_4567_89AB_CDEF,
    0xFEDC_BA98_7654_3210,
    0x8000_0000_8000_0000,
];

/// Operands of both signs, as a 64-bit and as a 32-bit value.
const SIGNED_OPERANDS: [u64; 12] = [
    0,
    1,
    (1 << 31) - 1,
    1 << 31,
    (1 << 32) - 1,
    0xFFFF_FFFF_8000_0000,
    0x0000_0000_7FFF_FFFF,
    (1 << 63) - 1,
    1 << 63,
    (1 << 63) + 1,
    u64::MAX - 1,
    u64::MAX,
];

/// How a table reads its index, which decides the case-split indices.
#[derive(Clone, Copy, Debug)]
enum Family {
    /// The low bits of the index are a shift amount or byte offset.
    IndexShift,
    /// A function of the whole index, with a sign or range boundary.
    IndexSigned,
    /// A function of the whole index without a case split on a sign.
    Index,
    /// Bitwise on (x, y), possibly with a fixed rotation.
    Bitwise,
    /// A comparison of x and y.
    Compare,
    /// x shifted or rotated by the amount that the bitmask y encodes.
    ShiftBitmask,
    /// The 32-bit form of `ShiftBitmask`: y = 2^32 - 2^s.
    ShiftBitmaskW,
    /// The low byte, halfword or word of x, shifted by 8 * (y & mask).
    ShiftData,
    /// x is the divisor; zero divisors are the case split.
    DivisorX,
    /// y is the divisor; zero divisors are the case split.
    DivisorY,
    /// y negated when x's sign bit is set.
    NegateIf,
    /// Parallel bit extract of x at y's set bits.
    Pext,
}

/// The family of every variant. The match has no wildcard, so a variant added
/// to Jolt's `LookupTableKind` fails to compile here until it is classified.
fn family(t: &Table) -> Family {
    use Family::*;
    match t {
        Table::RangeCheck(_) => Index,
        Table::RangeCheckAligned(_) => Index,
        Table::And(_) => Bitwise,
        Table::Andn(_) => Bitwise,
        Table::Or(_) => Bitwise,
        Table::Xor(_) => Bitwise,
        Table::Equal(_) => Compare,
        Table::SignedGreaterThanEqual(_) => Compare,
        Table::UnsignedGreaterThanEqual(_) => Compare,
        Table::NotEqual(_) => Compare,
        Table::SignedLessThan(_) => Compare,
        Table::UnsignedLessThan(_) => Compare,
        Table::SignMask(_) => IndexSigned,
        Table::UpperWord(_) => Index,
        Table::UnsignedLessThanEqual(_) => Compare,
        Table::ValidUnsignedRemainder(_) => DivisorY,
        Table::ValidDiv0(_) => DivisorX,
        Table::LowerHalfWord(_) => IndexSigned,
        Table::SignExtendWord(_) => IndexSigned,
        Table::Pow2(_) => IndexShift,
        Table::Pow2W(_) => IndexShift,
        Table::ShiftRightBitmask(_) => IndexShift,
        Table::VirtualRev8W(_) => Index,
        Table::VirtualSRL(_) => ShiftBitmask,
        Table::VirtualSRA(_) => ShiftBitmask,
        Table::VirtualROTR(_) => ShiftBitmask,
        Table::VirtualROTRW(_) => ShiftBitmaskW,
        Table::VirtualNegateIf(_) => NegateIf,
        Table::MulUNoOverflow(_) => Index,
        Table::VirtualXORROT32(_) => Bitwise,
        Table::VirtualXORROT24(_) => Bitwise,
        Table::VirtualXORROT16(_) => Bitwise,
        Table::VirtualXORROT63(_) => Bitwise,
        Table::VirtualXORROTW16(_) => Bitwise,
        Table::VirtualXORROTW12(_) => Bitwise,
        Table::VirtualXORROTW8(_) => Bitwise,
        Table::VirtualXORROTW7(_) => Bitwise,
        Table::WindowMaskW(_) => IndexShift,
        Table::PextSigned(_) => Pext,
        Table::VirtualXORROTW22(_) => Bitwise,
        Table::VirtualXORROTW19(_) => Bitwise,
        Table::VirtualXORROTW6(_) => Bitwise,
        Table::ShiftRightBitmaskW(_) => IndexShift,
        Table::VirtualSRLW(_) => ShiftBitmaskW,
        Table::VirtualSRAW(_) => ShiftBitmaskW,
        Table::Pext(_) => Pext,
        Table::WindowMaskB(_) => IndexShift,
        Table::WindowMaskH(_) => IndexShift,
        Table::ShiftDataB(_) => ShiftData,
        Table::ShiftDataH(_) => ShiftData,
        Table::ShiftDataW(_) => ShiftData,
        Table::VirtualXORROTL1(_) => Bitwise,
        Table::AddressOffsetB(_) => IndexShift,
        Table::AddressOffsetH(_) => IndexShift,
        Table::AddressOffsetW(_) => IndexShift,
    }
}

/// The 64-bit right-shift bitmask of Jolt's `VirtualShiftRightBitmask`:
/// ones in bits s through 63.
fn bitmask(s: u32) -> u64 {
    u64::MAX.wrapping_shl(s)
}

/// The 32-bit form: ones in bits s through 31, for s < 32.
fn bitmask_w(s: u32) -> u64 {
    ((1u128 << 32) - (1u128 << s)) as u64
}

/// High bits that a table reading only low bits must ignore.
const HIGH_JUNK: u128 = 0xA5A5_5A5A_F00F_0FF0_C3C3_3C3C_9696_6900;

fn common_edges(out: &mut BTreeSet<u128>) {
    out.extend([0, 1, 2, (1u128 << 64) - 1, 1u128 << 64, 1u128 << 127, u128::MAX]);
    out.extend((0..128).map(|i| 1u128 << i));
    for &x in &EDGE_OPERANDS {
        for &y in &EDGE_OPERANDS {
            out.insert(interleave_bits(x, y));
        }
    }
}

/// Indices that exercise each branch of the table's family.
fn case_split_edges(f: Family, out: &mut BTreeSet<u128>) {
    // Every shift amount 0..63 in the low bits and in the right operand.
    let shift_amounts = |out: &mut BTreeSet<u128>| {
        for s in 0..64u32 {
            out.insert(s as u128);
            out.insert((u128::MAX << 6) | s as u128);
            out.insert((HIGH_JUNK & !63) | s as u128);
            for &x in &PATTERN_OPERANDS {
                out.insert(interleave_bits(x, s as u64));
                out.insert(interleave_bits(x, bitmask(s)));
                out.insert(interleave_bits(x, bitmask_w(s % 32)));
            }
        }
    };
    let both_signs = |out: &mut BTreeSet<u128>| {
        for &x in &SIGNED_OPERANDS {
            for &y in &SIGNED_OPERANDS {
                out.insert(interleave_bits(x, y));
            }
            for hi in [0u128, 1u128 << 127, HIGH_JUNK, (1u128 << 127) | HIGH_JUNK] {
                out.insert((hi & !((1u128 << 64) - 1)) | x as u128);
            }
        }
    };
    match f {
        Family::IndexShift | Family::ShiftData => shift_amounts(out),
        Family::ShiftBitmask | Family::ShiftBitmaskW => {
            shift_amounts(out);
            both_signs(out);
            // Jolt's tests use y = !0 << zeros for zeros in 0..=64, where a
            // shift by 64 wraps to 0.
            for &x in SIGNED_OPERANDS.iter().chain(&PATTERN_OPERANDS) {
                out.insert(interleave_bits(x, 0));
                for s in 0..64u32 {
                    out.insert(interleave_bits(x, bitmask(s)));
                    out.insert(interleave_bits(x, bitmask_w(s % 32)));
                }
            }
        }
        Family::IndexSigned | Family::NegateIf => both_signs(out),
        Family::Index => {
            for &x in &SIGNED_OPERANDS {
                for hi in [0u128, 1, u64::MAX as u128, 1u128 << 63] {
                    out.insert((hi << 64) | x as u128);
                }
            }
        }
        Family::Bitwise => {
            for &x in &PATTERN_OPERANDS {
                for &y in &PATTERN_OPERANDS {
                    out.insert(interleave_bits(x, y));
                }
                for i in 0..64 {
                    out.insert(interleave_bits(x, 1 << i));
                    out.insert(interleave_bits(1 << i, x));
                }
            }
        }
        Family::Compare => {
            both_signs(out);
            for &v in SIGNED_OPERANDS.iter().chain(&EDGE_OPERANDS) {
                out.insert(interleave_bits(v, v));
                out.insert(interleave_bits(v, v.wrapping_add(1)));
                out.insert(interleave_bits(v.wrapping_add(1), v));
            }
        }
        Family::DivisorX | Family::DivisorY => {
            for &v in SIGNED_OPERANDS.iter().chain(&EDGE_OPERANDS).chain(&PATTERN_OPERANDS) {
                // Zero divisor in either operand position, and equal or
                // adjacent operands.
                out.insert(interleave_bits(0, v));
                out.insert(interleave_bits(v, 0));
                out.insert(interleave_bits(v, v));
                out.insert(interleave_bits(v, v.wrapping_add(1)));
                out.insert(interleave_bits(v.wrapping_add(1), v));
            }
        }
        Family::Pext => {
            both_signs(out);
            for &x in SIGNED_OPERANDS.iter().chain(&PATTERN_OPERANDS) {
                for s in 0..64u32 {
                    out.insert(interleave_bits(x, 1 << s));
                    out.insert(interleave_bits(x, bitmask(s)));
                    out.insert(interleave_bits(x, (1u64 << s) - 1));
                }
                for m in [0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 0x8000_0000_0000_0001,
                          0x00FF_0000_FF00_00F0, 0xF0F0_0000_0000_000F] {
                    out.insert(interleave_bits(x, m));
                }
            }
        }
    }
}

/// SplitMix64: a small seeded generator, so the crate needs no `rand`.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn next_u128(&mut self) -> u128 {
        ((self.next_u64() as u128) << 64) | self.next_u64() as u128
    }
}

/// A random index of the table. For the shift and rotate tables whose Jolt
/// tests override `random_lookup_index` (`tables/test_utils.rs`,
/// `gen_bitmask_lookup_index` and `gen_bitmask_w_lookup_index`), every second
/// index follows that override; all other indices are uniform.
fn random_index(f: Family, k: usize, rng: &mut SplitMix64) -> u128 {
    if k % 2 == 1 {
        match f {
            Family::ShiftBitmask => {
                let x = rng.next_u64();
                let zeros = (rng.next_u64() % 65) as u32;
                return interleave_bits(x, (!0u64).wrapping_shl(zeros));
            }
            Family::ShiftBitmaskW => {
                let x = rng.next_u64();
                let shift = (rng.next_u64() % 32) as u32;
                return interleave_bits(x, bitmask_w(shift));
            }
            _ => {}
        }
    }
    rng.next_u128()
}

struct Args {
    out: PathBuf,
    jolt_dir: Option<PathBuf>,
    seed: u64,
    random_per_table: usize,
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        out: PathBuf::new(),
        jolt_dir: std::env::var_os("JOLT_DIR").map(PathBuf::from),
        seed: 0x7434_5eed,
        random_per_table: 2000,
    };
    let mut out = None;
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        let mut val = || it.next().ok_or(format!("{flag} needs a value"));
        match flag.as_str() {
            "--out" => out = Some(PathBuf::from(val()?)),
            "--jolt-dir" => a.jolt_dir = Some(PathBuf::from(val()?)),
            "--seed" => a.seed = val()?.parse().map_err(|e| format!("--seed: {e}"))?,
            "--random-per-table" => {
                a.random_per_table =
                    val()?.parse().map_err(|e| format!("--random-per-table: {e}"))?
            }
            other => return Err(format!("unknown argument {other}")),
        }
    }
    a.out = out.ok_or("--out is required")?;
    Ok(a)
}

fn jolt_commit(dir: &Option<PathBuf>) -> String {
    let Some(dir) = dir else { return "unknown".into() };
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

fn run(a: &Args) -> Result<bool, String> {
    std::fs::create_dir_all(&a.out).map_err(|e| format!("{}: {e}", a.out.display()))?;
    let path = a.out.join("lookup_vectors.jsonl");
    let file = std::fs::File::create(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut w = BufWriter::new(file);

    // A panic in materialize_entry is recorded, not fatal.
    std::panic::set_hook(Box::new(|_| {}));
    let mut panics = Vec::new();
    let mut counts = BTreeMap::new();
    let mut variants = Vec::new();
    let start = std::time::Instant::now();
    for (position, table) in Table::iter().enumerate() {
        let name: &'static str = table.into();
        if table.index() != position {
            return Err(format!("{name}: index() {} at position {position}", table.index()));
        }
        variants.push(name);
        let f = family(&table);
        let mut edges = BTreeSet::new();
        common_edges(&mut edges);
        case_split_edges(f, &mut edges);
        // Seed each table's sample from the seed and the table's position, so
        // one table's sample does not depend on the others.
        let mut rng = SplitMix64(a.seed ^ (position as u64).wrapping_mul(0xD1B5_4A32_D192_ED03));
        let randoms: Vec<u128> =
            (0..a.random_per_table).map(|k| random_index(f, k, &mut rng)).collect();
        let mut n = [0usize; 2];
        for (class, ci, indices) in
            [("edge", 0, edges.into_iter().collect::<Vec<_>>()), ("random", 1, randoms)]
        {
            for index in indices {
                match std::panic::catch_unwind(|| table.materialize_entry(index)) {
                    Ok(value) => {
                        let line = json!({
                            "table": name,
                            "index": index.to_string(),
                            "value": value.to_string(),
                            "class": class,
                        });
                        writeln!(w, "{line}").map_err(|e| e.to_string())?;
                        n[ci] += 1;
                    }
                    Err(_) => panics.push(json!({
                        "table": name, "index": index.to_string(), "class": class
                    })),
                }
            }
        }
        counts.insert(name, json!({ "family": format!("{f:?}"), "edge": n[0], "random": n[1] }));
    }
    w.flush().map_err(|e| e.to_string())?;
    let elapsed = start.elapsed().as_secs_f64();
    let total: usize = counts
        .values()
        .map(|c| c["edge"].as_u64().unwrap_or(0) as usize + c["random"].as_u64().unwrap_or(0) as usize)
        .sum();

    let summary = json!({
        "jolt_commit": jolt_commit(&a.jolt_dir),
        "seed": a.seed,
        "random_per_table": a.random_per_table,
        "variant_count": Table::COUNT,
        "rust_variants": variants,
        "counts": counts,
        "total_vectors": total,
        "panics": panics,
        "seconds": elapsed,
    });
    let spath = a.out.join("lookup_summary.json");
    std::fs::write(&spath, serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())?)
        .map_err(|e| format!("{}: {e}", spath.display()))?;
    println!(
        "lookup-tables: {} variants, {total} vectors, {} panics, {elapsed:.2}s; wrote {}",
        variants.len(),
        panics.len(),
        path.display()
    );
    Ok(panics.is_empty() && variants.len() == Table::COUNT)
}

fn main() {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("lookup-tables: {e}");
            eprintln!(
                "usage: lookup-tables --out DIR [--jolt-dir DIR] [--seed N] [--random-per-table N]"
            );
            std::process::exit(2);
        }
    };
    match run(&args) {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(e) => {
            eprintln!("lookup-tables: {e}");
            std::process::exit(2);
        }
    }
}
