//! Known-answer driver for Jolt's secp256k1 inline advice and sequences.
//!
//! It records, as one JSON document:
//! - `advice`: Jolt's `build_advice` and `build_runtime_advice` for the six
//!   field inlines (which call `mulq_quotient_advice` and
//!   `mulq_division_advice` in `jolt-inlines/sdk/src/host.rs`) and for
//!   `SECP256K1_GLVR_ADV`, on edge-case and random operands, with panics
//!   recorded as panics;
//! - `glv`: `glv::decompose_scalar` and `glv::decompose_scalar_to_u64s` on
//!   edge-case and random scalars, with the untruncated split from a replica
//!   of `glv.rs` (checked here against `decompose_scalar`) and bit-length
//!   statistics;
//! - `runs`: each of the seven inlines run in Jolt's tracer through the
//!   registered expansion (`INLINE::trace`), with the advice words the
//!   `VirtualAdvice` rows received and the output memory.
//!
//! Usage: `secp256k1-kat OUT.json`.

use std::collections::HashMap;
use std::panic::{catch_unwind, AssertUnwindSafe};

use jolt_inlines_sdk::host::{FormatInline, InlineAdviceContext, InlineAdviceError, InlineOp};
use jolt_inlines_secp256k1::glv;
use jolt_inlines_secp256k1::sequence_builder::{
    Secp256k1DivQ, Secp256k1DivR, Secp256k1GlvrAdv, Secp256k1MulQ, Secp256k1MulR,
    Secp256k1SquareQ, Secp256k1SquareR,
};
use jolt_inlines_secp256k1::{
    INLINE_OPCODE, SECP256K1_DIVQ_FUNCT3, SECP256K1_DIVR_FUNCT3, SECP256K1_FUNCT7,
    SECP256K1_GLVR_ADV_FUNCT3, SECP256K1_MULQ_FUNCT3, SECP256K1_MULR_FUNCT3,
    SECP256K1_SQUAREQ_FUNCT3, SECP256K1_SQUARER_FUNCT3,
};
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use serde_json::{json, Value};
use tracer::instruction::{Cycle, RISCVTrace};
use tracer::utils::inline_test_harness::{
    InlineMemoryLayout, InlineTestHarness, INLINE_RS1, INLINE_RS2, INLINE_RS3,
};

// ---------------------------------------------------------------- numbers

fn hex_big(n: &BigUint) -> String {
    format!("0x{}", n.to_str_radix(16))
}

fn hex_int(n: &BigInt) -> String {
    match n.sign() {
        Sign::Minus => format!("-0x{}", n.magnitude().to_str_radix(16)),
        _ => format!("0x{}", n.magnitude().to_str_radix(16)),
    }
}

fn hex_u64(x: u64) -> String {
    format!("0x{x:x}")
}

fn words(ws: &[u64]) -> Value {
    Value::Array(ws.iter().map(|w| Value::String(hex_u64(*w))).collect())
}

fn big(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 16).expect("hex constant")
}

fn to_limbs(n: &BigUint) -> [u64; 4] {
    let m = BigUint::from(1u8) << 256usize;
    let n = n % &m;
    let ds = n.to_u64_digits();
    let mut out = [0u64; 4];
    out[..ds.len()].copy_from_slice(&ds);
    out
}

fn from_limbs(l: &[u64]) -> BigUint {
    let mut n = BigUint::from(0u8);
    for (i, w) in l.iter().enumerate() {
        n += BigUint::from(*w) << (64 * i);
    }
    n
}

fn p() -> BigUint {
    big("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")
}

fn n() -> BigUint {
    big("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141")
}

fn lambda() -> BigUint {
    big("5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72")
}

/// splitmix64, so the corpus is reproducible without extra dependencies.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn limbs(&mut self) -> [u64; 4] {
        [self.next(), self.next(), self.next(), self.next()]
    }
    fn below(&mut self, m: &BigUint) -> BigUint {
        // 320 random bits reduced modulo m: bias below 2^-64.
        let mut x = BigUint::from(0u8);
        for i in 0..5 {
            x += BigUint::from(self.next()) << (64 * i);
        }
        x % m
    }
}

// ---------------------------------------------------------------- panics

fn panic_message(e: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = e.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = e.downcast_ref::<String>() {
        s.clone()
    } else {
        "panic with a non-string payload".to_string()
    }
}

fn catch<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    catch_unwind(AssertUnwindSafe(f)).map_err(panic_message)
}

// ---------------------------------------------------------------- inlines

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    MulQ,
    SquareQ,
    DivQ,
    MulR,
    SquareR,
    DivR,
    Glv,
}

const OPS: [Op; 7] = [
    Op::MulQ,
    Op::SquareQ,
    Op::DivQ,
    Op::MulR,
    Op::SquareR,
    Op::DivR,
    Op::Glv,
];

impl Op {
    fn name(self) -> &'static str {
        match self {
            Op::MulQ => Secp256k1MulQ::NAME,
            Op::SquareQ => Secp256k1SquareQ::NAME,
            Op::DivQ => Secp256k1DivQ::NAME,
            Op::MulR => Secp256k1MulR::NAME,
            Op::SquareR => Secp256k1SquareR::NAME,
            Op::DivR => Secp256k1DivR::NAME,
            Op::Glv => Secp256k1GlvrAdv::NAME,
        }
    }
    fn funct3(self) -> u32 {
        match self {
            Op::MulQ => SECP256K1_MULQ_FUNCT3,
            Op::SquareQ => SECP256K1_SQUAREQ_FUNCT3,
            Op::DivQ => SECP256K1_DIVQ_FUNCT3,
            Op::MulR => SECP256K1_MULR_FUNCT3,
            Op::SquareR => SECP256K1_SQUARER_FUNCT3,
            Op::DivR => SECP256K1_DIVR_FUNCT3,
            Op::Glv => SECP256K1_GLVR_ADV_FUNCT3,
        }
    }
    /// The modulus the inline works modulo (`n` for GLV, which reduces `k`).
    fn modulus(self) -> BigUint {
        match self {
            Op::MulQ | Op::SquareQ | Op::DivQ => p(),
            _ => n(),
        }
    }
    /// Whether the inline reads a second operand through `rs2`.
    fn binary(self) -> bool {
        matches!(self, Op::MulQ | Op::DivQ | Op::MulR | Op::DivR)
    }
    fn out_words(self) -> usize {
        if self == Op::Glv {
            6
        } else {
            4
        }
    }
    /// The typed result of the inline's `InlineOp::build_advice`.
    fn typed_advice(
        self,
        operands: FormatInline,
        ctx: &mut dyn InlineAdviceContext,
    ) -> Result<Value, InlineAdviceError> {
        fn q(a: jolt_inlines_sdk::host::QuotientAdvice) -> Value {
            json!({"quotient": words(&a.quotient)})
        }
        fn d(a: jolt_inlines_sdk::host::ModularDivisionAdvice) -> Value {
            json!({"result": words(&a.result), "quotient": words(&a.quotient)})
        }
        Ok(match self {
            Op::MulQ => q(Secp256k1MulQ::build_advice(operands, ctx)?),
            Op::SquareQ => q(Secp256k1SquareQ::build_advice(operands, ctx)?),
            Op::DivQ => d(Secp256k1DivQ::build_advice(operands, ctx)?),
            Op::MulR => q(Secp256k1MulR::build_advice(operands, ctx)?),
            Op::SquareR => q(Secp256k1SquareR::build_advice(operands, ctx)?),
            Op::DivR => d(Secp256k1DivR::build_advice(operands, ctx)?),
            Op::Glv => {
                let a = Secp256k1GlvrAdv::build_advice(operands, ctx)?;
                json!({
                    "k1_negative": a.k1.is_negative, "k1": words(&a.k1.magnitude),
                    "k2_negative": a.k2.is_negative, "k2": words(&a.k2.magnitude),
                })
            }
        })
    }
    /// The words `InlineOp::build_runtime_advice` hands the `VirtualAdvice` rows.
    fn runtime_advice(
        self,
        operands: FormatInline,
        ctx: &mut dyn InlineAdviceContext,
    ) -> Result<Option<Vec<u64>>, InlineAdviceError> {
        let r = match self {
            Op::MulQ => Secp256k1MulQ::build_runtime_advice(operands, ctx)?,
            Op::SquareQ => Secp256k1SquareQ::build_runtime_advice(operands, ctx)?,
            Op::DivQ => Secp256k1DivQ::build_runtime_advice(operands, ctx)?,
            Op::MulR => Secp256k1MulR::build_runtime_advice(operands, ctx)?,
            Op::SquareR => Secp256k1SquareR::build_runtime_advice(operands, ctx)?,
            Op::DivR => Secp256k1DivR::build_runtime_advice(operands, ctx)?,
            Op::Glv => Secp256k1GlvrAdv::build_runtime_advice(operands, ctx)?,
        };
        Ok(r.map(|v| v.into_iter().collect()))
    }
}

/// A guest view for advice builders: `rs1` points at `a`, `rs2` at `b`.
struct Ctx {
    regs: HashMap<usize, u64>,
    mem: HashMap<u64, u64>,
}

const A_ADDR: u64 = 0x8000_0000;
const B_ADDR: u64 = 0x8000_0020;
const OUT_ADDR: u64 = 0x8000_0040;

impl Ctx {
    fn new(a: &[u64; 4], b: &[u64; 4]) -> Self {
        let mut mem = HashMap::new();
        for i in 0..4 {
            mem.insert(A_ADDR + 8 * i as u64, a[i]);
            mem.insert(B_ADDR + 8 * i as u64, b[i]);
        }
        let regs = HashMap::from([
            (INLINE_RS1 as usize, A_ADDR),
            (INLINE_RS2 as usize, B_ADDR),
            (INLINE_RS3 as usize, OUT_ADDR),
        ]);
        Ctx { regs, mem }
    }
}

impl InlineAdviceContext for Ctx {
    fn register(&self, index: usize) -> u64 {
        *self.regs.get(&index).unwrap_or(&0)
    }
    fn load_doubleword(&mut self, address: u64) -> Option<u64> {
        self.mem.get(&address).copied()
    }
}

fn operands() -> FormatInline {
    FormatInline {
        rs1: INLINE_RS1,
        rs2: INLINE_RS2,
        rs3: INLINE_RS3,
    }
}

/// Jolt's advice for one call, with panics recorded.
fn advice_case(op: Op, case: &str, a: &[u64; 4], b: &[u64; 4]) -> Value {
    let typed = catch(|| op.typed_advice(operands(), &mut Ctx::new(a, b)));
    let runtime = catch(|| op.runtime_advice(operands(), &mut Ctx::new(a, b)));
    let outcome = |r: Result<Result<Value, InlineAdviceError>, String>| match r {
        Ok(Ok(v)) => json!({"ok": v}),
        Ok(Err(e)) => json!({"error": e.to_string()}),
        Err(m) => json!({"panic": m}),
    };
    let runtime = runtime.map(|r| r.map(|w| w.map(|w| words(&w)).unwrap_or(Value::Null)));
    json!({
        "inline": op.name(),
        "case": case,
        "a": words(a),
        "b": if op.binary() { words(b) } else { Value::Null },
        "typed": outcome(typed),
        "words": outcome(runtime),
    })
}

/// Run the inline in Jolt's tracer on a fresh CPU and record what happened.
fn run_case(op: Op, case: &str, a: &[u64; 4], b: &[u64; 4]) -> Value {
    let layout = InlineMemoryLayout::two_inputs(32, 32, 48);
    let mut h = InlineTestHarness::new(layout);
    h.setup_registers();
    h.load_input64(a);
    if op.binary() {
        h.load_input2_64(b);
    }
    let inst =
        InlineTestHarness::create_default_instruction(INLINE_OPCODE, op.funct3(), SECP256K1_FUNCT7);
    let mut cycles: Vec<Cycle> = Vec::new();
    let traced = catch(|| inst.trace(&mut h.cpu, Some(&mut cycles)));
    let mut out = json!({
        "inline": op.name(),
        "case": case,
        "a": words(a),
        "b": if op.binary() { words(b) } else { Value::Null },
    });
    match traced {
        Err(m) => out["outcome"] = json!({"panic": m}),
        Ok(()) => {
            let advice: Vec<u64> = cycles
                .iter()
                .filter_map(|c| match c {
                    Cycle::VirtualAdvice(c) => Some(c.instruction.advice),
                    _ => None,
                })
                .collect();
            let output = h.read_output64(op.out_words());
            let base = tracer::emulator::mmu::DRAM_BASE;
            let mut read = |addr: u64| h.cpu.mmu.load_doubleword(addr).expect("load").0;
            let a_after: Vec<u64> = (0..4).map(|i| read(base + 8 * i)).collect();
            let b_after: Vec<u64> = (0..4).map(|i| read(base + 32 + 8 * i)).collect();
            out["outcome"] = json!({"ok": {
                "rows": cycles.len(),
                "advice": words(&advice),
                "output": words(&output),
                "a_after": words(&a_after),
                "b_after": words(&b_after),
            }});
        }
    }
    out
}

// ---------------------------------------------------------------- GLV

/// Replica of the private helpers of `jolt-inlines/secp256k1/src/glv.rs`
/// (`r`, `a1`, `b1`, `a2`, `rounded_div` and the body of `decompose_scalar`
/// before `to_sign_abs`). It only reports the untruncated split; `main`
/// checks it against `glv::decompose_scalar` on every scalar.
fn glv_raw(k: &BigInt) -> (BigInt, BigInt) {
    let r = BigInt::from(n());
    let a1 = BigInt::from(big("3086d221a7d46bcde86c90e49284eb15"));
    let b1 = BigInt::from(big("e4437ed6010e88286f547fa90abfe4c3"));
    let a2 = BigInt::from(big("114ca50f7a8e2f3f657c1108d9d44cfd8"));
    let rounded_div = |k: &BigInt, coeff: &BigInt| {
        let (mut div, rem) = (k * coeff).div_rem(&r);
        if (&rem + &rem) > r {
            div += BigInt::from(1u8);
        }
        div
    };
    let beta_1 = rounded_div(k, &a1);
    let beta_2 = rounded_div(k, &b1);
    let k1 = k - &beta_1 * &a1 - &beta_2 * &a2;
    let k2 = &beta_1 * &b1 - &beta_2 * &a1;
    (k1, k2)
}

/// `to_sign_abs` of `glv.rs`, replicated for the replica check.
fn sign_abs(x: &BigInt) -> (bool, u128) {
    let m = x.magnitude() % (BigUint::from(1u8) << 128usize);
    let ds = m.to_u64_digits();
    let lo = *ds.first().unwrap_or(&0) as u128;
    let hi = *ds.get(1).unwrap_or(&0) as u128;
    (x.sign() == Sign::Minus, lo | (hi << 64))
}

fn u128_words(x: u128) -> Value {
    words(&[x as u64, (x >> 64) as u64])
}

struct GlvStats {
    count: usize,
    max_k1_bits: u64,
    max_k2_bits: u64,
    max_k1: BigInt,
    max_k2: BigInt,
    over_128: Vec<Value>,
}

fn glv_case(case: &str, k: &BigInt, in_range: bool, stats: &mut GlvStats) -> Value {
    let (k1, k2) = glv_raw(k);
    let dec = catch(|| glv::decompose_scalar(k.clone()));
    let u64s = catch(|| glv::decompose_scalar_to_u64s(k.clone()));
    if let Ok(d) = &dec {
        assert!(
            d[0] == sign_abs(&k1) && d[1] == sign_abs(&k2),
            "glv replica disagrees with glv::decompose_scalar on {case}"
        );
    }
    if in_range {
        stats.count += 1;
        let (b1, b2) = (k1.bits(), k2.bits());
        if b1 > stats.max_k1_bits || (b1 == stats.max_k1_bits && k1.magnitude() > stats.max_k1.magnitude()) {
            stats.max_k1_bits = b1;
            stats.max_k1 = k1.clone();
        }
        if b2 > stats.max_k2_bits || (b2 == stats.max_k2_bits && k2.magnitude() > stats.max_k2.magnitude()) {
            stats.max_k2_bits = b2;
            stats.max_k2 = k2.clone();
        }
        if b1 > 128 || b2 > 128 {
            stats.over_128.push(json!({"case": case, "k": hex_int(k),
                "k1": hex_int(&k1), "k2": hex_int(&k2)}));
        }
    }
    json!({
        "case": case,
        "k": hex_int(k),
        "in_range": in_range,
        "raw_k1": hex_int(&k1),
        "raw_k2": hex_int(&k2),
        "decompose": match dec {
            Ok([(s1, m1), (s2, m2)]) => json!({"ok": {
                "k1_negative": s1, "k1": u128_words(m1),
                "k2_negative": s2, "k2": u128_words(m2)}}),
            Err(m) => json!({"panic": m}),
        },
        "u64s": match u64s {
            Ok(w) => json!({"ok": words(&w)}),
            Err(m) => json!({"panic": m}),
        },
    })
}

/// Scalars at which `rounded_div(k, coeff, n)` changes value: the smallest
/// `k` with `2 * (k * coeff mod n) > n` after the `j`-th multiple, and its
/// neighbours.
fn rounding_thresholds(coeff: &BigUint, js: &[BigUint]) -> Vec<(String, BigUint)> {
    let nn = n();
    let mut out = Vec::new();
    for j in js {
        // smallest k with k*coeff > j*n + n/2, i.e. k = floor((j*n + n/2) / coeff) + 1
        let t = (j * &nn + (&nn >> 1usize)) / coeff + BigUint::from(1u8);
        for (d, label) in [(0i32, "t"), (-1, "t-1"), (1, "t+1"), (-2, "t-2"), (2, "t+2")] {
            let k = if d < 0 {
                &t - BigUint::from((-d) as u32)
            } else {
                &t + BigUint::from(d as u32)
            };
            if k < nn {
                out.push((format!("j={} {label}", j), k));
            }
        }
    }
    out
}

// ---------------------------------------------------------------- corpus

fn field_edges(q: &BigUint) -> Vec<(String, BigUint)> {
    let one = BigUint::from(1u8);
    let two256 = &one << 256usize;
    let mut v = vec![
        ("0".to_string(), BigUint::from(0u8)),
        ("1".to_string(), one.clone()),
        ("2".to_string(), BigUint::from(2u8)),
        ("q-1".to_string(), q - &one),
        ("q-2".to_string(), q - BigUint::from(2u8)),
        ("q".to_string(), q.clone()),
        ("q+1".to_string(), q + &one),
        ("(q+1)/2".to_string(), (q + &one) >> 1usize),
        ("2^256-q".to_string(), &two256 - q),
        ("2^256-1".to_string(), &two256 - &one),
        ("2^255".to_string(), &one << 255usize),
        ("2^128".to_string(), &one << 128usize),
        ("2^64-1".to_string(), (&one << 64usize) - &one),
        ("limb0=ffff".to_string(), from_limbs(&[u64::MAX, 0, 0, 0])),
        ("limb3=ffff".to_string(), from_limbs(&[0, 0, 0, u64::MAX])),
        ("limbs=0x8000..".to_string(), from_limbs(&[1 << 63; 4])),
    ];
    v.retain(|(_, x)| x < &two256);
    v
}

fn main() {
    let out_path = std::env::args().nth(1).expect("usage: secp256k1-kat OUT.json");
    std::panic::set_hook(Box::new(|_| {}));
    assert!(
        tracer::instruction::inline::is_inline_registered(
            INLINE_OPCODE,
            SECP256K1_MULQ_FUNCT3,
            SECP256K1_FUNCT7
        ),
        "the secp256k1 inlines are not registered"
    );
    let mut rng = Rng(0x5ec9_256b_1a7e_0001);
    let mut advice = Vec::new();
    let mut runs = Vec::new();

    // Field inlines.
    for op in OPS.iter().copied().filter(|o| *o != Op::Glv) {
        let q = op.modulus();
        let edges = field_edges(&q);
        let mut pairs: Vec<(String, [u64; 4], [u64; 4])> = Vec::new();
        if op.binary() {
            for (na, a) in &edges {
                for (nb, b) in &edges {
                    pairs.push((format!("edge a={na} b={nb}"), to_limbs(a), to_limbs(b)));
                }
            }
        } else {
            for (na, a) in &edges {
                pairs.push((format!("edge a={na}"), to_limbs(a), [0; 4]));
            }
        }
        // Spec section 5.3: a = 2, b = (q + 1) / 2 (already among the edge pairs
        // for binary inlines; named here for the report).
        if op.binary() {
            let b = (&q + BigUint::from(1u8)) >> 1usize;
            pairs.push(("spec 5.3 a=2 b=(q+1)/2".to_string(), to_limbs(&BigUint::from(2u8)), to_limbs(&b)));
        }
        // Random canonical inputs (the SDK's domain).
        for i in 0..100 {
            let a = rng.below(&q);
            let b = rng.below(&q);
            pairs.push((format!("random canonical {i}"), to_limbs(&a), to_limbs(&b)));
        }
        // Random 256-bit inputs, mostly unreduced.
        for i in 0..30 {
            pairs.push((format!("random 256-bit {i}"), rng.limbs(), rng.limbs()));
        }
        // Random input with a random divisor in {1, q-1} for DIV.
        if matches!(op, Op::DivQ | Op::DivR) {
            for i in 0..10 {
                let a = rng.below(&q);
                pairs.push((format!("random a, b=1 {i}"), to_limbs(&a), to_limbs(&BigUint::from(1u8))));
                pairs.push((format!("random a, b=q-1 {i}"), to_limbs(&a), to_limbs(&(&q - BigUint::from(1u8)))));
            }
        }
        for (case, a, b) in &pairs {
            advice.push(advice_case(op, case, a, b));
            runs.push(run_case(op, case, a, b));
        }
    }

    // GLV.
    let nn = n();
    let one = BigUint::from(1u8);
    let lam = lambda();
    let a1 = big("3086d221a7d46bcde86c90e49284eb15");
    let b1 = big("e4437ed6010e88286f547fa90abfe4c3");
    let a2 = big("114ca50f7a8e2f3f657c1108d9d44cfd8");
    let mut stats = GlvStats {
        count: 0,
        max_k1_bits: 0,
        max_k2_bits: 0,
        max_k1: BigInt::from(0),
        max_k2: BigInt::from(0),
        over_128: Vec::new(),
    };
    let mut glv_edges: Vec<(String, BigUint)> = vec![
        ("0".into(), BigUint::from(0u8)),
        ("1".into(), one.clone()),
        ("2".into(), BigUint::from(2u8)),
        ("n-1".into(), &nn - &one),
        ("n-2".into(), &nn - BigUint::from(2u8)),
        ("(n-1)/2".into(), (&nn - &one) >> 1usize),
        ("(n+1)/2".into(), (&nn + &one) >> 1usize),
        ("lambda".into(), lam.clone()),
        ("n-lambda".into(), &nn - &lam),
        ("lambda^2 mod n".into(), (&lam * &lam) % &nn),
        ("lambda+1".into(), &lam + &one),
        ("lambda-1".into(), &lam - &one),
        ("2^128-1".into(), (&one << 128usize) - &one),
        ("2^128".into(), &one << 128usize),
        ("2^128+1".into(), (&one << 128usize) + &one),
        ("2^127".into(), &one << 127usize),
        ("2^255".into(), &one << 255usize),
        ("a1".into(), a1.clone()),
        ("a1-1".into(), &a1 - &one),
        ("a1+1".into(), &a1 + &one),
        ("b1".into(), b1.clone()),
        ("b1-1".into(), &b1 - &one),
        ("b1+1".into(), &b1 + &one),
        ("a2".into(), a2.clone()),
        ("a2-1".into(), &a2 - &one),
        ("a2+1".into(), &a2 + &one),
        ("n-a1".into(), &nn - &a1),
        ("n-b1".into(), &nn - &b1),
        ("n-a2".into(), &nn - &a2),
        ("(a1+a2)/2".into(), (&a1 + &a2) >> 1usize),
        ("(b1+a1)/2".into(), (&b1 + &a1) >> 1usize),
        ("lambda*a1 mod n".into(), (&lam * &a1) % &nn),
        ("lambda*b1 mod n".into(), (&lam * &b1) % &nn),
        ("lambda*a2 mod n".into(), (&lam * &a2) % &nn),
        ("a1 + lambda*a1 mod n".into(), (&a1 + &lam * &a1) % &nn),
    ];
    // Rounding thresholds of beta_1 = round(k*a1/n) and beta_2 = round(k*b1/n).
    let mut js = vec![
        BigUint::from(0u8),
        BigUint::from(1u8),
        BigUint::from(2u8),
        BigUint::from(1000u32),
    ];
    for c in [&a1, &b1] {
        js.push(c >> 1usize);
        js.push(c - BigUint::from(2u8));
    }
    for (label, coeff) in [("a1", &a1), ("b1", &b1)] {
        for (case, k) in rounding_thresholds(coeff, &js) {
            glv_edges.push((format!("round({label}) {case}"), k));
        }
    }
    // Multiples k = j * ceil(n / coeff) put k*coeff/n near an integer.
    for coeff in [&a1, &b1] {
        let step = (&nn + coeff - &one) / coeff;
        for j in [1u32, 2, 3, 7] {
            let k = &step * BigUint::from(j);
            if k < nn {
                glv_edges.push((format!("ceil(n/coeff)*{j}"), k));
            }
        }
    }
    let mut glv = Vec::new();
    for (case, k) in &glv_edges {
        glv.push(glv_case(&format!("edge {case}"), &BigInt::from(k.clone()), true, &mut stats));
    }
    for i in 0..10_000 {
        let k = rng.below(&nn);
        glv.push(glv_case(&format!("random {i}"), &BigInt::from(k), true, &mut stats));
    }
    // Inputs outside [0, n): the production path never passes them (it
    // reduces k first), but they pin down the truncating division and the
    // 128-bit truncation of `to_sign_abs`.
    let out_of_range: Vec<(String, BigInt)> = vec![
        ("-1".into(), BigInt::from(-1)),
        ("-lambda".into(), -BigInt::from(lam.clone())),
        ("-(n-1)".into(), -BigInt::from(&nn - &one)),
        ("-(2^200+12345)".into(), -BigInt::from((&one << 200usize) + BigUint::from(12345u32))),
        ("n".into(), BigInt::from(nn.clone())),
        ("2n+5".into(), BigInt::from(&nn * BigUint::from(2u8) + BigUint::from(5u8))),
        ("2^256-1".into(), BigInt::from((&one << 256usize) - &one)),
        ("2^300+7".into(), BigInt::from((&one << 300usize) + BigUint::from(7u8))),
    ];
    for (case, k) in &out_of_range {
        glv.push(glv_case(&format!("out-of-range {case}"), k, false, &mut stats));
    }

    // GLVR_ADV advice and runs: edge scalars, unreduced limbs, random scalars.
    let mut glv_inputs: Vec<(String, [u64; 4])> = glv_edges
        .iter()
        .map(|(c, k)| (format!("edge {c}"), to_limbs(k)))
        .collect();
    for (c, k) in [
        ("n", nn.clone()),
        ("n+1", &nn + &one),
        ("n+lambda", &nn + &lam),
        ("2^256-1", (&one << 256usize) - &one),
    ] {
        glv_inputs.push((format!("unreduced {c}"), to_limbs(&k)));
    }
    for i in 0..100 {
        glv_inputs.push((format!("random {i}"), to_limbs(&rng.below(&nn))));
    }
    for (case, k) in &glv_inputs {
        advice.push(advice_case(Op::Glv, case, k, &[0; 4]));
        runs.push(run_case(Op::Glv, case, k, &[0; 4]));
    }

    let doc = json!({
        "jolt_commit": option_env!("JOLT_COMMIT").unwrap_or("unknown"),
        "moduli": {"p": hex_big(&p()), "n": hex_big(&nn), "lambda": hex_big(&lam)},
        "advice": advice,
        "runs": runs,
        "glv": glv,
        "glv_stats": {
            "in_range_count": stats.count,
            "max_k1_bits": stats.max_k1_bits,
            "max_k2_bits": stats.max_k2_bits,
            "max_k1": hex_int(&stats.max_k1),
            "max_k2": hex_int(&stats.max_k2),
            "over_128": stats.over_128,
        },
    });
    std::fs::write(&out_path, serde_json::to_string(&doc).expect("json")).expect("write");
    let count = |v: &Vec<Value>, key: &str| {
        v.iter().filter(|c| c["outcome"].get(key).is_some()).count()
    };
    eprintln!(
        "secp256k1-kat: {} advice cases, {} runs ({} ok, {} panicked), {} GLV scalars; \
         max |k1| {} bits, max |k2| {} bits, {} above 128 bits",
        advice.len(),
        runs.len(),
        count(&runs, "ok"),
        count(&runs, "panic"),
        glv.len(),
        stats.max_k1_bits,
        stats.max_k2_bits,
        stats.over_128.len()
    );
}
