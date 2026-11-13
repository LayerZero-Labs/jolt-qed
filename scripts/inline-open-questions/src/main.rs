//! Probes for the I0(c) and I0(f) questions of jolt-qed's inline plan.
//! Every run drives Jolt's production code: `jolt_program` decoding and
//! expansion, `jolt_host::JoltProgramSource::decode` (what the SDK's
//! preprocessing calls), and `tracer::trace` (the reference tracer).
#![allow(clippy::type_complexity)]

mod elf;

#[cfg(feature = "inlines")]
use jolt_inlines_blake2 as _;
#[cfg(feature = "inlines")]
use jolt_inlines_keccak256 as _;
#[cfg(feature = "inlines")]
use jolt_inlines_secp256k1 as _;
#[cfg(feature = "inlines")]
use jolt_inlines_sha2 as _;

use common::jolt_device::{MemoryConfig, MemoryLayout};
use elf::*;
use jolt_riscv::RamAccess;
use std::panic::{self, AssertUnwindSafe};
use std::sync::Mutex;

static LAST_PANIC: Mutex<Option<String>> = Mutex::new(None);

fn install_hook() {
    panic::set_hook(Box::new(|info| {
        let loc = info
            .location()
            .map(|l| format!("{}:{}", short_path(l.file()), l.line()))
            .unwrap_or_default();
        let msg = if let Some(s) = info.payload().downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = info.payload().downcast_ref::<String>() {
            s.clone()
        } else {
            "<non-string payload>".into()
        };
        // The layout Debug that some messages append is long; keep line one.
        let first = msg.lines().next().unwrap_or("").to_string();
        *LAST_PANIC.lock().unwrap() = Some(format!("panic at {loc}: {first}"));
    }));
}

fn short_path(p: &str) -> String {
    for marker in ["jolt-inline-pin-a6b6/", "/rustc/"] {
        if let Some(i) = p.find(marker) {
            return p[i + marker.len()..].to_string();
        }
    }
    p.to_string()
}

fn catch<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    *LAST_PANIC.lock().unwrap() = None;
    panic::catch_unwind(AssertUnwindSafe(f))
        .map_err(|_| LAST_PANIC.lock().unwrap().clone().unwrap_or_default())
}

fn config() -> MemoryConfig {
    MemoryConfig { program_size: Some(program_size()), ..Default::default() }
}

fn layout() -> MemoryLayout { MemoryLayout::try_new(&config()).expect("layout") }

const INPUTS: [u8; 64] = [0x5a; 64];

struct Run {
    rows: usize,
    advice_rows: usize,
    mem: tracer::emulator::memory::Memory,
    accesses: Vec<RamAccess>,
    device: common::jolt_device::JoltDevice,
}

fn trace(elf: &[u8]) -> Result<Run, String> {
    let cfg = config();
    catch(|| {
        let (_lazy, cycles, mem, device, _tape) =
            tracer::trace(elf, None, &INPUTS, &[], &[], &cfg, None);
        let advice_rows = cycles
            .iter()
            .filter(|c| matches!(c, tracer::instruction::Cycle::VirtualAdvice(_)))
            .count();
        let accesses = cycles.iter().map(|c| c.ram_access()).collect();
        Run { rows: cycles.len(), advice_rows, mem, accesses, device }
    })
}

/// The prover's address check (`MemoryLayout::remap_word_address`, which
/// jolt-witness applies to every RAM access) on the accesses of a run.
/// It omits jolt-witness's second check, that the remapped index is below
/// `ram_k` (`crates/jolt-witness/src/backend/trace/ram.rs:274-282`).
fn remap_report(run: &Run, l: &MemoryLayout) -> String {
    let mut zero = 0;
    let mut bad = Vec::new();
    for a in &run.accesses {
        let addr = match a {
            RamAccess::Read(r) => r.address,
            RamAccess::Write(w) => w.address,
            RamAccess::NoOp => continue,
        };
        match l.remap_word_address(addr) {
            Ok(None) => zero += 1,
            Ok(Some(_)) => {}
            Err(e) => bad.push(format!("{addr:#x}: {e:?}")),
        }
    }
    let mut s = format!("remap: {zero} access(es) at address 0 (no access)");
    if bad.is_empty() {
        s += ", every other access remaps";
    } else {
        s += &format!(", {} rejected, first {}", bad.len(), bad[0]);
    }
    s
}

fn words(run: &Run, addr: u64, n: usize) -> Vec<u64> {
    // `tracer::trace` returns the inner `Memory`, indexed from RAM_START
    // (the MMU's wrapper subtracts DRAM_BASE, mmu.rs:943).
    (0..n).map(|i| run.mem.get_doubleword(addr - RAM_START + 8 * i as u64)).collect()
}

#[derive(Clone, Copy)]
struct Inline {
    name: &'static str,
    f3: u32,
    f7: u32,
    hash: bool, // SDK calls with rd = x0
}

const SHA256: Inline = Inline { name: "SHA256", f3: 0, f7: 0, hash: true };
const SHA256_INIT: Inline = Inline { name: "SHA256_INIT", f3: 1, f7: 0, hash: true };
const KECCAK256: Inline = Inline { name: "KECCAK256", f3: 0, f7: 1, hash: true };
const KECCAK_ABSORB: Inline = Inline { name: "KECCAK256_ABSORB_PERMUTE", f3: 1, f7: 1, hash: true };
const BLAKE2: Inline = Inline { name: "BLAKE2", f3: 0, f7: 2, hash: true };
const MULQ: Inline = Inline { name: "MULQ", f3: 0, f7: 5, hash: false };
const SQUAREQ: Inline = Inline { name: "SQUAREQ", f3: 1, f7: 5, hash: false };
const DIVQ: Inline = Inline { name: "DIVQ", f3: 2, f7: 5, hash: false };
const MULR: Inline = Inline { name: "MULR", f3: 4, f7: 5, hash: false };
const SQUARER: Inline = Inline { name: "SQUARER", f3: 5, f7: 5, hash: false };
const DIVR: Inline = Inline { name: "DIVR", f3: 6, f7: 5, hash: false };
const GLVR_ADV: Inline = Inline { name: "GLVR_ADV", f3: 7, f7: 5, hash: false };

/// Program for one call with rs1 = x10, rs2 = x11 (or x0) and rd = x12 (or x0).
fn call(i: Inline, rs1: u64, rs2: Option<u64>, rs3: Option<u64>, buf: &[u8]) -> Vec<u8> {
    let mut regs = vec![(10, rs1)];
    if let Some(v) = rs2 {
        regs.push((11, v));
    }
    if let Some(v) = rs3 {
        regs.push((12, v));
    }
    let rs2r = if rs2.is_some() { 11 } else { 0 };
    let rd = if i.hash { 0 } else { 12 };
    program(&regs, (i.f3, i.f7, rd, 10, rs2r), buf)
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    /// Four limbs below 2^255, hence below p and n.
    fn field(&mut self) -> [u64; 4] {
        [self.next(), self.next(), self.next(), self.next() >> 1]
    }
}

fn put(buf: &mut [u8], addr: u64, ws: &[u64]) {
    let off = (addr - BUF) as usize;
    for (k, w) in ws.iter().enumerate() {
        buf[off + 8 * k..off + 8 * k + 8].copy_from_slice(&w.to_le_bytes());
    }
}

fn outcome(run: Result<Run, String>) -> String {
    match run {
        Ok(r) => format!("ok ({} rows)", r.rows),
        Err(e) => e,
    }
}

// ---------------------------------------------------------------- Q1

struct ElfSource(Vec<u8>);
impl jolt_host::JoltProgramSource for ElfSource {
    fn get_elf_contents(&self) -> Option<Vec<u8>> { Some(self.0.clone()) }
    fn get_elf_compute_advice_contents(&self) -> Option<Vec<u8>> { None }
}

fn q1() {
    let reg = tracer::list_registered_inlines();
    println!("linked inline registrations: {}", reg.len());
    for ((op, f3, f7), name) in &reg {
        println!("  {op:#04x} f3={f3} f7={f7} {name}");
    }
    // SHA256 with rd = x0, rs1 = x10 (state), rs2 = x11 (block), as sha2/src/sdk.rs emits it.
    let elf = call(SHA256, BUF, Some(BUF + 0x100), None, &[]);
    println!("inline word: {:#010x}", inline_word(0, 0, 0, 10, 11));

    let profile = jolt_riscv::RV64IMAC_JOLT_ALL_INLINES;
    let r = catch(|| jolt_program::image::decode_elf(&elf, profile).map(|i| i.instructions.len()));
    println!("(a) jolt_program::image::decode_elf(RV64IMAC_JOLT_ALL_INLINES): {r:?}");

    let r = catch(|| {
        let mut p = tracer::TracerInlineExpansionProvider::new();
        jolt_program::build_jolt_program_with_inline_provider(&elf, &mut p, profile)
            .map(|p| p.expanded_bytecode.len())
    });
    println!("(b) jolt_program::build_jolt_program_with_inline_provider: {r:?}");

    let r = catch(|| jolt_program::build_jolt_program(&elf).map(|p| p.expanded_bytecode.len()));
    println!("(c) jolt_program::build_jolt_program (RV64IMAC_JOLT, no provider): {r:?}");

    let r = catch(|| {
        let mut src = ElfSource(elf.clone());
        jolt_host::JoltProgramSource::decode(&mut src).0.len()
    });
    println!("(d) jolt_host::JoltProgramSource::decode (called by jolt-sdk program_preprocessing): {r:?}");

    let r = trace(&elf);
    println!("(e) tracer::trace: {}", outcome(r));
}

// ---------------------------------------------------------------- Q3

fn q3() {
    let l = layout();
    println!("layout: lowest={:#x} input={:#x}..{:#x} output={:#x}..{:#x} panic={:#x} termination={:#x} io_end={:#x}",
        l.get_lowest_address(), l.input_start, l.input_end, l.output_start, l.output_end,
        l.panic, l.termination, l.io_end);
    println!("        program={:#x}..{:#x} stack_end(canary start)={:#x} heap_end={:#x}",
        RAM_START, RAM_START + l.program_size, l.stack_end, l.heap_end);
    let state = BUF; // 0x80000500
    let block = BUF + 0x400;
    let below = l.get_lowest_address() - 0x1000;
    let gap = l.io_end + 0x100 - (l.io_end + 0x100) % 8;
    let wrap = 0u64.wrapping_sub(16);
    let cases: Vec<(&str, u64, u64)> = vec![
        ("valid", state, block),
        ("rs1 misaligned by 4", state + 4, block),
        ("rs1 misaligned by 1", state + 1, block),
        ("rs2 misaligned by 4", state, block + 4),
        ("rs1 range wraps past 2^64 (rs1 = 2^64-16)", wrap, block),
        ("rs2 range wraps past 2^64 (rs2 = 2^64-16)", state, wrap),
        ("rs1 = heap_end", l.heap_end, block),
        ("rs1 = heap_end - 16 (straddles heap_end)", l.heap_end - 16, block),
        ("rs2 = heap_end - 32 (straddles heap_end)", state, l.heap_end - 32),
        ("rs1 in stack canary (= stack_end)", l.stack_end, block),
        ("rs1 below lowest address", below, block),
        ("rs2 below lowest address", state, below),
        ("rs1 = 0", 0, block),
        ("rs2 = 0", state, 0),
        ("rs1 in gap above io_end", gap, block),
        ("rs2 in gap above io_end", state, gap),
        ("rs2 = input_start", state, l.input_start),
        ("rs1 = input_start", l.input_start, block),
        ("rs1 = output_start", l.output_start, block),
        ("rs1 = panic - 24 (state covers the panic word)", l.panic - 24, block),
        ("rs1 = 0x1020 (DTB range, below lowest)", 0x1020, block),
        ("rs2 = 0x1020 (DTB range, below lowest)", state, 0x1020),
        ("rs2 = 0x10000000 (UART range, below lowest)", state, 0x1000_0000),
    ];
    for i in [SHA256, KECCAK_ABSORB, MULQ] {
        println!("\n{}: rs1 = {}, rs2 = {}{}", i.name,
            if i.hash { "state (read, then written)" } else { "a (read)" },
            if i.hash { "block (read)" } else { "b (read)" },
            if i.hash { ", rd = x0" } else { ", rs3 = out (written), valid" });
        let mut rng = Rng(7);
        let mut buf = vec![0u8; BUF_SIZE];
        if !i.hash {
            put(&mut buf, state, &rng.field());
            put(&mut buf, block, &rng.field());
        }
        for (name, rs1, rs2) in &cases {
            let rs3 = if i.hash { None } else { Some(BUF + 0x800) };
            let r = trace(&call(i, *rs1, Some(*rs2), rs3, &buf));
            let detail = match &r {
                Ok(run) => {
                    let mut s = format!("ok ({} rows); {}", run.rows, remap_report(run, &l));
                    if run.device.panic { s += "; device panic flag SET"; }
                    if !run.device.outputs.iter().all(|b| *b == 0) { s += "; output bytes written"; }
                    s
                }
                Err(e) => e.clone(),
            };
            println!("  {name:<48} rs1={rs1:#x} rs2={rs2:#x}: {detail}");
        }
        if !i.hash {
            for (name, rs3) in [
                ("rs3 misaligned by 4", BUF + 0x804),
                ("rs3 = heap_end - 16", l.heap_end - 16),
                ("rs3 = 0", 0),
                ("rs3 below lowest", below),
                ("rs3 in stack canary", l.stack_end),
            ] {
                let r = trace(&call(i, state, Some(block), Some(rs3), &buf));
                let detail = match &r {
                    Ok(run) => format!("ok ({} rows); {}", run.rows, remap_report(run, &l)),
                    Err(e) => e.clone(),
                };
                println!("  {name:<48} rs3={rs3:#x}: {detail}");
            }
        }
    }

    // GLVR_ADV: its rows never load rs1; only the advice reads k, through
    // InlineAdviceContext, which records no RAM access.
    println!("\nGLVR_ADV: rs1 = k (read by the advice only), rs3 = out (written)");
    let mut rng = Rng(11);
    let k = rng.field();
    let mut buf = vec![0u8; BUF_SIZE];
    put(&mut buf, state, &k);
    let out = BUF + 0x800;
    for (name, rs1) in [
        ("valid", state),
        ("rs1 misaligned by 4", state + 4),
        ("rs1 = 0", 0),
        ("rs1 below lowest address", below),
        ("rs1 = 0x1020 (DTB range, below lowest)", 0x1020),
        ("rs1 = 0x1018 (second word at 0x1020, DTB)", 0x1018),
        ("rs1 in gap above io_end", gap),
        ("rs1 = input_start", l.input_start),
        ("rs1 = heap_end", l.heap_end),
        ("rs1 range wraps past 2^64 (rs1 = 2^64-16)", wrap),
    ] {
        let r = trace(&call(GLVR_ADV, rs1, None, Some(out), &buf));
        let detail = match &r {
            Ok(run) => format!("ok ({} rows); {}; out = {:x?}", run.rows, remap_report(run, &l),
                words(run, out, 6)),
            Err(e) => e.clone(),
        };
        println!("  {name:<48} rs1={rs1:#x}: {detail}");
    }
}

// ---------------------------------------------------------------- aliasing

/// (rs1 bytes, rs2 bytes or 0, rs3 bytes or 0, output operand 1 or 3, output bytes)
fn footprint(i: Inline) -> (usize, usize, usize, u8, usize) {
    match i.name {
        "SHA256" | "SHA256_INIT" => (32, 64, 0, 1, 32),
        "KECCAK256" => (200, 0, 0, 1, 200),
        "KECCAK256_ABSORB_PERMUTE" => (200, 136, 0, 1, 200),
        "BLAKE2" => (64, 144, 0, 1, 64),
        "MULQ" | "MULR" | "DIVQ" | "DIVR" => (32, 32, 32, 3, 32),
        "SQUAREQ" | "SQUARER" => (32, 0, 32, 3, 32),
        "GLVR_ADV" => (32, 0, 48, 3, 48),
        _ => unreachable!(),
    }
}

/// Run `i` with rs1 at `a1`, rs2 at `a2`, rs3 at `a3` over `buf`; return the output words.
fn run_at(i: Inline, a1: u64, a2: u64, a3: u64, buf: &[u8]) -> Result<(Vec<u64>, usize, usize), String> {
    let (_, n2, n3, out_op, out_len) = footprint(i);
    let elf = call(i, a1, (n2 > 0).then_some(a2), (n3 > 0 || !i.hash).then_some(a3), buf);
    let run = trace(&elf)?;
    let out = if out_op == 1 { a1 } else { a3 };
    Ok((words(&run, out, out_len / 8), run.rows, run.advice_rows))
}

/// Fill operand buffers so the region read through each operand holds valid
/// input: canonical field elements, nonzero divisors, is_final in {0, 1}.
fn fill(i: Inline, buf: &mut [u8], a1: u64, a2: u64, rng: &mut Rng) {
    let (n1, n2, _, _, _) = footprint(i);
    match i.name {
        "BLAKE2" => {
            let h: Vec<u64> = (0..8).map(|_| rng.next()).collect();
            let mut m: Vec<u64> = (0..17).map(|_| rng.next()).collect();
            m.push(1); // is_final
            put(buf, a2, &m);
            put(buf, a1, &h);
        }
        _ if i.hash => {
            let w1: Vec<u64> = (0..n1 / 8).map(|_| rng.next()).collect();
            put(buf, a1, &w1);
            if n2 > 0 {
                let w2: Vec<u64> = (0..n2 / 8).map(|_| rng.next()).collect();
                put(buf, a2, &w2);
            }
        }
        _ => {
            put(buf, a1, &rng.field());
            if n2 > 0 {
                put(buf, a2, &rng.field());
            }
        }
    }
}

fn copy_region(buf: &mut [u8], from: u64, to: u64, n: usize) {
    let (f, t) = ((from - BUF) as usize, (to - BUF) as usize);
    let tmp = buf[f..f + n].to_vec();
    buf[t..t + n].copy_from_slice(&tmp);
}

fn alias() {
    let all = [SHA256, SHA256_INIT, KECCAK256, KECCAK_ABSORB, BLAKE2, MULQ, SQUAREQ, DIVQ, MULR,
        SQUARER, DIVR, GLVR_ADV];
    // Disjoint baseline addresses.
    let (d1, d2, d3) = (BUF, BUF + 0x400, BUF + 0x800);
    for i in all {
        let (n1, n2, n3, _, _) = footprint(i);
        let mut rng = Rng(0x1234_5678 ^ ((i.f3 as u64) << 8) ^ i.f7 as u64);
        // Honest disjoint run first.
        let mut buf = vec![0u8; BUF_SIZE];
        fill(i, &mut buf, d1, d2, &mut rng);
        match run_at(i, d1, d2, d3, &buf) {
            Ok((_, rows, adv)) => println!("{}: disjoint buffers ok, {rows} rows, {adv} VirtualAdvice rows", i.name),
            Err(e) => println!("{}: disjoint buffers FAILED: {e}", i.name),
        }
        // Aliasing shapes: (label, rs1, rs2, rs3) inside one region at R.
        let r = BUF + 0x100;
        let mut shapes: Vec<(&str, u64, u64, u64)> = Vec::new();
        if n2 > 0 {
            shapes.push(("rs2 = rs1", r, r, d3));
            shapes.push(("rs2 = rs1 + 8", r, r + 8, d3));
        }
        if n3 > 0 {
            shapes.push(("rs3 = rs1", r, d2, r));
            shapes.push(("rs3 = rs1 + 8", r, d2, r + 8));
            shapes.push(("rs3 = rs1 - 16", r, d2, r - 16));
            if n2 > 0 {
                shapes.push(("rs3 = rs2", d1, r, r));
                shapes.push(("rs1 = rs2 = rs3", r, r, r));
            }
        }
        for (label, a1, a2, a3) in shapes {
            // Random bytes over the aliased region, then fix the words each
            // read operand needs: canonical limbs, is_final in {0, 1}.
            let mut buf = vec![0u8; BUF_SIZE];
            for k in 0..0x300 / 8 {
                put(&mut buf, r - 0x80 + 8 * k, &[rng.next()]);
            }
            if !i.hash {
                put(&mut buf, a1 + 24, &[rng.next() >> 1]);
                if n2 > 0 { put(&mut buf, a2 + 24, &[rng.next() >> 1]); }
            }
            if i.name == "BLAKE2" { put(&mut buf, a2 + 136, &[1]); }
            // Reference: copy what each operand sees into disjoint buffers.
            let mut refb = buf.clone();
            let e1 = BUF + 0xA00;
            let e2 = BUF + 0xB00;
            let e3 = BUF + 0xD00;
            copy_region(&mut refb, a1, e1, n1);
            if n2 > 0 { copy_region(&mut refb, a2, e2, n2); }
            let aliased = run_at(i, a1, a2, a3, &buf);
            let reference = run_at(i, e1, e2, e3, &refb);
            let verdict = match (&aliased, &reference) {
                (Ok((x, _, _)), Ok((y, _, _))) if x == y => "outputs equal".to_string(),
                (Ok(_), Ok(_)) => "OUTPUTS DIFFER".to_string(),
                (a, b) => format!("aliased: {:?} / reference: {:?}", a.as_ref().err(), b.as_ref().err()),
            };
            println!("  {label:<18} rs1={a1:#x} rs2={a2:#x} rs3={a3:#x}: {verdict}");
        }
    }
}

// ---------------------------------------------------------------- GLVR_ADV

fn glv() {
    let mut rng = Rng(42);
    for trial in 0..3 {
        let k = rng.field();
        let kaddr = BUF + 0x100;
        let mut buf = vec![0u8; BUF_SIZE];
        put(&mut buf, kaddr, &k);
        let disjoint = run_at(GLVR_ADV, kaddr, 0, BUF + 0x800, &buf);
        println!("k = {:x?}", k);
        println!("  disjoint rs3: {:x?}", disjoint.as_ref().map(|x| &x.0));
        for (label, rs3) in [("rs3 = rs1", kaddr), ("rs3 = rs1 + 8", kaddr + 8),
            ("rs3 = rs1 - 16", kaddr - 16), ("rs3 = rs1 + 24", kaddr + 24)] {
            let r = run_at(GLVR_ADV, kaddr, 0, rs3, &buf);
            let same = matches!((&r, &disjoint), (Ok(a), Ok(b)) if a.0 == b.0);
            println!("  {label:<14} out = {:x?}: {}", r.as_ref().map(|x| &x.0),
                if same { "equal to disjoint run" } else { "DIFFERENT" });
        }
        if trial == 0 {
            // A late read would see k overwritten: show that the k region changed.
            let elf = call(GLVR_ADV, kaddr, None, Some(kaddr), &buf);
            if let Ok(run) = trace(&elf) {
                println!("  after rs3 = rs1 run, memory at rs1 = {:x?} (k was {:x?})", words(&run, kaddr, 4), k);
            }
        }
    }
}

// ---------------------------------------------------------------- edge inputs

fn edge() {
    let (a, b, c) = (BUF, BUF + 0x400, BUF + 0x800);
    let max = [u64::MAX; 4];
    let p = [0xFFFF_FFFE_FFFF_FC2F, u64::MAX, u64::MAX, u64::MAX];
    let one = [1, 0, 0, 0];
    let zero = [0u64; 4];
    let p_minus_1 = [0xFFFF_FFFE_FFFF_FC2E, u64::MAX, u64::MAX, u64::MAX];
    let p_plus_1 = [0xFFFF_FFFE_FFFF_FC30, u64::MAX, u64::MAX, u64::MAX];
    let n = [0xBFD2_5E8C_D036_4141, 0xBAAE_DCE6_AF48_A03B, 0xFFFF_FFFF_FFFF_FFFE, u64::MAX];
    let n_minus_1 = [0xBFD2_5E8C_D036_4140, 0xBAAE_DCE6_AF48_A03B, 0xFFFF_FFFF_FFFF_FFFE, u64::MAX];
    let n_plus_1 = [0xBFD2_5E8C_D036_4142, 0xBAAE_DCE6_AF48_A03B, 0xFFFF_FFFF_FFFF_FFFE, u64::MAX];
    // Every assert row of the secp256k1 inlines is VirtualAssertEQ or
    // VirtualAssertLTE with imm = 0, and the tracer panics when one fails
    // (tracer/src/instruction/virtual_assert_eq.rs:20, virtual_assert_lte.rs:19).
    // "ok" below therefore means that Jolt's advice passed every assert row.
    let cases: Vec<(&str, Inline, [u64; 4], [u64; 4])> = vec![
        ("MULQ a = b = 2^256 - 1 (non-canonical)", MULQ, max, max),
        ("MULQ a = p, b = 1 (a = p, non-canonical)", MULQ, p, one),
        ("MULQ a = 2^256 - 1, b = 1", MULQ, max, one),
        ("MULQ a = 2^256 - 1, b = p - 1 (w = 2^256 - 3)", MULQ, max, p_minus_1),
        ("MULQ a = 2^256 - 1, b = p (w = 2^256 - 1, largest)", MULQ, max, p),
        ("MULQ a = b = p", MULQ, p, p),
        ("SQUAREQ a = 2^256 - 1", SQUAREQ, max, zero),
        ("SQUAREQ a = p", SQUAREQ, p, zero),
        ("SQUAREQ a = p + 1", SQUAREQ, p_plus_1, zero),
        ("MULR a = n, b = 1", MULR, n, one),
        ("MULR a = 2^256 - 1, b = n - 1", MULR, max, n_minus_1),
        ("SQUARER a = n + 1", SQUARER, n_plus_1, zero),
        ("DIVQ a = 1, b = 0", DIVQ, one, zero),
        ("DIVQ a = 0, b = 0", DIVQ, zero, zero),
        ("DIVQ a = 1, b = p (b = 0 mod p, non-canonical)", DIVQ, one, p),
        ("DIVQ a = p, b = 1 (dividend non-canonical)", DIVQ, p, one),
        ("DIVQ a = p + 1, b = 1 (dividend non-canonical)", DIVQ, p_plus_1, one),
        ("DIVQ a = 1, b = p + 1 (divisor non-canonical)", DIVQ, one, p_plus_1),
        ("DIVQ a = p - 1, b = 2^256 - 1 (divisor non-canonical)", DIVQ, p_minus_1, max),
        ("DIVR a = 1, b = 0", DIVR, one, zero),
        ("DIVR a = n, b = 1 (dividend non-canonical)", DIVR, n, one),
        ("DIVR a = 1, b = n + 1 (divisor non-canonical)", DIVR, one, n_plus_1),
        ("GLVR_ADV k = 2^256 - 1 (k >= n)", GLVR_ADV, max, zero),
    ];
    for (label, i, x, y) in cases {
        let mut buf = vec![0u8; BUF_SIZE];
        put(&mut buf, a, &x);
        put(&mut buf, b, &y);
        let r = run_at(i, a, b, c, &buf);
        let modulus = match i.name {
            "MULQ" | "SQUAREQ" | "DIVQ" => Some(p),
            "MULR" | "SQUARER" | "DIVR" => Some(n),
            _ => None,
        };
        println!("{label:<56}: {}", match r {
            Ok((out, rows, _)) => {
                let canon = match modulus {
                    Some(m) if out.len() == 4 => {
                        let o = [out[0], out[1], out[2], out[3]];
                        if lt4(&o, &m) { ", out < modulus" } else { ", out >= modulus" }
                    }
                    _ => "",
                };
                format!("ok ({rows} rows), out = {out:x?}{canon}")
            }
            Err(e) => e,
        });
    }
    // BLAKE2 with is_final = 0, 1, 2, 2^64 - 1.
    let mut rng = Rng(99);
    let h: Vec<u64> = (0..8).map(|_| rng.next()).collect();
    let m: Vec<u64> = (0..17).map(|_| rng.next()).collect();
    for f in [0u64, 1, 2, u64::MAX] {
        let mut buf = vec![0u8; BUF_SIZE];
        put(&mut buf, a, &h);
        let mut mm = m.clone();
        mm.push(f);
        put(&mut buf, b, &mm);
        let r = run_at(BLAKE2, a, b, c, &buf);
        println!("BLAKE2 is_final = {f:#x}: {}", match r {
            Ok((out, rows, _)) => format!("ok ({rows} rows), h[0] = {:#018x}", out[0]),
            Err(e) => e,
        });
    }
}

/// `x < m` for little-endian four-limb integers.
fn lt4(x: &[u64; 4], m: &[u64; 4]) -> bool {
    for k in (0..4).rev() {
        if x[k] != m[k] {
            return x[k] < m[k];
        }
    }
    false
}

fn main() {
    install_hook();
    let cmd = std::env::args().nth(1).unwrap_or_default();
    match cmd.as_str() {
        "q1" => q1(),
        "q3" => q3(),
        "alias" => alias(),
        "glv" => glv(),
        "edge" => edge(),
        _ => eprintln!("usage: inline-probe q1|q3|alias|glv|edge"),
    }
}
