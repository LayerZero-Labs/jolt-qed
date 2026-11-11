//! Known-answer driver for Jolt's five hash inlines.
//!
//! For each case this program writes the inline's input memory, runs the
//! INLINE instruction through `INLINE::trace` in Jolt's tracer (which expands
//! it with the registered sequence builder, the same path the prover's bytecode
//! uses), and records the memory before and after as hexadecimal byte strings.
//! It does not compute any hash itself: `lake exe inline-kat` compares the
//! recorded outputs with the Lean specifications.
//!
//! Memory layout, as in Jolt's `InlineTestHarness::single_input`: the region
//! read through rs2 starts at DRAM_BASE and the region read and written
//! through rs1 follows it. Each region is recorded byte by byte, so the JSON
//! holds exactly the bytes the sequence builder loads.
//!
//! Usage: inline-kat [--jolt-commit COMMIT] OUT.json

// The registrations are collected through `inventory`; these lines make sure
// the inline crates are linked even where only their constants are used.
extern crate jolt_inlines_blake2 as _;
extern crate jolt_inlines_keccak256 as _;
extern crate jolt_inlines_sha2 as _;

use serde_json::{json, Value};
use tracer::emulator::mmu::DRAM_BASE;
use tracer::instruction::inline::INLINE;
use tracer::instruction::{Cycle, RISCVTrace};
use tracer::utils::inline_test_harness::{InlineMemoryLayout, InlineTestHarness, INLINE_RS1, INLINE_RS2};
use tracer::utils::virtual_registers::VirtualRegisterAllocator;

/// Number of seeded random cases per inline.
const RANDOM_CASES: usize = 64;

#[derive(Clone, Copy)]
struct Inline {
    /// Short name used in the JSON and by the Lean checker.
    name: &'static str,
    registration: &'static str,
    funct3: u32,
    funct7: u32,
    /// Bytes read and written through rs1.
    rs1_size: usize,
    /// Bytes read through rs2.
    rs2_size: usize,
    layout: &'static str,
}

const OPCODE: u32 = jolt_inlines_sha2::INLINE_OPCODE;

const SHA256: Inline = Inline {
    name: "SHA256",
    registration: jolt_inlines_sha2::SHA256_NAME,
    funct3: jolt_inlines_sha2::SHA256_FUNCT3,
    funct7: jolt_inlines_sha2::SHA256_FUNCT7,
    rs1_size: 32,
    rs2_size: 64,
    layout: "rs1: state, 8 u32 little-endian; rs2: the 64 message bytes in order \
             (word t is the big-endian value of bytes 4t..4t+3)",
};
const SHA256_INIT: Inline = Inline {
    name: "SHA256_INIT",
    registration: jolt_inlines_sha2::SHA256_INIT_NAME,
    funct3: jolt_inlines_sha2::SHA256_INIT_FUNCT3,
    funct7: jolt_inlines_sha2::SHA256_INIT_FUNCT7,
    rs1_size: 32,
    rs2_size: 64,
    layout: "rs1: output state only (not read), 8 u32 little-endian; rs2: as SHA256",
};
const KECCAK256: Inline = Inline {
    name: "KECCAK256",
    registration: jolt_inlines_keccak256::KECCAK256_NAME,
    funct3: jolt_inlines_keccak256::KECCAK256_FUNCT3,
    funct7: jolt_inlines_keccak256::KECCAK256_FUNCT7,
    rs1_size: 200,
    rs2_size: 136,
    layout: "rs1: state, 25 u64 lanes little-endian, lane x+5y at 8(x+5y); rs2: not read",
};
const KECCAK256_ABSORB_PERMUTE: Inline = Inline {
    name: "KECCAK256_ABSORB_PERMUTE",
    registration: jolt_inlines_keccak256::KECCAK256_ABSORB_PERMUTE_NAME,
    funct3: jolt_inlines_keccak256::KECCAK256_ABSORB_PERMUTE_FUNCT3,
    funct7: jolt_inlines_keccak256::KECCAK256_FUNCT7,
    rs1_size: 200,
    rs2_size: 136,
    layout: "rs1: state as KECCAK256; rs2: one 136-byte rate block, XORed into lanes 0..16",
};
const BLAKE2: Inline = Inline {
    name: "BLAKE2",
    registration: jolt_inlines_blake2::BLAKE2_NAME,
    funct3: jolt_inlines_blake2::BLAKE2_FUNCT3,
    funct7: jolt_inlines_blake2::BLAKE2_FUNCT7,
    rs1_size: 64,
    rs2_size: 144,
    layout: "rs1: h, 8 u64 little-endian; rs2: m (16 u64 little-endian), then the counter t \
             (one u64), then is_final (one u64)",
};

const INLINES: [Inline; 5] = [SHA256, SHA256_INIT, KECCAK256, KECCAK256_ABSORB_PERMUTE, BLAKE2];

/// One case: the input regions, and optionally the expected start of rs1
/// after the call, with the source of that value.
struct Case {
    name: String,
    group: &'static str,
    judged: bool,
    rs1: Vec<u8>,
    rs2: Vec<u8>,
    expected: Option<(Vec<u8>, &'static str)>,
    note: Option<&'static str>,
}

impl Case {
    fn new(name: impl Into<String>, group: &'static str, rs1: Vec<u8>, rs2: Vec<u8>) -> Self {
        Case { name: name.into(), group, judged: true, rs1, rs2, expected: None, note: None }
    }
    fn expect(mut self, bytes: Vec<u8>, source: &'static str) -> Self {
        self.expected = Some((bytes, source));
        self
    }
}

/// splitmix64, so the random cases need no external crate and are reproducible.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn le32(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn be32(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_be_bytes()).collect()
}

fn le64(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// A recognisable filler for regions the inline does not read.
fn filler(n: usize) -> Vec<u8> {
    (0..n).map(|i| 0xA5 ^ (i as u8)).collect()
}

// SHA-256 ---------------------------------------------------------------------

const SHA256_IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// The padded blocks of a short message, per FIPS 180-4 section 5.1.1.
fn sha256_pad(msg: &[u8]) -> Vec<Vec<u8>> {
    let mut m = msg.to_vec();
    m.push(0x80);
    while m.len() % 64 != 56 {
        m.push(0);
    }
    m.extend_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
    m.chunks(64).map(|c| c.to_vec()).collect()
}

/// The rs1 bytes after the last block of a message with this digest:
/// the digest is the big-endian encoding of the state words, and the inline
/// stores them little-endian.
fn sha256_state_bytes_of_digest(digest: &str) -> Vec<u8> {
    unhex(digest).chunks(4).flat_map(|c| c.iter().rev().copied().collect::<Vec<_>>()).collect()
}

const SHA_ABC: &str = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
const SHA_EMPTY: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
const SHA_448: &str = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
const SHA_448_MSG: &[u8] = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
/// The intermediate hash value H(1) after the first block of SHA_448_MSG
/// (NIST CSRC example "SHA256.pdf", two-block message).
const SHA_448_H1: [u32; 8] = [
    0x85e655d6, 0x417a1795, 0x3363376a, 0x624cde5c, 0x76e09589, 0xcac5f811, 0xcc4b32c1, 0xf20e533a,
];

/// Jolt's compression vectors (jolt-inlines/sha2/src/test_constants.rs):
/// block words, and the state after compressing them into the IV.
fn sha256_jolt_vectors() -> Vec<(&'static str, [u32; 16], [u32; 8])> {
    let pattern = [
        0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b,
        0x1c1d1e1f, 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637,
        0x38393a3b, 0x3c3d3e3f,
    ];
    vec![
        (
            "jolt: all zeros block with initial IV",
            [0; 16],
            [
                0xda5698be, 0x17b9b469, 0x62335799, 0x779fbeca, 0x8ce5d491, 0xc0d26243, 0xbafef9ea,
                0x1837a9d8,
            ],
        ),
        (
            "jolt: NIST pattern block with initial IV",
            pattern,
            [
                0xfc99a2df, 0x88f42a7a, 0x7bb9d180, 0x33cdc6a2, 0x0256755f, 0x9d5b9a50, 0x44a9cc31,
                0x5abe84a7,
            ],
        ),
        (
            "jolt: all ones block with initial IV",
            [0xffffffff; 16],
            [
                0xef0c748d, 0xf4da50a8, 0xd6c43c01, 0x3edc3ce7, 0x6c9d9fa9, 0xa1458ade, 0x56eb86c0,
                0xa64492d2,
            ],
        ),
    ]
}

/// SHA256 and SHA256_INIT cases. The two-block message needs the state after
/// the first block, which `run` provides from an earlier tracer run.
fn sha256_cases(inline: Inline, run: &mut dyn FnMut(&Case) -> Vec<u8>) -> Vec<Case> {
    let init = inline.name == "SHA256_INIT";
    let state = |iv: &[u32; 8]| if init { filler(32) } else { le32(iv) };
    let mut cases = Vec::new();
    for (label, msg, digest) in [("\"abc\"", &b"abc"[..], SHA_ABC), ("\"\"", &b""[..], SHA_EMPTY)] {
        let block = sha256_pad(msg).remove(0);
        cases.push(
            Case::new(format!("FIPS 180-4: SHA-256({label}), one block"), "kat", state(&SHA256_IV), block)
                .expect(sha256_state_bytes_of_digest(digest), "FIPS 180-4 / NIST CSRC example"),
        );
    }
    let blocks = sha256_pad(SHA_448_MSG);
    assert_eq!(blocks.len(), 2);
    let first = Case::new("FIPS 180-4: 448-bit message, block 1", "kat", state(&SHA256_IV), blocks[0].clone())
        .expect(le32(&SHA_448_H1), "FIPS 180-4 / NIST CSRC example, intermediate H(1)");
    let mid = run(&first);
    cases.push(first);
    // The second block always goes through SHA256, from the tracer's state.
    if !init {
        cases.push(
            Case::new("FIPS 180-4: 448-bit message, block 2 (state from block 1)", "kat", mid, blocks[1].clone())
                .expect(sha256_state_bytes_of_digest(SHA_448), "FIPS 180-4 / NIST CSRC example"),
        );
    }
    for (label, block, result) in sha256_jolt_vectors() {
        cases.push(Case::new(label, "jolt", state(&SHA256_IV), be32(&block)).expect(le32(&result), "Jolt test_constants.rs"));
    }
    let mut rng = Rng(if init { 0x5A256_1 } else { 0x5A256_0 });
    for i in 0..RANDOM_CASES {
        let rs1 = rng.bytes(32);
        let rs2 = rng.bytes(64);
        cases.push(Case::new(format!("random {i}"), "random", rs1, rs2));
    }
    cases
}

/// The SHA256 cases that need a tracer run of SHA256_INIT first: block 2 of
/// the two-block message, chained from SHA256_INIT's output on block 1.
fn sha256_chained_case(init_out: Vec<u8>) -> Case {
    let blocks = sha256_pad(SHA_448_MSG);
    Case::new("FIPS 180-4: 448-bit message, block 2 (state from SHA256_INIT on block 1)", "kat", init_out, blocks[1].clone())
        .expect(sha256_state_bytes_of_digest(SHA_448), "FIPS 180-4 / NIST CSRC example")
}

// Keccak ----------------------------------------------------------------------

/// Keccak-256 padding (pad10*1 with the 0x01 domain byte) of a short message.
fn keccak_pad(msg: &[u8]) -> Vec<u8> {
    assert!(msg.len() < 136);
    let mut block = msg.to_vec();
    block.resize(136, 0);
    block[msg.len()] ^= 0x01;
    block[135] ^= 0x80;
    block
}

const KECCAK_EMPTY: &str = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470";
const KECCAK_ABC: &str = "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45";
/// Keccak-f[1600] of the zero state and of that result (KeccakKAT-3,
/// as recorded in EthLib tests/cryptography/keccak/permutation).
const KECCAK_F_ZERO: &str = "e7dde140798f25f18a47c033f9ccd584eea95aa61e2698d54d49806f304715bd57d05362054e288bd46f8e7f2da497ffc44746a4a0e5fe90762e19d60cda5b8c9c05191bf7a630ad64fc8fd0b75a933035d617233fa95aeb0321710d26e6a6a95f55cfdb167ca58126c84703cd31b8439f56a5111a2ff20161aed9215a63e505f270c98cf2febe641166c47b95703661cb0ed04f555a7cb8c832cf1c8ae83e8c14263aae22790c94e409c5a224f94118c26504e72635f5163ba1307fe944f67549a2ec5c7bfff1ea";
const KECCAK_F_ZERO_TWICE: &str = "3ccb6ef94d955c2d6db55770d02c336a6c6bd770128d3d0994d06955b2d9208a56f1e7e5994f9c4f38fb65daa2b957f90daf7512ae3d7785f710d8c347f2f4fa59879af7e69e1b1f25b498ee0fccfee4a168ceb9b661ce684f978fbac466eadef5b1af6e833dc433d9db1927045406e065128309f0a9f87c434717bfa64954fd404b99d833addd9774e70b5dfcd5ea483cb0b755eec8b8e3e9429e646e22a0917bddbae729310e90e8cca3fac59e2a20b63d1c4e4602345b59104ca4624e9f605cbf8f6ad26cd020";

fn keccak_state_with_block(block: &[u8]) -> Vec<u8> {
    let mut state = block.to_vec();
    state.resize(200, 0);
    state
}

fn keccak256_cases() -> Vec<Case> {
    let src = "KeccakKAT-3 (EthLib permutation tests)";
    let mut cases = vec![
        Case::new("KeccakKAT: zero state", "kat", vec![0; 200], filler(136)).expect(unhex(KECCAK_F_ZERO), src),
        Case::new("KeccakKAT: permutation of the zero-state result", "kat", unhex(KECCAK_F_ZERO), filler(136))
            .expect(unhex(KECCAK_F_ZERO_TWICE), src),
        Case::new("Keccak-256(\"\"): zero state XOR padded block", "kat", keccak_state_with_block(&keccak_pad(b"")), filler(136))
            .expect(unhex(KECCAK_EMPTY), "Keccak-256 reference digest"),
        Case::new("Keccak-256(\"abc\"): zero state XOR padded block", "kat", keccak_state_with_block(&keccak_pad(b"abc")), filler(136))
            .expect(unhex(KECCAK_ABC), "Keccak-256 reference digest"),
        Case::new("jolt: simple pattern (lane i = 3i+5)", "jolt", le64(&core::array::from_fn::<u64, 25, _>(|i| (i * 3 + 5) as u64)), filler(136)),
        Case::new("all-ones state", "kat", vec![0xff; 200], filler(136)),
    ];
    let mut rng = Rng(0x4ECC_0);
    for i in 0..RANDOM_CASES {
        let rs1 = rng.bytes(200);
        let rs2 = rng.bytes(136);
        cases.push(Case::new(format!("random {i}"), "random", rs1, rs2));
    }
    cases
}

fn keccak256_absorb_cases() -> Vec<Case> {
    let mut cases = vec![
        Case::new("jolt: zero state, zero block", "jolt", vec![0; 200], vec![0; 136])
            .expect(unhex(KECCAK_F_ZERO), "KeccakKAT-3 (EthLib permutation tests)"),
        Case::new("jolt: all-ones state, all-ones block", "jolt", vec![0xff; 200], vec![0xff; 136]),
        Case::new("Keccak-256(\"\"): zero state, padded block", "kat", vec![0; 200], keccak_pad(b""))
            .expect(unhex(KECCAK_EMPTY), "Keccak-256 reference digest"),
        Case::new("Keccak-256(\"abc\"): zero state, padded block", "kat", vec![0; 200], keccak_pad(b"abc"))
            .expect(unhex(KECCAK_ABC), "Keccak-256 reference digest"),
    ];
    let mut rng = Rng(0x4ECC_1);
    for i in 0..RANDOM_CASES {
        let rs1 = rng.bytes(200);
        let rs2 = rng.bytes(136);
        cases.push(Case::new(format!("random {i}"), "random", rs1, rs2));
    }
    cases
}

// BLAKE2b ---------------------------------------------------------------------

const BLAKE2B_IV: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];

fn blake2_rs2(m: &[u64; 16], t: u64, is_final: u64) -> Vec<u8> {
    let mut rs2 = le64(m);
    rs2.extend_from_slice(&t.to_le_bytes());
    rs2.extend_from_slice(&is_final.to_le_bytes());
    rs2
}

const BLAKE2B_EMPTY: &str = "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce";
const BLAKE2B_ABC: &str = "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923";
const EIP152_V6: &str = "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d2875298743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735";

fn blake2_cases() -> Vec<Case> {
    // BLAKE2b-512 without a key: h[0] ^= 0x0101_0000 ^ 64 (RFC 7693 section 3.3).
    let mut h0 = BLAKE2B_IV;
    h0[0] ^= 0x0101_0040;
    let mut abc = [0u64; 16];
    abc[0] = 0x0000_0000_0063_6261;
    let mut cases = vec![
        Case::new("jolt: BLAKE2b-512(\"\"), zero block, t = 0, final", "jolt", le64(&h0), blake2_rs2(&[0; 16], 0, 1))
            .expect(unhex(BLAKE2B_EMPTY), "RFC 7693 BLAKE2b-512 of the empty message"),
        Case::new("jolt + RFC 7693 + EIP-152 vector 5: BLAKE2b-512(\"abc\"), t = 3, final", "kat", le64(&h0), blake2_rs2(&abc, 3, 1))
            .expect(unhex(BLAKE2B_ABC), "RFC 7693 appendix A; EIP-152 vector 5"),
        Case::new("EIP-152 vector 6: \"abc\" block, t = 3, not final", "kat", le64(&h0), blake2_rs2(&abc, 3, 0))
            .expect(unhex(EIP152_V6), "EIP-152 vector 6"),
        Case::new("jolt: all-ones h and m, t = 128, not final", "jolt", vec![0xff; 64], blake2_rs2(&[u64::MAX; 16], 128, 0)),
    ];
    let mut rng = Rng(0xB1A2E_0);
    for (k, t) in [(1u64 << 32) + 5, 1u64 << 63, u64::MAX].into_iter().enumerate() {
        for f in [0u64, 1] {
            let h = rng.bytes(64);
            let m: [u64; 16] = core::array::from_fn(|_| rng.next());
            cases.push(Case::new(format!("counter {t:#x} (case {k}), is_final = {f}"), "kat", h, blake2_rs2(&m, t, f)));
        }
    }
    for i in 0..RANDOM_CASES {
        let h = rng.bytes(64);
        let m: [u64; 16] = core::array::from_fn(|_| rng.next());
        let t = rng.next();
        cases.push(Case::new(format!("random {i}, is_final = {}", i % 2), "random", h, blake2_rs2(&m, t, (i % 2) as u64)));
    }
    for f in [2u64, u64::MAX] {
        let h = rng.bytes(64);
        let m: [u64; 16] = core::array::from_fn(|_| rng.next());
        let mut case = Case::new(format!("is_final = {f:#x} (outside {{0, 1}})"), "informational", h, blake2_rs2(&m, 3, f));
        case.judged = false;
        case.note = Some("The specification takes a boolean final flag; the builder XORs (0 - is_final) into v14.");
        cases.push(case);
    }
    cases
}

// Running ---------------------------------------------------------------------

struct Outcome {
    rs1_after: Vec<u8>,
    rs2_after: Vec<u8>,
    rows: usize,
    registers_preserved: bool,
}

fn run(inline: Inline, case: &Case) -> Outcome {
    assert_eq!(case.rs1.len(), inline.rs1_size, "{}: {}", inline.name, case.name);
    assert_eq!(case.rs2.len(), inline.rs2_size, "{}: {}", inline.name, case.name);
    let layout = InlineMemoryLayout::single_input(inline.rs2_size, inline.rs1_size);
    let rs2_addr = layout.input_base;
    let rs1_addr = layout.output_base;
    let mut h = InlineTestHarness::new(layout);
    for (i, &b) in case.rs2.iter().enumerate() {
        h.cpu.mmu.store(rs2_addr + i as u64, b).expect("store rs2");
    }
    for (i, &b) in case.rs1.iter().enumerate() {
        h.cpu.mmu.store(rs1_addr + i as u64, b).expect("store rs1");
    }
    h.setup_registers();
    let before: Vec<i64> = h.cpu.x[1..32].to_vec();
    let instr: INLINE = InlineTestHarness::create_default_instruction(OPCODE, inline.funct3, inline.funct7);
    let mut trace: Vec<Cycle> = Vec::new();
    instr.trace(&mut h.cpu, Some(&mut trace));
    let registers_preserved = h.cpu.x[1..32] == before[..];
    let read = |h: &mut InlineTestHarness, addr: u64, n: usize| -> Vec<u8> {
        (0..n).map(|i| h.cpu.mmu.load(addr + i as u64).expect("load").0).collect()
    };
    Outcome {
        rs1_after: read(&mut h, rs1_addr, inline.rs1_size),
        rs2_after: read(&mut h, rs2_addr, inline.rs2_size),
        rows: trace.len(),
        registers_preserved,
    }
}

fn case_json(inline: Inline, case: &Case, out: &Outcome) -> Value {
    let layout = InlineMemoryLayout::single_input(inline.rs2_size, inline.rs1_size);
    let mut v = json!({
        "inline": inline.name,
        "name": case.name,
        "group": case.group,
        "judged": case.judged,
        "rs1_addr": layout.output_base,
        "rs2_addr": layout.input_base,
        "rs1_before": hex(&case.rs1),
        "rs2_before": hex(&case.rs2),
        "rs1_after": hex(&out.rs1_after),
        "rs2_after": hex(&out.rs2_after),
        "rows": out.rows,
        "registers_preserved": out.registers_preserved,
    });
    if let Some((bytes, source)) = &case.expected {
        v["expected_rs1_after_prefix"] = json!(hex(bytes));
        v["expected_source"] = json!(source);
    }
    if let Some(note) = case.note {
        v["note"] = json!(note);
    }
    v
}

fn push(inline: Inline, cases: Vec<Case>, cases_json: &mut Vec<Value>) {
    for case in &cases {
        let out = run(inline, case);
        cases_json.push(case_json(inline, case, &out));
    }
    eprintln!("inline-kat: {} cases for {}", cases.len(), inline.name);
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut jolt_commit = "unknown".to_string();
    if args.len() >= 2 && args[0] == "--jolt-commit" {
        jolt_commit = args[1].clone();
        args.drain(0..2);
    }
    let [out_path] = args.as_slice() else {
        eprintln!("usage: inline-kat [--jolt-commit COMMIT] OUT.json");
        std::process::exit(2);
    };

    let registered = tracer::list_registered_inlines();
    let mut inlines_json = Vec::new();
    for inline in INLINES {
        let key = (OPCODE, inline.funct3, inline.funct7);
        let name = registered.iter().find(|(k, _)| *k == key).map(|(_, n)| n.clone());
        assert_eq!(name.as_deref(), Some(inline.registration), "{} is not registered under {key:?}", inline.name);
        let instr = InlineTestHarness::create_default_instruction(OPCODE, inline.funct3, inline.funct7);
        let rows = instr.inline_sequence(&VirtualRegisterAllocator::default()).len();
        inlines_json.push(json!({
            "name": inline.name,
            "registration": inline.registration,
            "opcode": OPCODE,
            "funct3": inline.funct3,
            "funct7": inline.funct7,
            "sequence_rows": rows,
            "rs1_register": INLINE_RS1,
            "rs2_register": INLINE_RS2,
            "rs1_size": inline.rs1_size,
            "rs2_size": inline.rs2_size,
            "layout": inline.layout,
        }));
    }

    let mut cases_json = Vec::new();
    let mut sha_cases = sha256_cases(SHA256, &mut |c: &Case| run(SHA256, c).rs1_after);
    let init_cases = sha256_cases(SHA256_INIT, &mut |c: &Case| run(SHA256_INIT, c).rs1_after);
    let init_block1 = init_cases.iter().find(|c| c.name.contains("block 1")).expect("block 1 case");
    sha_cases.push(sha256_chained_case(run(SHA256_INIT, init_block1).rs1_after));
    push(SHA256, sha_cases, &mut cases_json);
    push(SHA256_INIT, init_cases, &mut cases_json);
    push(KECCAK256, keccak256_cases(), &mut cases_json);
    push(KECCAK256_ABSORB_PERMUTE, keccak256_absorb_cases(), &mut cases_json);
    push(BLAKE2, blake2_cases(), &mut cases_json);

    let doc = json!({
        "format": "jolt-qed inline-kat v1",
        "jolt_commit": jolt_commit,
        "dram_base": DRAM_BASE,
        "inlines": inlines_json,
        "cases": cases_json,
    });
    std::fs::write(out_path, serde_json::to_string_pretty(&doc).unwrap() + "\n").expect("write output");
    eprintln!("inline-kat: wrote {} cases to {out_path}", doc["cases"].as_array().unwrap().len());
}
