import JoltTests.InlineKat.Layout

/-!
# The known-answer cases a corpus must contain

`lake exe inline-kat` checks every case of a corpus against the specifications, but a corpus
could leave out the cases whose answers are published. This module lists those cases with their
inputs and answers, written down here from the published sources rather than taken from the
corpus or computed by the specifications:

- SHA-256: the FIPS 180-4 examples of the NIST CSRC (`"abc"`, `""`, and the 448-bit message,
  whose intermediate value `H(1)` the example also lists), and the three compression vectors of
  Jolt's `jolt-inlines/sha2/src/test_constants.rs`;
- Keccak: the Keccak-f[1600] answers of the Keccak team's `KeccakKAT-3` for the zero state and
  for its image, and the Keccak-256 digests of `""` and `"abc"`;
- BLAKE2b: BLAKE2b-512 of `""` and `"abc"` (RFC 7693 appendix A, EIP-152 vector 5) and EIP-152
  vector 6.

`inline-kat` requires each entry to appear in the corpus under its inline and name, with the
same input, with the same published answer, and with a tracer result that starts with that
answer.
-/

namespace JoltTests.InlineKat

/-! ## Byte strings -/

/-- Bytes from a list of byte values. -/
def bytesOf (bs : List Nat) : ByteArray := ⟨(bs.map UInt8.ofNat).toArray⟩

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- Words of 32 bits stored little-endian, as at `rs1` of the SHA-256 inlines. -/
def le32 (ws : List Nat) : ByteArray := ⟨(ws.flatMap (leBytes · 4)).toArray⟩

/-- Words of 32 bits stored big-endian, as in a SHA-256 message block. -/
def be32 (ws : List Nat) : ByteArray := ⟨(ws.flatMap fun w => (leBytes w 4).reverse).toArray⟩

/-- Words of 64 bits stored little-endian. -/
def le64 (ws : List Nat) : ByteArray := ⟨(ws.flatMap (leBytes · 8)).toArray⟩

/-- A SHA-256 digest as the inline stores the final state: the digest is the big-endian encoding
of the eight state words, and `rs1` holds each word little-endian. -/
def digestState (hex : String) : ByteArray :=
  ⟨((List.range 8).flatMap fun j => ((ofHex hex).toList.drop (4 * j) |>.take 4).reverse).toArray⟩

/-- The padded blocks of a short message (FIPS 180-4 section 5.1.1): the message, `0x80`, zeros
up to 56 bytes modulo 64, and the bit length as a big-endian `u64`. -/
def shaPad (msg : String) : List ByteArray :=
  let m := msg.toUTF8.toList.map UInt8.toNat
  let zerosNeeded := (119 - m.length) % 64
  let bytes := m ++ [0x80] ++ List.replicate zerosNeeded 0 ++ (leBytes (8 * m.length) 8).reverse.map
    UInt8.toNat
  (List.range (bytes.length / 64)).map fun k => bytesOf ((bytes.drop (64 * k)).take 64)

/-- A Keccak-256 block of a message shorter than 136 bytes: the message, then `0x01` and `0x80`
(pad10*1 with Keccak's domain byte), 136 bytes in all. -/
def keccakPad (msg : String) : ByteArray :=
  let m := msg.toUTF8.toList.map UInt8.toNat
  let block := (m ++ List.replicate (136 - m.length) 0).set m.length 0x01
  bytesOf (block.set 135 (block[135]! ^^^ 0x80))

/-! ## Published answers -/

/-- The SHA-256 initial hash value `H(0)` (FIPS 180-4 section 5.3.3). -/
def sha256IV : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- `H(1)` of the NIST CSRC two-block SHA-256 example (the 448-bit message). -/
def sha256TwoBlockH1 : List Nat :=
  [0x85e655d6, 0x417a1795, 0x3363376a, 0x624cde5c, 0x76e09589, 0xcac5f811, 0xcc4b32c1, 0xf20e533a]

/-- The 448-bit message of the NIST CSRC two-block SHA-256 example. -/
def sha256TwoBlockMessage : String := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

/-- Keccak-f[1600] of the zero state, from the Keccak team's `KeccakKAT-3`
(EthLib `tests/cryptography/keccak/permutation/permutation_zero`). -/
def keccakFZero : String :=
  "e7dde140798f25f18a47c033f9ccd584eea95aa61e2698d54d49806f304715bd57d05362054e288bd46f8e7f2da4" ++
  "97ffc44746a4a0e5fe90762e19d60cda5b8c9c05191bf7a630ad64fc8fd0b75a933035d617233fa95aeb0321710d" ++
  "26e6a6a95f55cfdb167ca58126c84703cd31b8439f56a5111a2ff20161aed9215a63e505f270c98cf2febe641166" ++
  "c47b95703661cb0ed04f555a7cb8c832cf1c8ae83e8c14263aae22790c94e409c5a224f94118c26504e72635f516" ++
  "3ba1307fe944f67549a2ec5c7bfff1ea"

/-- Keccak-f[1600] applied twice to the zero state (`permutation_zero_twice`). -/
def keccakFZeroTwice : String :=
  "3ccb6ef94d955c2d6db55770d02c336a6c6bd770128d3d0994d06955b2d9208a56f1e7e5994f9c4f38fb65daa2b9" ++
  "57f90daf7512ae3d7785f710d8c347f2f4fa59879af7e69e1b1f25b498ee0fccfee4a168ceb9b661ce684f978fba" ++
  "c466eadef5b1af6e833dc433d9db1927045406e065128309f0a9f87c434717bfa64954fd404b99d833addd9774e7" ++
  "0b5dfcd5ea483cb0b755eec8b8e3e9429e646e22a0917bddbae729310e90e8cca3fac59e2a20b63d1c4e4602345b" ++
  "59104ca4624e9f605cbf8f6ad26cd020"

/-- The BLAKE2b-512 state `h` for an unkeyed 64-byte digest: the IV (RFC 7693 section 2.6) with
`0x01010040` XORed into word 0. -/
def blake2bH0 : List Nat :=
  [0x6a09e667f3bcc908 ^^^ 0x01010040, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The bytes at `rs2` of the `BLAKE2` inline: the block, the counter and the final flag. -/
def blake2Input (block : ByteArray) (t flag : Nat) : ByteArray :=
  block ++ le64 [t, flag]

/-- The 128-byte block holding `"abc"`. -/
def blake2AbcBlock : ByteArray := "abc".toUTF8 ++ zeros 125

/-! ## The manifest -/

/-- A case the corpus must contain. `rs1` and `rs2` are the inputs the inline reads; `none`
means it does not read that region, and then the corpus may hold anything there. -/
structure KnownCase where
  inline : String
  name : String
  rs1 : Option ByteArray
  rs2 : Option ByteArray
  answer : ByteArray
  source : String

/-- The SHA-256 cases, for `SHA256` (which reads the IV at `rs1`) or `SHA256_INIT` (which does
not read `rs1`). -/
def sha256Known (inline : String) : List KnownCase :=
  let rs1 := if inline == "SHA256" then some (le32 sha256IV) else none
  let fips := "FIPS 180-4 / NIST CSRC example"
  let jolt := "Jolt test_constants.rs"
  let pattern := (List.range 16).map fun i =>
    (4 * i) * 0x1000000 + (4 * i + 1) * 0x10000 + (4 * i + 2) * 0x100 + (4 * i + 3)
  [ ⟨inline, "FIPS 180-4: SHA-256(\"abc\"), one block", rs1, some (shaPad "abc")[0]!,
      digestState "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad", fips⟩,
    ⟨inline, "FIPS 180-4: SHA-256(\"\"), one block", rs1, some (shaPad "")[0]!,
      digestState "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", fips⟩,
    ⟨inline, "FIPS 180-4: 448-bit message, block 1", rs1,
      some (shaPad sha256TwoBlockMessage)[0]!, le32 sha256TwoBlockH1,
      "FIPS 180-4 / NIST CSRC example, intermediate H(1)"⟩,
    ⟨inline, "jolt: all zeros block with initial IV", rs1, some (zeros 64),
      le32 [0xda5698be, 0x17b9b469, 0x62335799, 0x779fbeca, 0x8ce5d491, 0xc0d26243, 0xbafef9ea,
        0x1837a9d8], jolt⟩,
    ⟨inline, "jolt: NIST pattern block with initial IV", rs1, some (be32 pattern),
      le32 [0xfc99a2df, 0x88f42a7a, 0x7bb9d180, 0x33cdc6a2, 0x0256755f, 0x9d5b9a50, 0x44a9cc31,
        0x5abe84a7], jolt⟩,
    ⟨inline, "jolt: all ones block with initial IV", rs1, some (bytesOf (List.replicate 64 0xff)),
      le32 [0xef0c748d, 0xf4da50a8, 0xd6c43c01, 0x3edc3ce7, 0x6c9d9fa9, 0xa1458ade, 0x56eb86c0,
        0xa64492d2], jolt⟩ ] ++
  if inline == "SHA256" then
    let digest := digestState "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    let block2 := some (shaPad sha256TwoBlockMessage)[1]!
    [ ⟨inline, "FIPS 180-4: 448-bit message, block 2 (state from block 1)",
        some (le32 sha256TwoBlockH1), block2, digest, fips⟩,
      ⟨inline, "FIPS 180-4: 448-bit message, block 2 (state from SHA256_INIT on block 1)",
        some (le32 sha256TwoBlockH1), block2, digest, fips⟩ ]
  else []

/-- Every case the corpus must contain. -/
def manifest : List KnownCase :=
  let kat := "KeccakKAT-3 (EthLib permutation tests)"
  let digest := "Keccak-256 reference digest"
  let keccakEmpty := ofHex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
  let keccakAbc := ofHex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
  sha256Known "SHA256" ++ sha256Known "SHA256_INIT" ++
  [ ⟨"KECCAK256", "KeccakKAT: zero state", some (zeros 200), none, ofHex keccakFZero, kat⟩,
    ⟨"KECCAK256", "KeccakKAT: permutation of the zero-state result", some (ofHex keccakFZero),
      none, ofHex keccakFZeroTwice, kat⟩,
    ⟨"KECCAK256", "Keccak-256(\"\"): zero state XOR padded block",
      some (keccakPad "" ++ zeros 64), none, keccakEmpty, digest⟩,
    ⟨"KECCAK256", "Keccak-256(\"abc\"): zero state XOR padded block",
      some (keccakPad "abc" ++ zeros 64), none, keccakAbc, digest⟩,
    ⟨"KECCAK256_ABSORB_PERMUTE", "jolt: zero state, zero block", some (zeros 200),
      some (zeros 136), ofHex keccakFZero, kat⟩,
    ⟨"KECCAK256_ABSORB_PERMUTE", "Keccak-256(\"\"): zero state, padded block", some (zeros 200),
      some (keccakPad ""), keccakEmpty, digest⟩,
    ⟨"KECCAK256_ABSORB_PERMUTE", "Keccak-256(\"abc\"): zero state, padded block",
      some (zeros 200), some (keccakPad "abc"), keccakAbc, digest⟩,
    ⟨"BLAKE2", "jolt: BLAKE2b-512(\"\"), zero block, t = 0, final", some (le64 blake2bH0),
      some (blake2Input (zeros 128) 0 1),
      ofHex ("786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419" ++
        "d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"),
      "RFC 7693 BLAKE2b-512 of the empty message"⟩,
    ⟨"BLAKE2", "jolt + RFC 7693 + EIP-152 vector 5: BLAKE2b-512(\"abc\"), t = 3, final",
      some (le64 blake2bH0), some (blake2Input blake2AbcBlock 3 1),
      ofHex ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
        "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"),
      "RFC 7693 appendix A; EIP-152 vector 5"⟩,
    ⟨"BLAKE2", "EIP-152 vector 6: \"abc\" block, t = 3, not final", some (le64 blake2bH0),
      some (blake2Input blake2AbcBlock 3 0),
      ofHex ("75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752" ++
        "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735"),
      "EIP-152 vector 6"⟩ ]

/-! ## Coverage -/

/-- The five inlines, with the fewest judged cases a corpus must hold for each: the known-answer
cases above plus 64 random cases, and for `BLAKE2` six cases with large counters and one Jolt
case. -/
def requiredInlines : List (String × Nat) :=
  [("SHA256", 72), ("SHA256_INIT", 70), ("KECCAK256", 70), ("KECCAK256_ABSORB_PERMUTE", 68),
    ("BLAKE2", 74)]

/-- The a16z/jolt commit whose tracer the corpus must come from, unless `--jolt-commit` names
another. -/
def defaultJoltCommit : String := "a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5"

end JoltTests.InlineKat
