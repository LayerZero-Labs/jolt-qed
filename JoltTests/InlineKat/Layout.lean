import JoltBytecode.Inlines.Spec

/-!
# Inline memory layouts

This module converts the memory that Jolt's hash inlines read into the arguments of their
specifications, and the specifications' results back into memory.
`JoltTests.InlineKat.Main` uses it to compare the specifications with Jolt's tracer.

Every inline takes two pointers: `rs1` points at the state, which the inline reads and
overwrites, and `rs2` points at the input, which it only reads.
RISC-V memory is little-endian, so a `u32` or `u64` stored at an address has its least
significant byte first.

The layouts below are those of Jolt's sequence builders at a16z/jolt commit
`a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`; the report
`reports/2026-11-11-inline-known-answer-hashes.md` cites the lines.

- `SHA256` and `SHA256_INIT`:
  - `rs1` holds the state, eight `u32` words little-endian, word `j` (the FIPS 180-4 variable
    `H_j`) at byte `4j`. `SHA256_INIT` does not read it.
  - `rs2` holds the 64 message bytes in order. The builder loads them as big-endian words, so
    message word `t` is the big-endian value of bytes `4t` to `4t + 3`, which is
    `Spec.inputWords rs2 0`.
  - The result is `Spec.compression (Spec.inputWords rs2 0) S`, where `S` is the state at `rs1`
    for `SHA256` and `Spec.initial` for `SHA256_INIT`. It is stored back at `rs1` in the same
    layout.
- `KECCAK256` and `KECCAK256_ABSORB_PERMUTE`:
  - `rs1` holds the 25 lanes, each a `u64` little-endian, lane `x + 5y` at byte `8(x + 5y)`.
    This is the FIPS 202 state string, as in `Keccak.Internal.laneAt`.
  - `KECCAK256` does not read `rs2`, and computes `Keccak.keccakF` of the state.
  - `KECCAK256_ABSORB_PERMUTE` reads 136 bytes at `rs2` as lanes 0 to 16, XORs them into the
    state, then permutes: `Keccak.keccakF (Keccak.Internal.absorbBlock 136 S rs2 0)`.
- `BLAKE2`:
  - `rs1` holds the state `h`, eight `u64` little-endian.
  - `rs2` holds the message block `m` (16 `u64` little-endian, bytes 0 to 127), then the
    counter `t` (one `u64`, bytes 128 to 135), then the final-block flag (one `u64`, bytes 136
    to 143).
  - The counter is 64 bits: the builder XORs `t` into word 12 of the work vector and leaves
    word 13 as `IV[5]`, so the high half `t1` of the 128-bit counter of RFC 7693 is zero.
  - The builder XORs `0 - flag` into word 14. For flag 1 that inverts the word, as the RFC's
    final block does, and for flag 0 it leaves the word alone. Other flag values are outside
    the specification, which takes a Boolean.
  - So for flags 0 and 1 the result is `Blake2b.Spec.compress 12 h m t (flag = 1)`, with `t`
    widened to 128 bits, stored back at `rs1` as eight `u64` little-endian.
-/

namespace JoltTests.InlineKat

open JoltSpec

/-! ## Bytes and numbers -/

/-- The little-endian value of the `n` bytes from index `start`; bytes past the end read as 0. -/
def leNat (bytes : ByteArray) (start n : Nat) : Nat :=
  (List.range n).foldr (fun i acc => (bytes[start + i]?.getD 0).toNat + 256 * acc) 0

/-- The `n` little-endian bytes of `v mod 256^n`. -/
def leBytes (v n : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (v / 256 ^ i % 256)

/-- Parse a string of hexadecimal digits, two per byte. -/
def ofHex? (s : String) : Option ByteArray := do
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let cs := s.toList
  if cs.length % 2 ≠ 0 then none
  let mut out := ByteArray.empty
  for i in [0:cs.length / 2] do
    let hi ← digit cs[2 * i]!
    let lo ← digit cs[2 * i + 1]!
    out := out.push (UInt8.ofNat (16 * hi + lo))
  return out

/-- `ofHex?`, with the empty array for a malformed string. -/
def ofHex (s : String) : ByteArray := (ofHex? s).getD .empty

/-- The bytes as lowercase hexadecimal digits. -/
def toHex (bytes : ByteArray) : String :=
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  String.ofList (bytes.toList.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

/-! ## SHA-256 -/

/-- The SHA-256 state stored at `rs1`: eight `u32` words, little-endian. -/
def sha256State (rs1 : ByteArray) : Sha256.Spec.State :=
  let w (j : Nat) : Sha256.Spec.Word := BitVec.ofNat 32 (leNat rs1 (4 * j) 4)
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩

/-- A SHA-256 state as stored at `rs1`. -/
def sha256Bytes (s : Sha256.Spec.State) : ByteArray :=
  ⟨(s.words.toList.flatMap fun w => leBytes w.toNat 4).toArray⟩

/-- What the specification says `SHA256` leaves at `rs1`. -/
def sha256Result (rs1 rs2 : ByteArray) : ByteArray :=
  sha256Bytes (Sha256.Spec.compression (Sha256.Spec.inputWords rs2 0) (sha256State rs1))

/-- What the specification says `SHA256_INIT` leaves at `rs1`. -/
def sha256InitResult (rs2 : ByteArray) : ByteArray :=
  sha256Bytes (Sha256.Spec.compression (Sha256.Spec.inputWords rs2 0) Sha256.Spec.initial)

/-! ## Keccak -/

/-- The Keccak state stored at `rs1`: lane `x + 5y` is the little-endian `u64` at `8(x + 5y)`. -/
def keccakState (rs1 : ByteArray) : Keccak.State :=
  Keccak.State.ofLanes fun x y => Keccak.Internal.laneAt rs1 (8 * (x.val + 5 * y.val))

/-- A Keccak state as stored at `rs1`. -/
def keccakBytes (S : Keccak.State) : ByteArray :=
  ⟨((List.range 25).flatMap fun i =>
    Keccak.Internal.bytesOfLane (S.lane (Fin.ofNat 5 (i % 5)) (Fin.ofNat 5 (i / 5)))).toArray⟩

/-- What the specification says `KECCAK256` leaves at `rs1`. -/
def keccak256Result (rs1 : ByteArray) : ByteArray :=
  keccakBytes (Keccak.keccakF (keccakState rs1))

/-- What the specification says `KECCAK256_ABSORB_PERMUTE` leaves at `rs1`. -/
def keccak256AbsorbResult (rs1 rs2 : ByteArray) : ByteArray :=
  keccakBytes (Keccak.keccakF (Keccak.Internal.absorbBlock 136 (keccakState rs1) rs2 0))

/-! ## BLAKE2b -/

/-- `n` little-endian `u64` words from byte `start`, as words of the model. -/
def blake2Words (n : Nat) (bytes : ByteArray) (start : Nat) : Vector Blake2b.Spec.Word n :=
  Vector.ofFn fun i => BitVec.ofNat 64 (leNat bytes (start + 8 * i.val) 8)

/-- The counter `t` at `rs2 + 128`. -/
def blake2Counter (rs2 : ByteArray) : Nat := leNat rs2 128 8

/-- The final-block flag at `rs2 + 136`. -/
def blake2Flag (rs2 : ByteArray) : Nat := leNat rs2 136 8

/-- A BLAKE2b state as stored at `rs1`. -/
def blake2Bytes (h : Vector Blake2b.Spec.Word 8) : ByteArray :=
  ⟨(h.toList.flatMap fun w => leBytes w.toNat 8).toArray⟩

/-- What the specification says `BLAKE2` leaves at `rs1`, for a flag of 0 or 1.

The 64-bit counter is the low half of the 128-bit counter of the specification. -/
def blake2Result (rs1 rs2 : ByteArray) (final : Bool) : ByteArray :=
  blake2Bytes (Blake2b.Spec.compress 12 (blake2Words 8 rs1 0) (blake2Words 16 rs2 0)
    (BitVec.ofNat 128 (blake2Counter rs2)) final)

end JoltTests.InlineKat
