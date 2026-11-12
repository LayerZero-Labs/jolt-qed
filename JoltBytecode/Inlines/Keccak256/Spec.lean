import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Keccak-f[1600] and absorb-then-permute: the specification

This file is the specification of Jolt's `KECCAK256` and `KECCAK256_ABSORB_PERMUTE` inlines.
`KECCAK256` computes `Keccak.keccakF S` on the 25-lane state `S`, and
`KECCAK256_ABSORB_PERMUTE` computes `Keccak.keccakF (Keccak.Internal.absorbBlock 136 S block 0)`.
The lane code is specified by the bit-level model `KeccakBits.permutation` of FIPS 202, copied
below with the maps `KeccakBits.ofLanes` and `KeccakBits.toLanes` between the two state types.
EthLib's theorem `KeccakBits.toLanes_permutation`, copied below with its proof, says that the two
agree: `toLanes (permutation a) = keccakF (toLanes a)`.

## Provenance

The definitions are copied from EthLib.

- Repository: `ethereum/EthLib` (<https://github.com/ethereum/EthLib>)
- Commit: `5310b3ec007b05a2bfe33b01125392b07df5f636`
- Licence: CC0-1.0
- Source files:
  - `EthLib/Base/Bytes.lean`: `byteAt`;
  - `EthLib/Cryptography/Hash/Keccak.lean`: the whole file (the lane state, the constants and
    the algorithms that define them, the five step mappings, `keccakF`, the sponge with
    `Internal.absorbBlock`, `keccak256`, `keccak512` and the incremental `Hasher`);
  - `EthLib/Cryptography/Proofs/Hash/Keccak.lean`: the definitions `State.lane`,
    `State.ofLanes` and `State.column`, the theorems `theta_eq`, `rho_eq`, `pi_eq`, `chi_eq`
    and `iota_eq` (each proved by `rfl`), and `roundConstants_eq` and `rhoOffsets_eq`, which
    derive `RC` and `RHO` from FIPS 202 Algorithms 5, 6 and 2;
  - `EthLib/Cryptography/Proofs/Hash/KeccakPermutation.lean`: the lane lemmas
    `getLsbD_rotl`, `lane_ext`, `lane_ofLanes`, `ofLanes_lane` and `State.ext_lane`, which the
    proof below needs;
  - `EthLib/Cryptography/Proofs/Models/KeccakBits.lean`: the whole file (the bit model);
  - `EthLib/Cryptography/Proofs/Hash/KeccakBitsPermutation.lean`: the whole file, which proves
    `toLanes_permutation` through one lemma per step mapping.

Each copied declaration, with its docstring, is unchanged except for these edits:

- the namespaces `EthLib.Cryptography.Hash.Keccak`, `EthLib.Cryptography.Models.KeccakBits` and
  `EthLib.Base` are renamed `JoltSpec.Keccak`, `JoltSpec.KeccakBits` and `JoltSpec.Base`, and
  `open EthLib.Base (byteAt)` becomes `open JoltSpec.Base (byteAt)`;
- the module-system markers (`module`, `public import`, `@[expose] public section`) are dropped,
  because jolt-qed does not use the module system;
- the imports of the source files are replaced by `Mathlib.Data.Fintype.Basic` and
  `Mathlib.Tactic.FinCases`, which `lane_ofLanes` needs for `fin_cases`;
- the section headers between declarations are adapted to this file.

`scripts/check-ethlib-copies.sh` checks every declaration of this file against EthLib.

Five proofs use `decide +kernel`, as in EthLib: `roundConstants_eq`, `rhoOffsets_eq`, and the
three constant facts `rhoOffset_eq`, `rhoOffset_lt` and `roundConstantBit_eq` on which
`toLanes_permutation` rests. `AGENTS.md` allows it when the kernel check is fast. Checked alone,
each takes under two seconds, the slowest being `roundConstantBit_eq` at 1.4 seconds
(`reports/2026-11-11-inline-known-answer-hashes.md` lists the times).

## What was left out

- The padding lemmas of `Proofs/Hash/Keccak.lean` (`padding_data`, `pad_injective`, ...) and the
  bijectivity proof `keccakF_bijective` of `Proofs/Hash/KeccakPermutation.lean`, with the rest of
  that file's rotation and XOR lemmas: the inline specifications do not need them.
-/

namespace JoltSpec.Base

/-- The byte at index `i` of the buffer, or `0` past its end.

It reads the byte in place, since the array of all the bytes would cost a copy of the buffer. -/
@[inline] def byteAt (data : ByteArray) (i : Nat) : UInt8 :=
  if h : i < data.size then data[i] else 0

end JoltSpec.Base

namespace JoltSpec.Keccak

/-! ## The state

FIPS 202 §3.1.2 views the 1600-bit state as a 5 x 5 array of lanes, each of `w = 64` bits.

Lane `(x, y)` has the index `x + 5 * y`, so the 25 lanes run row by row.

Bit `z` of a lane is bit `z` of its 64-bit word.

That is the standard's own order: bit `64 * (x + 5y) + z` of the state string is `A[x, y, z]`.

So byte `k` of the state string is byte `k mod 8` of lane `k / 8`, least significant first.

FIPS 202 §3.1.3 and Appendix B.1 give that byte order.

The state is a record with one field per lane, so each step mapping below names its lanes.
-/

/-- Lanes in the state: 1600 bits of 64-bit lanes. -/
def LANES : Nat := 25

/-- Rounds in Keccak-f[1600].

FIPS 202 §3.4 sets `n_r = 12 + 2l`, with `l = 6` because `w = 2^6`. -/
def ROUNDS : Nat := 24

/-- The Keccak-f[1600] state: 25 lanes of 64 bits.

The field with the number `x + 5y` holds lane `(x, y)`. -/
structure State where
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 :
    UInt64)
  deriving DecidableEq

/-- The all-zero state, where every sponge starts (FIPS 202 §4, Algorithm 8, step 5). -/
def State.zero : State :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Rotate a lane towards its high bits by `n` positions, `n < 64`.

Bit `z` moves to bit `(z + n) mod 64`, which is what `rho` and `theta` ask of the bit index. -/
@[inline] def rotl (v : UInt64) (n : UInt64) : UInt64 :=
  -- The two shifts are disjoint and together move every bit once.
  -- At `n = 0` the right shift is by 64, which wraps to 0, and the result is still `v`.
  (v <<< n) ||| (v >>> (64 - n))

/-! ## The constants

FIPS 202 defines the round constants and the rotation offsets by two algorithms, transcribed here.

Its Table 2 lists the offsets before their reduction mod 64, and it lists no round constants.

The tables used by the permutation are proved equal to them in `Proofs/Hash/Keccak.lean`. -/

namespace Internal

/-- One step of the linear feedback shift register of FIPS 202 §3.2.5, Algorithm 5.

The register `R` is eight bits, `R[0]` in bit 0 of the number.

```text
    R := 0 || R                      prepend a zero: every bit moves one place up
    R[0], R[4], R[5], R[6] ^= R[8]   feed back the bit that moved out
    R := Trunc_8(R)                  drop bit 8
```
-/
def lfsrStep (r : Nat) : Nat :=
  -- Prepending a zero bit at index 0 shifts every bit one index up.
  let r := r <<< 1
  -- The bit pushed to index 8 is fed back into indices 0, 4, 5 and 6.
  -- 0x71 is 0111 0001 in binary: bits 0, 4, 5 and 6.
  let feedback := if (r >>> 8) % 2 = 1 then 0x71 else 0
  -- Truncation keeps indices 0 to 7.
  (r ^^^ feedback) % 256

/-- The bit `rc(t)` of FIPS 202 §3.2.5, Algorithm 5.

The register starts at `10000000`, that is `R[0] = 1`, and runs `t mod 255` steps.

The output is the bit `R[0]`. -/
def rc (t : Nat) : Bool :=
  -- The register has period 255, so only `t mod 255` steps matter.
  -- Algorithm 5 returns 1 at once when that count is zero, which zero steps also gives.
  (Nat.repeat lfsrStep (t % 255) 1) % 2 = 1

/-- The round constant of round `i_r`, by FIPS 202 §3.2.5, Algorithm 6.

For `j` from 0 to `l = 6`, bit `2^j - 1` of the lane is `rc(j + 7 * i_r)`.

All other bits are zero, so only bits 0, 1, 3, 7, 15, 31 and 63 can be set. -/
def roundConstant (ir : Nat) : UInt64 :=
  -- Seven candidate bits, one per `j`, each placed at position `2^j - 1`.
  (List.range 7).foldl
    (fun acc j => if rc (j + 7 * ir) then acc ||| ((1 : UInt64) <<< UInt64.ofNat (2 ^ j - 1)) else acc)
    0

/-- The rotation offsets of FIPS 202 §3.2.2, Algorithm 2, indexed like the state.

Lane `(0, 0)` is not rotated.

The walk starts at `(x, y) = (1, 0)` and visits the other 24 lanes once each:

```text
    step t:  offset of (x, y) is (t + 1)(t + 2)/2 mod 64
             then (x, y) := (y, (2x + 3y) mod 5)
```
-/
def rhoOffsets : Vector Nat LANES := Id.run do
  -- Every lane starts at offset 0, which is final for lane (0, 0).
  let mut offsets : Vector Nat LANES := Vector.replicate LANES 0
  let mut x := 1
  let mut y := 0
  for t in [:24] do
    -- Record the offset of the current lane, at index x + 5y.
    offsets := offsets.setIfInBounds (x + 5 * y) (((t + 1) * (t + 2) / 2) % 64)
    -- Move to the next lane of the walk.
    (x, y) := (y, (2 * x + 3 * y) % 5)
  return offsets

end Internal

/-- The 24 round constants `RC[i_r]` of iota.

Each equals the constant FIPS 202 §3.2.5, Algorithm 6 derives for its round.

The kernel checks this in `Proofs/Hash/Keccak.lean`. -/
def RC : Vector UInt64 ROUNDS := #v[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offset of each lane in rho, indexed like the state.

Each equals the offset FIPS 202 §3.2.2, Algorithm 2 assigns to its lane.

The kernel checks this in `Proofs/Hash/Keccak.lean`.

```text
            x = 0   1   2   3   4
    y = 0       0   1  62  28  27
    y = 1      36  44   6  55  20
    y = 2       3  10  43  25  39
    y = 3      41  45  15  21   8
    y = 4      18   2  61  56  14
```
-/
def RHO : Vector UInt64 LANES := #v[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

/-! ## The step mappings

The five step mappings of FIPS 202 §3.2, each written out for the 25 lanes.

`A[x, y]` is lane `(x, y)` of the input, and the coordinates are taken mod 5 (§3.1.4).

`Proofs/Hash/Keccak.lean` proves that each mapping is the formula of the standard. -/

/-- Theta, FIPS 202 §3.2.1, Algorithm 1.

Each lane is XORed with the parities of two nearby columns.

The parity of column `x` is `C[x] = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4]`.

Lane `(x, y)` becomes `A[x, y] ^ D[x]`, with `D[x] = C[x - 1] ^ rot(C[x + 1], 1)`. -/
@[inline] def theta (A : State) : State :=
  -- Step 1: the parity of each column.
  let c0 := A.a0 ^^^ A.a5 ^^^ A.a10 ^^^ A.a15 ^^^ A.a20
  let c1 := A.a1 ^^^ A.a6 ^^^ A.a11 ^^^ A.a16 ^^^ A.a21
  let c2 := A.a2 ^^^ A.a7 ^^^ A.a12 ^^^ A.a17 ^^^ A.a22
  let c3 := A.a3 ^^^ A.a8 ^^^ A.a13 ^^^ A.a18 ^^^ A.a23
  let c4 := A.a4 ^^^ A.a9 ^^^ A.a14 ^^^ A.a19 ^^^ A.a24
  -- Step 2: `x - 1` is `x + 4` mod 5, and the bit shift `z - 1` is a rotation by 1.
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  -- Step 3: every lane of column `x` takes the same `D[x]`.
  ⟨A.a0 ^^^ d0, A.a1 ^^^ d1, A.a2 ^^^ d2, A.a3 ^^^ d3, A.a4 ^^^ d4,
   A.a5 ^^^ d0, A.a6 ^^^ d1, A.a7 ^^^ d2, A.a8 ^^^ d3, A.a9 ^^^ d4,
   A.a10 ^^^ d0, A.a11 ^^^ d1, A.a12 ^^^ d2, A.a13 ^^^ d3, A.a14 ^^^ d4,
   A.a15 ^^^ d0, A.a16 ^^^ d1, A.a17 ^^^ d2, A.a18 ^^^ d3, A.a19 ^^^ d4,
   A.a20 ^^^ d0, A.a21 ^^^ d1, A.a22 ^^^ d2, A.a23 ^^^ d3, A.a24 ^^^ d4⟩

/-- Rho, FIPS 202 §3.2.2, Algorithm 2.

Each lane is rotated by its own offset from the table above.

The offsets are written as numbers, so that each rotation is by a constant. -/
@[inline] def rho (A : State) : State :=
  ⟨rotl A.a0 0, rotl A.a1 1, rotl A.a2 62, rotl A.a3 28, rotl A.a4 27,
   rotl A.a5 36, rotl A.a6 44, rotl A.a7 6, rotl A.a8 55, rotl A.a9 20,
   rotl A.a10 3, rotl A.a11 10, rotl A.a12 43, rotl A.a13 25, rotl A.a14 39,
   rotl A.a15 41, rotl A.a16 45, rotl A.a17 15, rotl A.a18 21, rotl A.a19 8,
   rotl A.a20 18, rotl A.a21 2, rotl A.a22 61, rotl A.a23 56, rotl A.a24 14⟩

/-- Pi, FIPS 202 §3.2.3, Algorithm 3.

The lanes are rearranged: `A'[x, y] = A[(x + 3y) mod 5, x]`. -/
@[inline] def pi (A : State) : State :=
  -- Output row `y` takes, for each `x`, lane `x` of input column `(x + 3y) mod 5`.
  ⟨A.a0, A.a6, A.a12, A.a18, A.a24,
   A.a3, A.a9, A.a10, A.a16, A.a22,
   A.a1, A.a7, A.a13, A.a19, A.a20,
   A.a4, A.a5, A.a11, A.a17, A.a23,
   A.a2, A.a8, A.a14, A.a15, A.a21⟩

/-- Chi, FIPS 202 §3.2.4, Algorithm 4.

The only nonlinear step: `A'[x, y] = A[x, y] ^ ((A[x + 1, y] ^ 1) & A[x + 2, y])`.

XOR with an all-ones lane is the complement. -/
@[inline] def chi (A : State) : State :=
  -- Each lane combines with the next two lanes of its row, which wraps around.
  ⟨A.a0 ^^^ (~~~A.a1 &&& A.a2), A.a1 ^^^ (~~~A.a2 &&& A.a3), A.a2 ^^^ (~~~A.a3 &&& A.a4),
   A.a3 ^^^ (~~~A.a4 &&& A.a0), A.a4 ^^^ (~~~A.a0 &&& A.a1),
   A.a5 ^^^ (~~~A.a6 &&& A.a7), A.a6 ^^^ (~~~A.a7 &&& A.a8), A.a7 ^^^ (~~~A.a8 &&& A.a9),
   A.a8 ^^^ (~~~A.a9 &&& A.a5), A.a9 ^^^ (~~~A.a5 &&& A.a6),
   A.a10 ^^^ (~~~A.a11 &&& A.a12), A.a11 ^^^ (~~~A.a12 &&& A.a13),
   A.a12 ^^^ (~~~A.a13 &&& A.a14), A.a13 ^^^ (~~~A.a14 &&& A.a10),
   A.a14 ^^^ (~~~A.a10 &&& A.a11),
   A.a15 ^^^ (~~~A.a16 &&& A.a17), A.a16 ^^^ (~~~A.a17 &&& A.a18),
   A.a17 ^^^ (~~~A.a18 &&& A.a19), A.a18 ^^^ (~~~A.a19 &&& A.a15),
   A.a19 ^^^ (~~~A.a15 &&& A.a16),
   A.a20 ^^^ (~~~A.a21 &&& A.a22), A.a21 ^^^ (~~~A.a22 &&& A.a23),
   A.a22 ^^^ (~~~A.a23 &&& A.a24), A.a23 ^^^ (~~~A.a24 &&& A.a20),
   A.a24 ^^^ (~~~A.a20 &&& A.a21)⟩

/-- Iota, FIPS 202 §3.2.5, Algorithm 6.

The round constant is XORed into lane `(0, 0)`, the only lane it touches. -/
@[inline] def iota (ir : Fin ROUNDS) (A : State) : State :=
  { A with a0 := A.a0 ^^^ RC[ir] }

/-! ## The permutation -/

/-- One round, FIPS 202 §3.3: `Rnd(A, i_r) = iota(chi(pi(rho(theta(A)))), i_r)`. -/
def round (ir : Fin ROUNDS) (A : State) : State :=
  iota ir (chi (pi (rho (theta A))))

/-- Keccak-f[1600], FIPS 202 §3.4: Keccak-p[1600, 24], rounds 0 to 23 in order.

With `n_r = 24 = 12 + 2l` the rounds run from `12 + 2l - n_r = 0` to `23` (§3.3, Algorithm 7). -/
def keccakF (A : State) : State :=
  roundsFrom 0 A
where
  /-- Rounds `i` to 23, in order. -/
  roundsFrom (i : Nat) (A : State) : State :=
    if h : i < ROUNDS then roundsFrom (i + 1) (round ⟨i, h⟩ A) else A
  termination_by ROUNDS - i

/-! ## The sponge

FIPS 202 §5.2 defines the Keccak family on byte strings `M` and output lengths `d`:

```text
    Keccak[c](M, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 - c](M, d)
```

Keccak-256 is `Keccak[512](M, 256)`, and Keccak-512 is `Keccak[1024](M, 512)`.

SHA3-256 is `Keccak[512](M || 01, 256)` (§6.1), so the two differ only in the two suffix bits.

In bytes, the first padding byte is `0x01` for Keccak-256 and `0x06` for SHA3-256.

The Keccak reference, version 3.0, calls Keccak-256 Keccak[r = 1088, c = 512].

It calls Keccak-512 Keccak[r = 576, c = 1024].

The padding and the absorbing below take the rate `r` in bytes. -/

/-- The rate of Keccak-256 in bytes: `r = 1600 - c = 1088` bits.

Each permutation absorbs this many message bytes. -/
def RATE : Nat := 136

/-- The digest length of Keccak-256 in bytes: `d = 256` bits. -/
def DIGEST_LEN : Nat := 32

/-- The rate of Keccak-512 in bytes: `r = 1600 - c = 576` bits. -/
def RATE_512 : Nat := 72

/-- The digest length of Keccak-512 in bytes: `d = 512` bits. -/
def DIGEST_LEN_512 : Nat := 64

/-- Byte `i` of the padding of a message of `len` bytes, at a rate of `rate` bytes.

- The first 1 bit of pad10*1 is bit 0 of the first padding byte.
- The final 1 bit is bit 7 of the last padding byte, and may share the first one's byte. -/
def paddingByte (rate len i : Nat) : UInt8 :=
  (if i = 0 then 0x01 else 0) ||| (if i + 1 = rate - len % rate then 0x80 else 0)

/-- The padding of a message of `len` bytes at a rate of `rate` bytes: pad10*1 of FIPS 202 §5.1.

The rule appends a 1 bit, then zeros, then a final 1 bit, so the total is a multiple of the rate.

At least two bits are appended.

So a whole block of padding is added when `len` is a multiple of the rate.

On byte strings the bits become bytes, least significant bit first (Appendix B.1):

```text
    k = rate - len mod rate bytes of padding, 1 <= k <= rate

    k = 1:   0x81                       the two 1 bits share one byte
    k >= 2:  0x01 0x00 ... 0x00 0x80    first bit 0 of the first byte, last bit 7 of the last
```
-/
def padding (rate len : Nat) : ByteArray :=
  -- The padding fills the block the message ends in, and a whole block when it ends exactly.
  let k := rate - len % rate
  -- Zeros, then bit 0 set in the first byte and bit 7 set in the last.
  ⟨((Array.replicate k 0).modify 0 (· ||| 0x01)).modify (k - 1) (· ||| 0x80)⟩

/-- The message followed by its padding: the string `P` of FIPS 202 §4, Algorithm 8, step 1. -/
def pad (rate : Nat) (msg : ByteArray) : ByteArray :=
  msg ++ padding rate msg.size

/-- The number of rate-sized blocks the padded message splits into: `n = len(P) / r`. -/
def blockCount (rate len : Nat) : Nat :=
  -- The padding brings the length up to the next multiple of the rate, strictly above `len`.
  len / rate + 1

namespace Internal

open JoltSpec.Base (byteAt)

/-- The lane that the 8 bytes from index `i` spell, the first byte least significant.

So byte `j` carries bits `8j` to `8j + 7` of the lane, as in FIPS 202 §3.1.2.

Bytes past the end of the string read as zero. -/
@[inline] def laneAt (bytes : ByteArray) (i : Nat) : UInt64 :=
  (byteAt bytes i).toUInt64 ||| (byteAt bytes (i + 1)).toUInt64 <<< 8 |||
    (byteAt bytes (i + 2)).toUInt64 <<< 16 ||| (byteAt bytes (i + 3)).toUInt64 <<< 24 |||
    (byteAt bytes (i + 4)).toUInt64 <<< 32 ||| (byteAt bytes (i + 5)).toUInt64 <<< 40 |||
    (byteAt bytes (i + 6)).toUInt64 <<< 48 ||| (byteAt bytes (i + 7)).toUInt64 <<< 56

/-- The 8 bytes of a lane, the least significant first. -/
def bytesOfLane (v : UInt64) : List UInt8 :=
  [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
    (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8]

/-- Lane `i` of the block of `rate` bytes from index `start`, or zero past the rate. -/
@[inline] def blockLane (rate : Nat) (bytes : ByteArray) (start i : Nat) : UInt64 :=
  if 8 * i < rate then laneAt bytes (start + 8 * i) else 0

/-- XOR the block of `rate` bytes from index `start` into the state, for a rate of at most 136.

This is `S ^ (P_i || 0^c)` of FIPS 202 §4, Algorithm 8, step 6.

A block of 136 bytes covers lanes 0 to 16, and a block of 72 bytes covers lanes 0 to 8.

The lanes past the block are XORed with zero, so they are left alone. -/
def absorbBlock (rate : Nat) (S : State) (bytes : ByteArray) (start : Nat) : State :=
  let lane := blockLane rate bytes start
  { S with
    a0 := S.a0 ^^^ lane 0, a1 := S.a1 ^^^ lane 1, a2 := S.a2 ^^^ lane 2,
    a3 := S.a3 ^^^ lane 3, a4 := S.a4 ^^^ lane 4, a5 := S.a5 ^^^ lane 5,
    a6 := S.a6 ^^^ lane 6, a7 := S.a7 ^^^ lane 7, a8 := S.a8 ^^^ lane 8,
    a9 := S.a9 ^^^ lane 9, a10 := S.a10 ^^^ lane 10, a11 := S.a11 ^^^ lane 11,
    a12 := S.a12 ^^^ lane 12, a13 := S.a13 ^^^ lane 13, a14 := S.a14 ^^^ lane 14,
    a15 := S.a15 ^^^ lane 15, a16 := S.a16 ^^^ lane 16 }

/-- The first `d = 256` bits of the state: `Trunc_d(S)` of FIPS 202 §4, Algorithm 8, step 9.

The digest fits in the first block of output, so no further permutation is needed.

Its 32 bytes are the bytes of lanes 0 to 3, in order. -/
def squeeze (S : State) : Vector UInt8 DIGEST_LEN :=
  ⟨(bytesOfLane S.a0 ++ bytesOfLane S.a1 ++ bytesOfLane S.a2 ++ bytesOfLane S.a3).toArray, rfl⟩

/-- The first `d = 512` bits of the state: `Trunc_d(S)` of FIPS 202 §4, Algorithm 8, step 9.

The digest fits in the first 72 bytes of output, so no further permutation is needed.

Its 64 bytes are the bytes of lanes 0 to 7, in order. -/
def squeeze512 (S : State) : Vector UInt8 DIGEST_LEN_512 :=
  ⟨(bytesOfLane S.a0 ++ bytesOfLane S.a1 ++ bytesOfLane S.a2 ++ bytesOfLane S.a3 ++
    bytesOfLane S.a4 ++ bytesOfLane S.a5 ++ bytesOfLane S.a6 ++ bytesOfLane S.a7).toArray, rfl⟩

/-- Absorb `n` blocks of `rate` bytes from index `start` on, in order, one permutation each.

This is FIPS 202 §4, Algorithm 8, step 6.

The blocks are read in place, so a long message is never copied block by block. -/
def absorbBlocks (f : State → State) (rate : Nat) (bytes : ByteArray) :
    Nat → Nat → State → State
  | 0, _, S => S
  | n + 1, start, S =>
    absorbBlocks f rate bytes n (start + rate) (f (absorbBlock rate S bytes start))

end Internal

/-- The absorbing phase of the sponge of FIPS 202 §4, Algorithm 8, at a rate of `rate` bytes.

The rate is at most 136 bytes, so each block fits in the lanes that it XORs.

```text
    P = M || pad10*1(r, len(M))              pad
    P = P_0 || ... || P_{n-1}                cut into blocks of r bits
    S = 0^1600                               start from the zero state
    for each block P_i:
        S = f(S ^ (P_i || 0^c))              absorb
```

FIPS 202 §4 defines the sponge for any permutation `f`, so the permutation is an argument. -/
def spongeAbsorb (f : State → State) (rate : Nat) (msg : ByteArray) : State :=
  -- Step 1: append the padding, so the length is a multiple of the rate.
  -- Steps 2 to 6: from the zero state, absorb the blocks in order, one permutation each.
  Internal.absorbBlocks f rate (pad rate msg) (blockCount rate msg.size) 0 State.zero

/-- Keccak-256 of a byte string: `Keccak[512](M, 256)` of FIPS 202 §5.2.

It absorbs at a rate of 136 bytes.

One block of output holds the 32 digest bytes, so no further permutation is needed. -/
def keccak256 (msg : ByteArray) : Vector UInt8 DIGEST_LEN :=
  Internal.squeeze (spongeAbsorb keccakF RATE msg)

/-- Keccak-512 of a byte string: `Keccak[1024](M, 512)` of FIPS 202 §5.2.

It absorbs at a rate of 72 bytes, with the same permutation as Keccak-256.

One block of output holds the 64 digest bytes, so no further permutation is needed. -/
def keccak512 (msg : ByteArray) : Vector UInt8 DIGEST_LEN_512 :=
  Internal.squeeze512 (spongeAbsorb keccakF RATE_512 msg)

/-! ## Incremental hashing

A hasher absorbs a message in pieces, for a digest of all the pieces so far.

It keeps the state after the whole blocks, and the bytes of the block not yet full.

The digest pads those bytes and absorbs the last block, without changing the hasher. -/

/-- A Keccak-256 hasher: the state after the whole blocks so far, and the bytes after them. -/
structure Hasher where
  /-- The state after every whole block so far. -/
  state : State
  /-- The bytes after the last whole block, fewer than the rate. -/
  pending : ByteArray

namespace Hasher

/-- The hasher of the empty message. -/
def empty : Hasher := ⟨State.zero, .empty⟩

/-- Absorb more bytes: every block they complete goes through the permutation. -/
def absorb (h : Hasher) (data : ByteArray) : Hasher :=
  let bytes := h.pending ++ data
  let count := bytes.size / RATE
  ⟨Internal.absorbBlocks keccakF RATE bytes count 0 h.state,
    bytes.extract (RATE * count) bytes.size⟩

/-- The Keccak-256 digest of every byte absorbed so far: pad the last block, absorb it, squeeze. -/
def digest (h : Hasher) : Vector UInt8 DIGEST_LEN :=
  let last := h.pending ++ padding RATE h.pending.size
  Internal.squeeze (Internal.absorbBlocks keccakF RATE last 1 0 h.state)

end Hasher


/-! ## The lanes of a state -/

/-- Lane `(x, y)` of a state, the field with the number `x + 5y`. -/
def State.lane (A : State) (x y : Fin 5) : UInt64 :=
  [A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, A.a6, A.a7, A.a8, A.a9, A.a10, A.a11, A.a12, A.a13,
    A.a14, A.a15, A.a16, A.a17, A.a18, A.a19, A.a20, A.a21, A.a22, A.a23,
    A.a24][x.val + 5 * y.val]!

/-- The state whose lane `(x, y)` is `f x y`. -/
def State.ofLanes (f : Fin 5 → Fin 5 → UInt64) : State :=
  ⟨f 0 0, f 1 0, f 2 0, f 3 0, f 4 0, f 0 1, f 1 1, f 2 1, f 3 1, f 4 1,
    f 0 2, f 1 2, f 2 2, f 3 2, f 4 2, f 0 3, f 1 3, f 2 3, f 3 3, f 4 3,
    f 0 4, f 1 4, f 2 4, f 3 4, f 4 4⟩

/-- The parity `C[x]` of column `x`: the XOR of its five lanes. -/
def State.column (A : State) (x : Fin 5) : UInt64 :=
  A.lane x 0 ^^^ A.lane x 1 ^^^ A.lane x 2 ^^^ A.lane x 3 ^^^ A.lane x 4

/-- Theta is `A'[x, y] = A[x, y] ^ C[x - 1] ^ rot(C[x + 1], 1)`, FIPS 202 §3.2.1. -/
theorem theta_eq (A : State) :
    theta A = State.ofLanes fun x y =>
      A.lane x y ^^^ (A.column (x - 1) ^^^ rotl (A.column (x + 1)) 1) :=
  rfl

/-- Rho rotates lane `(x, y)` by the offset of index `x + 5y`, FIPS 202 §3.2.2. -/
theorem rho_eq (A : State) :
    rho A = State.ofLanes fun x y =>
      rotl (A.lane x y) (RHO[x.val + 5 * y.val]'(by simp only [LANES]; omega)) :=
  rfl

/-- Pi is `A'[x, y] = A[(x + 3y) mod 5, x]`, FIPS 202 §3.2.3. -/
theorem pi_eq (A : State) : pi A = State.ofLanes fun x y => A.lane (x + 3 * y) x :=
  rfl

/-- Chi is `A'[x, y] = A[x, y] ^ ((A[x + 1, y] ^ 1) & A[x + 2, y])`, FIPS 202 §3.2.4. -/
theorem chi_eq (A : State) :
    chi A = State.ofLanes fun x y => A.lane x y ^^^ (~~~A.lane (x + 1) y &&& A.lane (x + 2) y) :=
  rfl

/-- Iota XORs the round constant into lane `(0, 0)` and leaves the others, FIPS 202 §3.2.5. -/
theorem iota_eq (ir : Fin ROUNDS) (A : State) :
    iota ir A = State.ofLanes fun x y =>
      if x = 0 ∧ y = 0 then A.lane x y ^^^ RC[ir] else A.lane x y :=
  rfl


/-! ## The derived constants -/

/-- The table of round constants is what FIPS 202 §3.2.5, Algorithm 6 derives.

So no round constant is taken on trust. -/
theorem roundConstants_eq : RC = Vector.ofFn fun ir => Internal.roundConstant ir := by
  -- 24 constants of 7 bits each, with at most 167 register steps per bit.
  decide +kernel

/-- The table of rotation offsets is what FIPS 202 §3.2.2, Algorithm 2 derives.

So no rotation offset is taken on trust. -/
theorem rhoOffsets_eq : RHO.map UInt64.toNat = Internal.rhoOffsets := by
  -- The walk of 24 steps, run by the kernel.
  decide +kernel

/-! ## Rotations and lanes -/

/-- Bit `i` of a lane rotated by `n` is bit `i - n` of the lane, mod 64. -/
theorem getLsbD_rotl (v n : UInt64) (hn : n.toNat ≤ 64) (i : Nat) (hi : i < 64) :
    (rotl v n).toBitVec.getLsbD i = v.toBitVec.getLsbD ((i + 64 - n.toNat % 64) % 64) := by
  unfold rotl
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.getLsbD_or]
  simp [hi]
  rw [show (18446744073709551616 - n.toNat) % 64 = (64 - n.toNat % 64) % 64 by omega]
  generalize hk : n.toNat % 64 = k
  have k64 : k < 64 := by omega
  by_cases h0 : k = 0
  · subst h0
    simp [Nat.mod_eq_of_lt hi, BitVec.getLsbD_eq_getElem, hi]
  by_cases hlt : i < k
  · rw [Nat.mod_eq_of_lt (by omega : 64 - k < 64), Nat.mod_eq_of_lt (by omega : i + 64 - k < 64)]
    rw [show 64 - k + i = i + 64 - k by omega]
    simp [hlt]
  · rw [Nat.mod_eq_of_lt (by omega : 64 - k < 64), BitVec.getLsbD_of_ge _ _ (by omega)]
    rw [show (i + 64 - k) % 64 = i - k by omega]
    simp [hlt, BitVec.getLsbD_eq_getElem, (by omega : i - k < 64)]

/-- Two lanes are equal when all their 64 bits are. -/
theorem lane_ext {v w : UInt64} (h : ∀ i < 64, v.toBitVec.getLsbD i = w.toBitVec.getLsbD i) :
    v = w :=
  UInt64.toBitVec_inj.1 (BitVec.eq_of_getLsbD_eq h)

/-- Each lane of a state built from lanes is the lane it was given. -/
theorem lane_ofLanes (f : Fin 5 → Fin 5 → UInt64) (x y : Fin 5) :
    (State.ofLanes f).lane x y = f x y := by
  fin_cases x <;> fin_cases y <;> rfl

/-- A state is the state built from its own lanes. -/
theorem ofLanes_lane (A : State) : State.ofLanes A.lane = A := by
  cases A
  rfl

/-- Two states with the same lanes are equal. -/
theorem State.ext_lane {A B : State} (h : ∀ x y, A.lane x y = B.lane x y) : A = B := by
  rw [← ofLanes_lane A, ← ofLanes_lane B]
  exact congrArg State.ofLanes (funext fun x => funext (h x))

end JoltSpec.Keccak

namespace JoltSpec.KeccakBits


/-- One bit at each bounded Keccak state coordinate. -/
abbrev State := Fin 5 → Fin 5 → Fin 64 → Bool

/-- Wrap an x or y coordinate. -/
def xy (n : Nat) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by decide)⟩

/-- Wrap a bit coordinate within a lane. -/
def zcoord (n : Nat) : Fin 64 := ⟨n % 64, Nat.mod_lt _ (by decide)⟩

/-- Theta column parity, FIPS 202 Algorithm 1, step 1. -/
def column (a : State) (x : Fin 5) (z : Fin 64) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (Bool.xor (a x 0 z) (a x 1 z)) (a x 2 z)) (a x 3 z)) (a x 4 z)

/-- Theta, FIPS 202 Algorithm 1. -/
def theta (a : State) : State := fun x y z =>
  Bool.xor (a x y z)
    (Bool.xor (column a (xy (x.val + 4)) z)
      (column a (xy (x.val + 1)) (zcoord (z.val + 63))))

/-- Position visited by the rho walk after `steps` applications.

The function accepts any natural number of steps.

FIPS 202 Algorithm 2 uses the first 24 positions.
-/
def rhoPosition (steps : Nat) : Nat × Nat :=
  (List.range steps).foldl (fun p _ => (p.2, (2 * p.1 + 3 * p.2) % 5)) (1, 0)

/-- The offset assigned by the 24-step rho walk, FIPS 202 Algorithm 2. -/
def rhoOffset (x y : Fin 5) : Nat :=
  (List.range 24).foldl (fun offset t =>
    if rhoPosition t = (x.val, y.val) then ((t + 1) * (t + 2) / 2) % 64 else offset) 0

/-- Rho, FIPS 202 Algorithm 2: it rotates each lane by its offset. -/
def rho (a : State) : State := fun x y z =>
  a x y (zcoord (z.val + 64 - rhoOffset x y))

/-- Pi, FIPS 202 Algorithm 3. -/
def pi (a : State) : State := fun x y z => a (xy (x.val + 3 * y.val)) x z

/-- Chi, FIPS 202 Algorithm 4. -/
def chi (a : State) : State := fun x y z =>
  Bool.xor (a x y z) ((!a (xy (x.val + 1)) y z) && a (xy (x.val + 2)) y z)

/-- The eight register bits used by FIPS 202 Algorithm 5. -/
abbrev Register := Fin 8 → Bool

/-- One register update, with the outgoing bit fed into positions 0, 4, 5 and 6. -/
def registerStep (r : Register) : Register := fun i =>
  let shifted := if i.val = 0 then false else r ⟨i.val - 1, by omega⟩
  if i.val = 0 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 then Bool.xor shifted (r 7)
  else shifted

/-- The FIPS 202 Algorithm 5 round-constant bit, with the index reduced modulo 255. -/
def rc (t : Nat) : Bool :=
  ((List.range (t % 255)).foldl (fun r _ => registerStep r)
    (fun i => i.val == 0)) 0

/-- A bit of the round constant, FIPS 202 Algorithm 6, steps 2 and 3. -/
def roundConstantBit (round : Nat) (z : Fin 64) : Bool :=
  (List.range 7).foldl (fun bit j =>
    if z.val = 2 ^ j - 1 then rc (j + 7 * round) else bit) false

/-- Iota, FIPS 202 Algorithm 6.

The function accepts any natural round index.

Keccak-f[1600] uses indices 0 through 23.
-/
def iota (round : Nat) (a : State) : State := fun x y z =>
  if x.val = 0 ∧ y.val = 0 then Bool.xor (a x y z) (roundConstantBit round z)
  else a x y z

/-- One round, FIPS 202 section 3.3. -/
def round (ir : Nat) (a : State) : State := iota ir (chi (pi (rho (theta a))))

/-- Keccak-f[1600], FIPS 202 section 3.4. -/
def permutation (a : State) : State :=
  (List.range 24).foldl (fun state ir => round ir state) a

/-- Bits of a byte in FIPS 202 Appendix B.1 order. -/
def byteBits (byte : UInt8) : List Bool :=
  (List.range 8).map (fun i => byte.toNat.testBit i)

/-- The bits of a byte string, in increasing byte and bit order. -/
def messageBits (msg : ByteArray) : List Bool := msg.data.toList.flatMap byteBits

/-- FIPS 202 Algorithm 9 at a positive rate of `rateBits` bits. -/
def padding (rateBits length : Nat) : List Bool :=
  true :: List.replicate ((rateBits - ((length + 2) % rateBits)) % rateBits) false ++ [true]

/-- The bits of a message followed by pad10*1 at a rate of `rateBits` bits. -/
def padded (rateBits : Nat) (msg : ByteArray) : List Bool :=
  let bits := messageBits msg
  bits ++ padding rateBits bits.length

/-- FIPS 202 section 3.1.2 linear state index. -/
def index (x y : Fin 5) (z : Fin 64) : Nat := 64 * (x.val + 5 * y.val) + z.val

/-- Each padded message has a whole number of rate-sized blocks, at any positive bit rate. -/
theorem padded_size_multiple {rateBits : Nat} (hr : 0 < rateBits) (msg : ByteArray) :
    (padded rateBits msg).length % rateBits = 0 := by
  simp only [padded, List.length_append, padding, List.length_cons,
    List.length_replicate, List.length_nil]
  let n := (messageBits msg).length + 2
  have hmod : n % rateBits < rateBits := Nat.mod_lt _ hr
  have hdiv := Nat.div_add_mod n rateBits
  by_cases h0 : n % rateBits = 0
  · have hlen : (messageBits msg).length +
        ((rateBits - n % rateBits) % rateBits + 1 + (0 + 1)) = rateBits * (n / rateBits) := by
      rw [h0, Nat.sub_zero, Nat.mod_self]
      omega
    rw [hlen, Nat.mul_mod_right]
  · have hsub : (rateBits - n % rateBits) % rateBits = rateBits - n % rateBits :=
      Nat.mod_eq_of_lt (by omega)
    have hlen : (messageBits msg).length +
        ((rateBits - n % rateBits) % rateBits + 1 + (0 + 1)) = rateBits * (n / rateBits + 1) := by
      rw [hsub, Nat.mul_add, Nat.mul_one]
      omega
    rw [hlen, Nat.mul_mod_right]

/-- A source block of `rateBits` bits. -/
abbrev Block (rateBits : Nat) := Vector Bool rateBits

/-- Extract complete block `i` from a message padded at `rateBits` bits. -/
def paddedBlock {rateBits : Nat} (hr : 0 < rateBits) (msg : ByteArray)
    (i : Fin ((padded rateBits msg).length / rateBits)) : Block rateBits :=
  Vector.ofFn fun j => (padded rateBits msg)[rateBits * i.val + j.val]'(by
    have hm := padded_size_multiple hr msg
    have hi := i.isLt
    have hj := j.isLt
    have hd := Nat.div_add_mod (padded rateBits msg).length rateBits
    have hmul : rateBits * (i.val + 1) ≤ rateBits * ((padded rateBits msg).length / rateBits) :=
      Nat.mul_le_mul_left rateBits hi
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega)

/-- XOR one `rateBits`-bit block into the state, leaving the capacity unchanged.

Bits at index 1600 and above are dropped, so the sponge requires a rate below 1600. -/
def absorb {rateBits : Nat} (a : State) (block : Block rateBits) : State := fun x y z =>
  let i := index x y z
  Bool.xor (a x y z) (if h : i < rateBits then block[i]'h else false)

/-- Absorb every complete block of a message padded at `rateBits` bits. -/
def absorbAll {rateBits : Nat} (hr : 0 < rateBits) (msg : ByteArray) : State :=
  (List.finRange ((padded rateBits msg).length / rateBits)).foldl
    (fun a i => permutation (absorb a (paddedBlock hr msg i)))
    (fun _ _ _ => false)

/-- The state bit at a linear index, modulo the state dimensions. -/
def stateBit (a : State) (i : Nat) : Bool :=
  a (xy ((i / 64) % 5)) (xy ((i / 64) / 5)) (zcoord i)

/-- Pack eight output bits into a byte, least significant bit first. -/
def outputByte (a : State) (i : Nat) : UInt8 :=
  UInt8.ofNat ((List.range 8).foldl (fun n j =>
    if stateBit a (8 * i + j) then n + 2 ^ j else n) 0)

/-- The first `outBytes` output bytes of a state, least significant bit first in each byte. -/
def squeezeBytes (outBytes : Nat) (a : State) : Vector UInt8 outBytes :=
  Vector.ofFn fun i => outputByte a i.val

/-- The sponge of FIPS 202 section 4, Algorithm 8, when `outBytes` fits in one rate block.

FIPS 202 section 4 requires a rate below the 1600-bit width, so the capacity is positive. -/
def sponge {rateBits outBytes : Nat} (hr : 0 < rateBits) (_hb : rateBits < 1600)
    (_hout : 8 * outBytes ≤ rateBits) (msg : ByteArray) : Vector UInt8 outBytes :=
  squeezeBytes outBytes (absorbAll hr msg)

/-- Original Keccak-256, FIPS 202 sections 4 and 5.2, at the 1088-bit rate. -/
def keccak256 (msg : ByteArray) : Vector UInt8 32 :=
  sponge (rateBits := 1088) (by decide) (by decide) (by decide) msg

/-- Original Keccak-512, FIPS 202 sections 4 and 5.2, at the 576-bit rate. -/
def keccak512 (msg : ByteArray) : Vector UInt8 64 :=
  sponge (rateBits := 576) (by decide) (by decide) (by decide) msg


open JoltSpec

/-! ## Bit coordinates -/

/-- A lane state viewed at the bit coordinates of FIPS 202 §3.1.2. -/
def ofLanes (a : Keccak.State) : State := fun x y z => (a.lane x y).toBitVec.getLsbD z.val

/-- The bit view of a state built lane by lane reads the bits of those lanes. -/
theorem ofLanes_ofLanes (f : Fin 5 → Fin 5 → UInt64) :
    ofLanes (Keccak.State.ofLanes f) = fun x y z => (f x y).toBitVec.getLsbD z.val := by
  funext x y z
  simp only [ofLanes, Keccak.lane_ofLanes]

/-- Flattening a coordinate and reading it recovers that coordinate. -/
theorem stateBit_index (a : State) (x y : Fin 5) (z : Fin 64) :
    stateBit a (index x y z) = a x y z := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  unfold stateBit index xy zcoord
  congr 1 <;> apply Fin.ext <;> simp only <;> omega

/-- The `Fin 5` sums of the lane formulas are the wrapped sums of the bit model. -/
private theorem coordinates :
    (∀ x y : Fin 5, x + 3 * y = xy (x.val + 3 * y.val)) ∧
    (∀ x : Fin 5, x - 1 = xy (x.val + 4)) ∧ (∀ x : Fin 5, x + 1 = xy (x.val + 1)) ∧
    (∀ x : Fin 5, x + 2 = xy (x.val + 2)) := by
  decide

/-! ## The step mappings -/

/-- Pi agrees with the lane implementation at every state bit. -/
theorem pi_ofLanes (a : Keccak.State) : ofLanes (Keccak.pi a) = pi (ofLanes a) := by
  rw [Keccak.pi_eq, ofLanes_ofLanes]
  funext x y z
  simp only [pi, ofLanes, coordinates.1]

/-- The rho walk of the model gives the offset of the lane table at every lane. -/
theorem rhoOffset_eq : ∀ x y : Fin 5,
    rhoOffset x y = (Keccak.RHO[x.val + 5 * y.val]'(by simp only [Keccak.LANES]; omega)).toNat := by
  decide +kernel

/-- Every offset of the rho walk is below the lane width. -/
theorem rhoOffset_lt : ∀ x y : Fin 5, rhoOffset x y < 64 := by
  decide +kernel

/-- Rho agrees with the lane implementation at every state bit. -/
theorem rho_ofLanes (a : Keccak.State) : ofLanes (Keccak.rho a) = rho (ofLanes a) := by
  rw [Keccak.rho_eq, ofLanes_ofLanes]
  funext x y z
  have offset := rhoOffset_eq x y
  have bound := rhoOffset_lt x y
  simp only [rho, ofLanes, zcoord]
  rw [Keccak.getLsbD_rotl _ _ (by omega) _ z.isLt, ← offset, Nat.mod_eq_of_lt bound]

/-- A bit of a lane column parity is the column parity of the model. -/
private theorem column_bit (a : Keccak.State) (x : Fin 5) (z : Fin 64) :
    (a.column x).toBitVec.getLsbD z.val = column (ofLanes a) x z := by
  simp [Keccak.State.column, column, ofLanes, UInt64.toBitVec_xor]

/-- Theta agrees with the lane implementation at every state bit. -/
theorem theta_ofLanes (a : Keccak.State) : ofLanes (Keccak.theta a) = theta (ofLanes a) := by
  rw [Keccak.theta_eq, ofLanes_ofLanes]
  funext x y z
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  rw [Keccak.getLsbD_rotl _ _ (by decide) _ z.isLt, column_bit, coordinates.2.1]
  -- The rotation by one reads bit `z - 1`, which is bit `z + 63` mod 64.
  have shift : (z.val + 64 - (1 : UInt64).toNat % 64) % 64 = (z.val + 63) % 64 := by
    simp only [UInt64.reduceToNat]
    omega
  rw [shift, coordinates.2.2.1]
  have col := column_bit a (xy (x.val + 1)) ⟨(z.val + 63) % 64, Nat.mod_lt _ (by decide)⟩
  rw [col]
  rfl

/-- Chi agrees with the lane implementation at every state bit. -/
theorem chi_ofLanes (a : Keccak.State) : ofLanes (Keccak.chi a) = chi (ofLanes a) := by
  rw [Keccak.chi_eq, ofLanes_ofLanes]
  funext x y z
  simp only [chi, ofLanes, coordinates.2.2.1, coordinates.2.2.2,
    UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, z.isLt, decide_true,
    Bool.true_and]

/-- Every round-constant bit of the model is the bit of the lane table. -/
theorem roundConstantBit_eq : ∀ (ir : Fin Keccak.ROUNDS) (z : Fin 64),
    roundConstantBit ir.val z = (Keccak.RC[ir]).toBitVec.getLsbD z.val := by
  decide +kernel

/-- Iota agrees with the lane implementation at every state bit. -/
theorem iota_ofLanes (a : Keccak.State) (ir : Fin Keccak.ROUNDS) :
    ofLanes (Keccak.iota ir a) = iota ir.val (ofLanes a) := by
  rw [Keccak.iota_eq, ofLanes_ofLanes]
  funext x y z
  -- Lane `(0, 0)` is the one whose coordinates are both zero.
  have zero : (x = 0 ∧ y = 0) ↔ (x.val = 0 ∧ y.val = 0) := by
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨hx, hy⟩
      exact ⟨Fin.ext hx, Fin.ext hy⟩
  by_cases h : x.val = 0 ∧ y.val = 0
  · obtain ⟨hx, hy⟩ := zero.mpr h
    subst hx hy
    simp [iota, ofLanes, roundConstantBit_eq]
  · have h' : ¬ (x = 0 ∧ y = 0) := fun e => h (zero.mp e)
    simp only [h', ite_false, iota, h, ofLanes]

/-! ## The permutation -/

/-- One round of the model agrees with one lane round. -/
theorem round_ofLanes (a : Keccak.State) (ir : Fin Keccak.ROUNDS) :
    ofLanes (Keccak.round ir a) = round ir.val (ofLanes a) := by
  simp only [Keccak.round, round, iota_ofLanes, chi_ofLanes, pi_ofLanes, rho_ofLanes,
    theta_ofLanes]

/-- The lane rounds from `i` to 23 agree with the model rounds from `i` to 23. -/
theorem roundsFrom_ofLanes (n i : Nat) (h : i + n = 24) (a : Keccak.State) :
    ofLanes (Keccak.keccakF.roundsFrom i a) =
      (List.range' i n).foldl (fun s ir => round ir s) (ofLanes a) := by
  induction n generalizing i a with
  | zero =>
    -- At round 24 no round is left.
    rw [Keccak.keccakF.roundsFrom, dite_eq_right (by simp only [Keccak.ROUNDS]; omega)]
    rfl
  | succ n ih =>
    -- Run round `i`, then the rounds after it.
    have hi : i < Keccak.ROUNDS := by simp only [Keccak.ROUNDS]; omega
    rw [Keccak.keccakF.roundsFrom, dite_eq_left hi, ih (i + 1) (by omega), round_ofLanes,
      List.range'_succ, List.foldl_cons]

/-- Keccak-f[1600] on lanes agrees with the 24 rounds of the model on every state. -/
theorem permutation_ofLanes (a : Keccak.State) :
    ofLanes (Keccak.keccakF a) = permutation (ofLanes a) := by
  rw [Keccak.keccakF, roundsFrom_ofLanes 24 0 rfl, permutation, List.range_eq_range']

/-! ## Packing bits into lanes -/

/-- Pack the bits of each lane coordinate into its 64-bit lane, bit `z` in bit `z`. -/
def toLanes (a : State) : Keccak.State :=
  Keccak.State.ofLanes fun x y => UInt64.ofBitVec ((BitVec.ofBoolListLE
    (List.ofFn fun z : Fin 64 => a x y z)).cast (by simp))

/-- Each bit of a packed lane is the bit at the same coordinate. -/
theorem toLanes_bit (a : State) (x y : Fin 5) (z : Fin 64) :
    ((toLanes a).lane x y).toBitVec.getLsbD z.val = a x y z := by
  simp only [toLanes, Keccak.lane_ofLanes, UInt64.toBitVec_ofBitVec, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some, List.getElem_ofFn]

/-- Packing a bit state and reading it back gives the same bit state. -/
theorem ofLanes_toLanes (a : State) : ofLanes (toLanes a) = a := by
  funext x y z
  exact toLanes_bit a x y z

/-- Reading a lane state and packing it back gives the same lane state. -/
theorem toLanes_ofLanes (a : Keccak.State) : toLanes (ofLanes a) = a := by
  apply Keccak.State.ext_lane
  intro x y
  apply Keccak.lane_ext
  intro z hz
  exact toLanes_bit (ofLanes a) x y ⟨z, hz⟩

/-- The model permutation, packed into lanes, is Keccak-f[1600] on the packed state. -/
theorem toLanes_permutation (a : State) :
    toLanes (permutation a) = Keccak.keccakF (toLanes a) := by
  have h := congrArg toLanes (permutation_ofLanes (toLanes a))
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm

end JoltSpec.KeccakBits
