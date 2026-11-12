/-!
# SHA-256 compression: the specification

This file is the specification of Jolt's `SHA256` and `SHA256_INIT` inlines.
`SHA256` computes `Spec.compression block state` on a given state, and `SHA256_INIT` computes
`Spec.compression block Spec.initial`.

## Provenance

The definitions are copied from EthLib.

- Repository: `ethereum/EthLib` (<https://github.com/ethereum/EthLib>)
- Commit: `5310b3ec007b05a2bfe33b01125392b07df5f636`
- Licence: CC0-1.0
- Source files:
  - `EthLib/Cryptography/Hash/Sha256.lean`: `K`, `IV`;
  - `EthLib/Cryptography/Proofs/Hash/Sha256.lean`: the whole `Spec` namespace, the
    definitions `smallPrime`, `smallPrimes`, `wholeSquareRoot`, `wholeCubeRoot`,
    `squareRootFraction` and `cubeRootFraction`, and the theorems `IV_from_primes` and
    `K_from_primes`, which derive `IV` and `K` from the primes.

Each copied declaration, with its docstring, is unchanged except for these edits:

- the namespace `EthLib.Cryptography.Hash.Sha256` is renamed `JoltSpec.Sha256`;
- the module-system markers (`module`, `public import`, `@[expose] public section`) are dropped,
  because jolt-qed does not use the module system;
- the section headers between declarations are adapted to this file.

`scripts/check-ethlib-copies.sh` checks every declaration of this file against EthLib.

`IV_from_primes` and `K_from_primes` are proved, as in EthLib, by `decide +kernel`. `AGENTS.md`
allows it when the kernel check is fast, and each check here takes under a second
(`reports/2026-11-11-inline-known-answer-hashes.md` lists the times).

## What was left out

- EthLib's executable `UInt32` implementation (`State`, `round`, `compress`, `hash`, ...) and its
  proofs (`compress_toState`, `hash_eq_spec`, ...): Jolt's inline rows are specified by the model
  `Spec.compression` directly, so the executable layer is not needed.
-/

namespace JoltSpec.Sha256

/-! ## Constants -/

/--
The round constants K₀ to K₆₃, FIPS 180-4 §4.2.2.

Each is the first 32 bits of the fractional part of the cube root of one of the first 64 primes.
-/
def K : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/--
The initial hash value H⁽⁰⁾, FIPS 180-4 §5.3.3.

Each is the first 32 bits of the fractional part of the square root of one of the first 8 primes.
-/
def IV : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]


namespace Spec

/-- A word whose arithmetic is modulo 2^32, FIPS 180-4 §3.2. -/
abbrev Word := BitVec 32

/-- The eight working variables a to h, FIPS 180-4 §6.2.2. -/
structure State where
  /-- The working variable `a`. -/
  a : Word
  /-- The working variable `b`. -/
  b : Word
  /-- The working variable `c`. -/
  c : Word
  /-- The working variable `d`. -/
  d : Word
  /-- The working variable `e`. -/
  e : Word
  /-- The working variable `f`. -/
  f : Word
  /-- The working variable `g`. -/
  g : Word
  /-- The working variable `h`. -/
  h : Word
  deriving DecidableEq

/-- σ0 of FIPS 180-4 §4.1.2 (4.6). -/
def small0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- σ1 of FIPS 180-4 §4.1.2 (4.7). -/
def small1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- Σ0 of FIPS 180-4 §4.1.2 (4.4). -/
def large0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- Σ1 of FIPS 180-4 §4.1.2 (4.5). -/
def large1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- One round of FIPS 180-4 §6.2.2, step 3. -/
def step (s : State) (constant word : Word) : State :=
  let choose := (s.e &&& s.f) ^^^ ((~~~s.e) &&& s.g)
  let majority := (s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c)
  let t1 := s.h + large1 s.e + choose + constant + word
  let t2 := large0 s.a + majority
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- The message schedule of FIPS 180-4 §6.2.2, step 1, as a recurrence. -/
def messageWord (input : Vector Word 16) (t : Nat) : Word :=
  if early : t < 16 then input[t]
  else
    messageWord input (t - 16) + small0 (messageWord input (t - 15)) +
      messageWord input (t - 7) + small1 (messageWord input (t - 2))
termination_by t

/-- Four bytes read as one big-endian word, FIPS 180-4 §3.1. -/
def inputWord (block : ByteArray) (start : Nat) : Word :=
  (BitVec.ofNat 32 block[start]!.toNat) <<< 24 |||
    (BitVec.ofNat 32 block[start + 1]!.toNat) <<< 16 |||
    (BitVec.ofNat 32 block[start + 2]!.toNat) <<< 8 |||
    BitVec.ofNat 32 block[start + 3]!.toNat

/-- The sixteen words of the block starting at a byte offset, FIPS 180-4 §5.2.1. -/
def inputWords (block : ByteArray) (start : Nat) : Vector Word 16 :=
  Vector.ofFn fun t => inputWord block (start + 4 * t.val)

/-- The first rounds of one block, FIPS 180-4 §6.2.2, steps 2 and 3. -/
def rounds (input : Vector Word 16) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => step (rounds input initial n) (K[n]!).toBitVec (messageWord input n)

/-- One block: 64 rounds, then the intermediate hash value added in, FIPS 180-4 §6.2.2, step 4. -/
def compression (input : Vector Word 16) (initial : State) : State :=
  let w := rounds input initial 64
  ⟨initial.a + w.a, initial.b + w.b, initial.c + w.c, initial.d + w.d,
    initial.e + w.e, initial.f + w.f, initial.g + w.g, initial.h + w.h⟩

/-- The initial hash value, FIPS 180-4 §5.3.3. -/
def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- The number of zero bytes after the `0x80` byte, FIPS 180-4 §5.1.1. -/
def zeroCount (size : Nat) : Nat := (119 - size % 64) % 64

/--
The padded message, FIPS 180-4 §5.1.1.

It is the message, `0x80`, zeros, and the bit length in eight big-endian bytes.
-/
def padded (message : ByteArray) : ByteArray :=
  ⟨message.data ++ #[0x80] ++ Array.replicate (zeroCount message.size) 0 ++
    Array.ofFn fun i : Fin 8 => UInt8.ofNat ((message.size * 8 / 2 ^ (56 - 8 * i.val)) % 256)⟩

/-- The intermediate hash value after the first blocks of a padded message, FIPS 180-4 §6.2.2. -/
def blocks (message : ByteArray) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => compression (inputWords message (64 * n)) (blocks message initial n)

/-- The eight words in digest order. -/
def State.words (s : State) : Vector Word 8 := #v[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

/-- The digest: each word as four big-endian bytes, FIPS 180-4 §6.2.2. -/
def digest (s : State) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 32 =>
    UInt8.ofNat ((s.words[i.val / 4]'(by omega)).toNat / 2 ^ (24 - 8 * (i.val % 4)) % 256)⟩

/-- SHA-256, FIPS 180-4 §6.2. -/
def hash (message : ByteArray) : ByteArray :=
  let input := padded message
  digest (blocks input initial (input.size / 64))

end Spec

/-! ## Deriving the constants

The test module checks with these definitions that `IV` and `K` are the ones FIPS 180-4 derives.
-/

/--
Whether a number below 324 is prime.

Trial division stops at 17, since every composite below 18² has a divisor that small.
-/
def smallPrime (candidate : Nat) : Bool :=
  2 ≤ candidate && (List.range 18).all fun divisor =>
    divisor < 2 || divisor * divisor > candidate || candidate % divisor != 0

/-- The primes below a bound, in order, for bounds up to 324. -/
def smallPrimes (bound : Nat) : List Nat := (List.range bound).filter smallPrime

/-- The largest number below 18 whose square is at most the given one. -/
def wholeSquareRoot (value : Nat) : Nat :=
  (List.range 18).foldl (fun best candidate => if candidate * candidate ≤ value then candidate else best) 0

/-- The largest number below 8 whose cube is at most the given one. -/
def wholeCubeRoot (value : Nat) : Nat :=
  (List.range 8).foldl (fun best candidate => if candidate ^ 3 ≤ value then candidate else best) 0

/--
Whether a word is the first 32 fractional bits of the square root of a prime.

With `root = ⌊√prime⌋ · 2^32 + word`, it is exactly when `root² ≤ prime · 2^64 < (root + 1)²`.
-/
def squareRootFraction (prime word : Nat) : Bool :=
  let root := wholeSquareRoot prime * 2 ^ 32 + word
  root ^ 2 ≤ prime * 2 ^ 64 && prime * 2 ^ 64 < (root + 1) ^ 2

/--
Whether a word is the first 32 fractional bits of the cube root of a prime.

With `root = ⌊∛prime⌋ · 2^32 + word`, it is exactly when `root³ ≤ prime · 2^96 < (root + 1)³`.
-/
def cubeRootFraction (prime word : Nat) : Bool :=
  let root := wholeCubeRoot prime * 2 ^ 32 + word
  root ^ 3 ≤ prime * 2 ^ 96 && prime * 2 ^ 96 < (root + 1) ^ 3

/--
The initial hash value is the one that FIPS 180-4 §5.3.3 derives.

It comes from the square roots of the first 8 primes.

So no initial word is taken on trust.
-/
theorem IV_from_primes :
    (smallPrimes 20).length = 8 ∧ IV.toList.length = 8 ∧
      ((smallPrimes 20).zip (IV.toList.map UInt32.toNat)).all
        (fun pair => squareRootFraction pair.1 pair.2) = true := by
  decide +kernel

/--
The round constants are the ones that FIPS 180-4 §4.2.2 derives.

They come from the cube roots of the first 64 primes.

So no round constant is taken on trust.
-/
theorem K_from_primes :
    (smallPrimes 312).length = 64 ∧ K.toList.length = 64 ∧
      ((smallPrimes 312).zip (K.toList.map UInt32.toNat)).all
        (fun pair => cubeRootFraction pair.1 pair.2) = true := by
  decide +kernel

end JoltSpec.Sha256
