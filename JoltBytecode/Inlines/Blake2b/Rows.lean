import JoltBytecode.Inlines.Generated.Blake2
import JoltBytecode.Inlines.Blake2b.Spec

/-!
# The rows of `BLAKE2`, in the shape of the compression function

Jolt's `BLAKE2` inline has 1,067 rows (`Generated.blake2RowsAutoList`). They fall into six
blocks, which this module names:

| Rows | Block | What the rows do |
|---|---|---|
| 0–25 | `loadRows` | load the state `h` (8 words at `rs1`) into `vr80..87`, the message `m` (16 words at `rs2`) into `vr64..79`, the counter at `rs2 + 128` into `vr60` and the final-block flag at `rs2 + 136` into `vr62` |
| 26–42 | `initRows` | set the work vector `v` in `vr48..63`: `h`, then the IV, with the counter XORed into word 12 and `0 - flag` into word 14 |
| 43–1002 | `(roundsMixes 12).flatMap mixRows` | the 96 calls of the mixing function G of the 12 rounds, 10 rows each |
| 1003–1018 | `finalRows` | `h[i] := h[i] ^ v[i] ^ v[i + 8]` in `vr80..87` |
| 1019–1026 | `storeRows` | store `vr80..87` to `rs1` |
| 1027–1066 | `resetRows` | reset `vr48..87` to zero |

`Blake2b.Shape` proves that the generated rows are these blocks
(`blake2RowsAutoList_eq`).

Register `vr(48 + i)` holds word `i` of the work vector, `vr(64 + j)` message word `j`, and
`vr(80 + i)` state word `i`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines.Blake2b

/-! ## Registers -/

/-- The register of work-vector word `i`: `vr(48 + i)`.
Example: `wReg 12 = vr60`. -/
abbrev wReg (i : Fin 16) : VReg := BitVec.ofNat 7 (48 + i.val)

/-- The register of message word `j`: `vr(64 + j)`.
Example: `mReg 15 = vr79`. -/
abbrev mReg (j : Fin 16) : VReg := BitVec.ofNat 7 (64 + j.val)

/-- The register of state word `i`: `vr(80 + i)`.
Example: `hReg 7 = vr87`. -/
abbrev hReg (i : Fin 8) : VReg := BitVec.ofNat 7 (80 + i.val)

/-! ## One call of G -/

/-- One call of the mixing function G: the four work-vector words `a`, `b`, `c`, `d` it mixes
and the indices `x`, `y` of the two message words it adds.
Example: the first call of round 1 is `⟨0, 4, 8, 12, 14, 10⟩`, because row 1 of the message
schedule starts `14, 10`. -/
structure Mix where
  a : Fin 16
  b : Fin 16
  c : Fin 16
  d : Fin 16
  x : Fin 16
  y : Fin 16
  deriving DecidableEq

/-- The first seven rows of a call of G: `a := a + b + m[x]`, `d := (d ^ a).rotateRight 32`,
`c := c + d`, `b := (b ^ c).rotateRight 24`, `a := a + b + m[y]`.
Example: for `⟨0, 4, 8, 12, 0, 1⟩` the first row is `ADD vr48, vr48, vr52`. -/
def mixLo (M : Mix) : List Instr :=
  [.ADD (.vreg (wReg M.a)) (.vreg (wReg M.a)) (.vreg (wReg M.b)),
   .ADD (.vreg (wReg M.a)) (.vreg (wReg M.a)) (.vreg (mReg M.x)),
   .VirtualXORROT32 (.vreg (wReg M.d)) (.vreg (wReg M.d)) (.vreg (wReg M.a)),
   .ADD (.vreg (wReg M.c)) (.vreg (wReg M.c)) (.vreg (wReg M.d)),
   .VirtualXORROT24 (.vreg (wReg M.b)) (.vreg (wReg M.b)) (.vreg (wReg M.c)),
   .ADD (.vreg (wReg M.a)) (.vreg (wReg M.a)) (.vreg (wReg M.b)),
   .ADD (.vreg (wReg M.a)) (.vreg (wReg M.a)) (.vreg (mReg M.y))]

/-- The last three rows of a call of G: `d := (d ^ a).rotateRight 16`, `c := c + d`,
`b := (b ^ c).rotateRight 63`.
Example: for `⟨0, 4, 8, 12, 0, 1⟩` the last row is `VirtualXORROT63 vr52, vr52, vr56`. -/
def mixHi (M : Mix) : List Instr :=
  [.VirtualXORROT16 (.vreg (wReg M.d)) (.vreg (wReg M.d)) (.vreg (wReg M.a)),
   .ADD (.vreg (wReg M.c)) (.vreg (wReg M.c)) (.vreg (wReg M.d)),
   .VirtualXORROT63 (.vreg (wReg M.b)) (.vreg (wReg M.b)) (.vreg (wReg M.c))]

/-- The ten rows of a call of G.
Example: `(mixRows ⟨0, 4, 8, 12, 0, 1⟩).length = 10`. -/
def mixRows (M : Mix) : List Instr := mixLo M ++ mixHi M

/-! ## Rounds -/

/-- The eight calls of G in a round whose message schedule row is `s`: the four columns,
then the four diagonals, as in `JoltSpec.Blake2b.Spec.round`.
Example: for row 0 of the schedule, the fifth call is `⟨0, 5, 10, 15, 8, 9⟩`. -/
def roundMixes (s : Vector (Fin 16) 16) : List Mix :=
  [⟨0, 4,  8, 12, s[0],  s[1]⟩,  ⟨1, 5,  9, 13, s[2],  s[3]⟩,
   ⟨2, 6, 10, 14, s[4],  s[5]⟩,  ⟨3, 7, 11, 15, s[6],  s[7]⟩,
   ⟨0, 5, 10, 15, s[8],  s[9]⟩,  ⟨1, 6, 11, 12, s[10], s[11]⟩,
   ⟨2, 7,  8, 13, s[12], s[13]⟩, ⟨3, 4,  9, 14, s[14], s[15]⟩]

/-- The calls of G in rounds `0` to `n - 1`, in order; round `i` uses schedule row `i mod 10`.
Example: `(roundsMixes 12).length = 96`. -/
def roundsMixes : Nat → List Mix
  | 0 => []
  | n + 1 => roundsMixes n ++ roundMixes JoltSpec.Blake2b.SIGMA[n % 10]

/-! ## The other blocks -/

/-- Rows 0–25: load `h` from `rs1` into `vr80..87`, `m` from `rs2` into `vr64..79`, the counter
from `rs2 + 128` into `vr60` and the final-block flag from `rs2 + 136` into `vr62`.
Example: row 8 is `LD vr64, 0(rs2)`. -/
def loadRows (rs1 rs2 : regidx) : List Instr :=
  ((List.range 8).map fun i =>
      .LD .normal (.vreg (BitVec.ofNat 7 (80 + i))) (.xreg rs1) (BitVec.ofNat 64 (8 * i))) ++
  ((List.range 16).map fun j =>
      .LD .normal (.vreg (BitVec.ofNat 7 (64 + j))) (.xreg rs2) (BitVec.ofNat 64 (8 * j))) ++
  [.LD .normal (.vreg (BitVec.ofNat 7 60)) (.xreg rs2) 128,
   .LD .normal (.vreg (BitVec.ofNat 7 62)) (.xreg rs2) 136]

/-- Rows 26–42: the work vector. Words 0–7 copy `h` (`XORI` with 0), words 8–11, 13 and 15 are
IV words, word 12 is the counter XOR `IV[4]`, and word 14 is `(0 - flag)` XOR `IV[6]`.
Example: row 34 is `LUI vr56, 0x6a09e667f3bcc908`, the first IV word. -/
def initRows : List Instr :=
  ((List.range 8).map fun i =>
      .XORI (.vreg (BitVec.ofNat 7 (48 + i))) (.vreg (BitVec.ofNat 7 (80 + i))) 0) ++
  [.LUI (.vreg (BitVec.ofNat 7 56)) 0x6a09e667f3bcc908,
   .LUI (.vreg (BitVec.ofNat 7 57)) 0xbb67ae8584caa73b,
   .LUI (.vreg (BitVec.ofNat 7 58)) 0x3c6ef372fe94f82b,
   .LUI (.vreg (BitVec.ofNat 7 59)) 0xa54ff53a5f1d36f1,
   .LUI (.vreg (BitVec.ofNat 7 61)) 0x9b05688c2b3e6c1f,
   .LUI (.vreg (BitVec.ofNat 7 63)) 0x5be0cd19137e2179,
   .XORI (.vreg (BitVec.ofNat 7 60)) (.vreg (BitVec.ofNat 7 60)) 0x510e527fade682d1,
   .SUB (.vreg (BitVec.ofNat 7 62)) (.xreg (regidx.Regidx 0)) (.vreg (BitVec.ofNat 7 62)),
   .XORI (.vreg (BitVec.ofNat 7 62)) (.vreg (BitVec.ofNat 7 62)) 0x1f83d9abfb41bd6b]

/-- Rows 1003–1018: `v[i] := v[i] ^ v[i + 8]`, then `h[i] := h[i] ^ v[i]`, for each `i`.
Example: rows 1003 and 1004 are `XOR vr48, vr48, vr56` and `XOR vr80, vr80, vr48`. -/
def finalRows : List Instr :=
  (List.range 8).flatMap fun i =>
    [.XOR (.vreg (BitVec.ofNat 7 (48 + i))) (.vreg (BitVec.ofNat 7 (48 + i)))
       (.vreg (BitVec.ofNat 7 (56 + i))),
     .XOR (.vreg (BitVec.ofNat 7 (80 + i))) (.vreg (BitVec.ofNat 7 (80 + i)))
       (.vreg (BitVec.ofNat 7 (48 + i)))]

/-- Rows 1019–1026: store `vr80..87` to `rs1`.
Example: row 1020 is `SD vr81, 8(rs1)`. -/
def storeRows (rs1 : regidx) : List Instr :=
  (List.range 8).map fun i =>
    .SD (.xreg rs1) (.vreg (BitVec.ofNat 7 (80 + i))) (BitVec.ofNat 64 (8 * i))

/-- Rows 1027–1066: reset the pool registers `vr48..87` to zero.
Example: row 1027 is `ADDI vr48, x0, 0`. -/
def resetRows : List Instr :=
  (List.range 40).map fun k =>
    .ADDI (.vreg (BitVec.ofNat 7 (48 + k))) (.xreg (regidx.Regidx 0)) 0

end JoltISA.Inlines.Blake2b
