import JoltBytecode.Inlines.Generated.Sha256
import JoltBytecode.Inlines.Generated.Sha256Init
import JoltBytecode.Inlines.Sha256.Spec

/-!
# The rows of `SHA256` and `SHA256_INIT`, in the shape of the compression function

Jolt builds both SHA-256 inlines with one builder (`jolt-inlines/sha2/src/sequence_builder.rs`):
`SHA256` compresses a block into a state read from memory, and `SHA256_INIT` compresses a block
into the initial hash value, which it folds into the rows as constants. This module restates
that builder in Lean, block by block, so that the proofs can follow the rounds.

| Block | `SHA256` rows | `SHA256_INIT` rows | What the rows do |
|---|---|---|---|
| `ivLoadRows` | 0–7 | none | load the state (4 doublewords at `rs1`, two words each) into `vr72..79` |
| `msgLoadRows` | 8–31 | 0–23 | load the block (8 doublewords at `rs2`), byte-swap each word, split into `vr56..71` |
| `allRounds 64` | 32–1839 | 24–1811 | the 64 rounds, 20 rows each before round 16 and 31 rows after; in `SHA256_INIT`, rounds 0–3 fold constants and have 3, 18, 20 and 19 rows |
| `finalRows` | 1840–1847 | 1812–1819 | add the old state into the working variables `vr48..55` |
| `storeRows` | 1848–1863 | 1820–1835 | pack two words per doubleword and store 4 doublewords to `rs1` |
| `resetRows` | 1864–1899 | 1836–1863 | reset the pool registers to zero |

`Sha256.Shape` proves that the generated rows are these blocks.

## Registers

The working variables `a..h` rotate through `vr48..55`: at round `n`, variable `c` (`a = 0`)
lives in `sReg n c = vr(48 + (c - n) mod 8)`. Message word `j` of the 16-word window lives in
`mReg j = vr(56 + j mod 16)`. `SHA256` keeps the old state in `vr72..79` (`ivReg`), and until
round 4 the working variables that no round has computed yet are read there. `SHA256_INIT`
reads those variables as constants instead. Each round uses four temporaries: `vr80..83` for
`SHA256` and `vr72..75` for `SHA256_INIT`.

## Values

Every 32-bit word lives in the low half of a 64-bit register. Rust's builder passes values as
`Value::Reg` or `Value::Imm` and folds an operation on two constants into a constant; `Val`
and `bin` do the same here, so that one definition covers both inlines.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines.Sha256

/-! ## Registers -/

/-- Virtual register number `n`.
Example: `vr 48` is the register of `a` before round 0. -/
abbrev vr (n : Nat) : VReg := BitVec.ofNat 7 n

/-- The register of working variable `c` (`a = 0`, ..., `h = 7`) at round `n`, once a round
has computed it: `vr(48 + (c - n) mod 8)`.
Example: `sReg 1 0 = vr 55`: the new `a` of round 0 goes to `vr55`. -/
abbrev sReg (n c : Nat) : VReg := vr (48 + (c + 8 - n % 8) % 8)

/-- The register of message window word `j`: `vr(56 + j mod 16)`.
Example: `mReg 17 = vr 57`. -/
abbrev mReg (j : Nat) : VReg := vr (56 + j % 16)

/-- The register that holds old state word `c` in `SHA256`: `vr(72 + c)`.
Example: `ivReg 7 = vr 79`, the old `h`. -/
abbrev ivReg (c : Nat) : VReg := vr (72 + c)

/-- The four temporaries of a round: `t1`, `t2`, and the scratch registers `ss`, `ss2`.
`SHA256` allocates them after the old state, `SHA256_INIT` after the message.
Example: `tReg false 0 = vr 80` and `tReg true 0 = vr 72`. -/
abbrev tReg (initial : Bool) (k : Nat) : VReg := vr ((if initial then 72 else 80) + k)

/-! ## Values and folded operations -/

/-- An operand of the builder: a register or a constant.
Example: before round 0 of `SHA256_INIT`, `a` is `.imm 0x6a09e667`. -/
inductive Val where
  | reg (r : VReg)
  | imm (v : BitVec 64)

/-- A binary operation as Rust's `bin` emits it: two registers give an R-row, a register and a
constant give an I-row (the constant goes last, whichever side it came from), and two
constants fold into a constant with no row.
Example: `add (.imm 1) (.reg r) d = ([ADDI d r 1], .reg d)`. -/
def bin (rk : Dst → Src → Src → Instr) (ik : Dst → Src → BitVec 64 → Instr)
    (fold : BitVec 64 → BitVec 64 → BitVec 64) : Val → Val → VReg → List Instr × Val
  | .reg x, .reg y, d => ([rk (.vreg d) (.vreg x) (.vreg y)], .reg d)
  | .reg x, .imm i, d => ([ik (.vreg d) (.vreg x) i], .reg d)
  | .imm i, .reg y, d => ([ik (.vreg d) (.vreg y) i], .reg d)
  | .imm i, .imm j, _ => ([], .imm (fold i j))

/-- Addition: `ADD`, `ADDI`, or a folded 64-bit sum.
Example: `add (.imm 1) (.imm 2) d = ([], .imm 3)`. -/
def add : Val → Val → VReg → List Instr × Val := bin .ADD .ADDI (· + ·)

/-- Exclusive or: `XOR`, `XORI`, or a folded constant.
Example: `xor (.reg r) (.imm 0xffffffff) d = ([XORI d r 0xffffffff], .reg d)`. -/
def xor : Val → Val → VReg → List Instr × Val := bin .XOR .XORI (· ^^^ ·)

/-- Conjunction: `AND`, `ANDI`, or a folded constant.
Example: `and (.reg e) (.reg f) d = ([AND d e f], .reg d)`. -/
def and : Val → Val → VReg → List Instr × Val := bin .AND .ANDI (· &&& ·)

/-- The low word of a 64-bit constant.
Example: `w32 0x108909ae5 = 0x08909ae5`. -/
abbrev w32 (v : BitVec 64) : BitVec 32 := v.setWidth 32

/-- The bit mask `2^32 - 2^k` that Jolt's 32-bit rotations and shifts by `k` carry: the shift
amount is its number of trailing zeros.
Example: `wordMask 18 = 4294705152`. -/
def wordMask (k : Nat) : Nat := 2 ^ 32 - 2 ^ k

/-- The bit mask `2^64 - 2^32` of `VirtualSRLI` by 32.
Example: `srli32Mask = 18446744069414584320`. -/
def srli32Mask : Nat := 2 ^ 64 - 2 ^ 32

/-- Σ1 of a register in three rows into `rd`, with scratch `ss`: `ss := x ⋙ 18`,
`rd := (x ^ ss) ⋙ 19`, `rd := (x ^ rd) ⋙ 6`. Of a constant it is a constant.
Example: on `.reg vr52` the first row is `VirtualROTRIW ss, vr52, wordMask 18`. -/
def bigSigma1 (x : Val) (rd ss : VReg) : List Instr × Val :=
  match x with
  | .reg x =>
    ([.VirtualROTRIW (.vreg ss) (.vreg x) (wordMask 18),
      .VirtualXORROTW19 (.vreg rd) (.vreg x) (.vreg ss),
      .VirtualXORROTW6 (.vreg rd) (.vreg x) (.vreg rd)], .reg rd)
  | .imm v => ([], .imm ((JoltSpec.Sha256.Spec.large1 (w32 v)).setWidth 64))

/-- Σ0 of a register in three rows into `rd`, with scratch `ss`: `ss := x ⋙ 11`,
`rd := (x ^ ss) ⋙ 12`, `rd := (x ^ rd) ⋙ 22`. Of a constant it is a constant.
Example: on `.reg vr48` the second row is `VirtualXORROTW12 rd, vr48, ss`. -/
def bigSigma0 (x : Val) (rd ss : VReg) : List Instr × Val :=
  match x with
  | .reg x =>
    ([.VirtualROTRIW (.vreg ss) (.vreg x) (wordMask 11),
      .VirtualXORROTW12 (.vreg rd) (.vreg x) (.vreg ss),
      .VirtualXORROTW22 (.vreg rd) (.vreg x) (.vreg rd)], .reg rd)
  | .imm v => ([], .imm ((JoltSpec.Sha256.Spec.large0 (w32 v)).setWidth 64))

/-- `Ch(e, f, g) = (e & f) ^ (~e & g)` into `rd`, with scratch `ss`, computing `~e` as
`e ^ 0xffffffff`: the rows of `ch` when `e` or `g` is a constant.
Example: for `e = .reg vr51` and `g = .imm 0x9b05688c` the rows are `ANDI ss vr51 f`,
`XORI rd vr51 0xffffffff`, `ANDI rd rd 0x9b05688c`, `XOR rd ss rd`. -/
def chGen (e f g : Val) (rd ss : VReg) : List Instr × Val :=
  let ef := and e f ss
  let ne := xor e (.imm 0xffffffff) rd
  let neg := and ne.2 g rd
  let x := xor ef.2 neg.2 rd
  (ef.1 ++ ne.1 ++ neg.1 ++ x.1, x.2)

/-- `Ch(e, f, g) = (e & f) ^ (~e & g)` into `rd`, with scratch `ss`. When `e` and `g` are both
registers, `~e & g` is one `ANDN`; otherwise the rows are `chGen`.
Example: on registers the rows are `AND ss e f`, `ANDN rd g e`, `XOR rd ss rd`. -/
def ch (e f g : Val) (rd ss : VReg) : List Instr × Val :=
  match e, g with
  | .reg re, .reg rg =>
    let ef := and e f ss
    let x := xor ef.2 (.reg rd) rd
    (ef.1 ++ [.ANDN (.vreg rd) (.vreg rg) (.vreg re)] ++ x.1, x.2)
  | _, _ => chGen e f g rd ss

/-- `Maj(a, b, c)` as `(b & c) ^ (a & (b ^ c))` into `rd`, with scratch `ss`.
Example: on registers the rows are `AND ss b c`, `XOR rd b c`, `AND rd a rd`, `XOR rd ss rd`. -/
def maj (a b c : Val) (rd ss : VReg) : List Instr × Val :=
  let bc := and b c ss
  let bxc := xor b c rd
  let abxc := and a bxc.2 rd
  let x := xor bc.2 abxc.2 rd
  (bc.1 ++ bxc.1 ++ abxc.1 ++ x.1, x.2)

/-! ## Rounds -/

/-- The round constant `K[n]` as a 64-bit immediate.
Example: `kImm 0 = 0x428a2f98`. -/
def kImm (n : Nat) : BitVec 64 := (JoltSpec.Sha256.K[n]!).toBitVec.setWidth 64

/-- Word `c` of the initial hash value as a 64-bit immediate.
Example: `ivImm 0 = 0x6a09e667`. -/
def ivImm (c : Nat) : BitVec 64 := (JoltSpec.Sha256.IV[c]!).toBitVec.setWidth 64

/-- Where the old state word `c` is: the register `ivReg c` for `SHA256`, the constant
`ivImm c` for `SHA256_INIT`.
Example: `ivVal true 4 = .imm 0x510e527f`. -/
def ivVal (initial : Bool) (c : Nat) : Val :=
  if initial then .imm (ivImm c) else .reg (ivReg c)

/-- Working variable `c` at the start of round `n`. Round `n` has computed the variables `c`
with `c mod 4 < n`; the others are still old state words.
Example: `cur false 1 1 = .reg (ivReg 0)` (`b` of round 1 is the old `a`) and
`cur false 1 0 = .reg (vr 55)`. -/
def cur (initial : Bool) (n c : Nat) : Val :=
  if n < 4 ∧ n ≤ c % 4 then ivVal initial ((c + 8 - n) % 8) else .reg (sReg n c)

/-- The message schedule update of round `n ≥ 16`, with scratch registers `ss` and `ss2`:
`w[n] := w[n - 16] + σ0(w[n - 15]) + w[n - 7] + σ1(w[n - 2])`, in place in the window.
Example: for round 16 the fifth row is `ADD vr56, vr56, ss`. -/
def updateRows (n : Nat) (ss ss2 : VReg) : List Instr :=
  [.VirtualROTRIW (.vreg ss2) (.vreg (mReg (n + 1))) (wordMask 11),
   .VirtualXORROTW7 (.vreg ss) (.vreg (mReg (n + 1))) (.vreg ss2),
   .VirtualSRLIW (.vreg ss2) (.vreg (mReg (n + 1))) (wordMask 3),
   .XOR (.vreg ss) (.vreg ss) (.vreg ss2),
   .ADD (.vreg (mReg n)) (.vreg (mReg n)) (.vreg ss),
   .ADD (.vreg (mReg n)) (.vreg (mReg (n + 9))) (.vreg (mReg n)),
   .VirtualROTRIW (.vreg ss2) (.vreg (mReg (n + 14))) (wordMask 30),
   .VirtualXORROTW19 (.vreg ss) (.vreg (mReg (n + 14))) (.vreg ss2),
   .VirtualSRLIW (.vreg ss2) (.vreg (mReg (n + 14))) (wordMask 10),
   .XOR (.vreg ss) (.vreg ss) (.vreg ss2),
   .ADD (.vreg (mReg n)) (.vreg (mReg n)) (.vreg ss)]

/-- The pieces of `t1 = h + K[n] + Σ1(e) + Ch(e, f, g) + w[n]`, in row order: `h + K[n]`, Σ1,
the first sum, Ch, the second sum, the schedule update (from round 16), and the last sum. -/
def t1Parts (initial : Bool) (n : Nat) :
    (List Instr × Val) × (List Instr × Val) × (List Instr × Val) × (List Instr × Val) ×
      (List Instr × Val) × List Instr × (List Instr × Val) :=
  let t1 := tReg initial 0
  let ss := tReg initial 2
  let ss2 := tReg initial 3
  let hk := add (.imm (kImm n)) (cur initial n 7) t1
  let s1 := bigSigma1 (cur initial n 4) ss ss2
  let a1 := add hk.2 s1.2 t1
  let c := ch (cur initial n 4) (cur initial n 5) (cur initial n 6) ss ss2
  let a2 := add a1.2 c.2 t1
  let u := if 16 ≤ n then updateRows n ss ss2 else []
  let a3 := add a2.2 (.reg (mReg n)) t1
  (hk, s1, a1, c, a2, u, a3)

/-- The pieces of `t2 = Σ0(a) + Maj(a, b, c)`, in row order. -/
def t2Parts (initial : Bool) (n : Nat) :
    (List Instr × Val) × (List Instr × Val) × (List Instr × Val) :=
  let t2 := tReg initial 1
  let ss := tReg initial 2
  let ss2 := tReg initial 3
  let s0 := bigSigma0 (cur initial n 0) t2 ss
  let m := maj (cur initial n 0) (cur initial n 1) (cur initial n 2) ss ss2
  let t := add s0.2 m.2 t2
  (s0, m, t)

/-- The rows of round `n`: `t1`, then `t2`, then the new `a = t1 + t2` and the new
`e = d + t1`, written to the registers of `a` and `e` of round `n + 1`.
Example: `(roundRows false 0).length = 20` and `(roundRows false 16).length = 31`. -/
def roundRows (initial : Bool) (n : Nat) : List Instr :=
  let p := t1Parts initial n
  let q := t2Parts initial n
  let t1 := p.2.2.2.2.2.2.2
  let t2 := q.2.2.2
  p.1.1 ++ p.2.1.1 ++ p.2.2.1.1 ++ p.2.2.2.1.1 ++ p.2.2.2.2.1.1 ++ p.2.2.2.2.2.1 ++
    p.2.2.2.2.2.2.1 ++ q.1.1 ++ q.2.1.1 ++ q.2.2.1 ++
    (add t1 t2 (sReg (n + 1) 0)).1 ++ (add t1 (cur initial n 3) (sReg (n + 1) 4)).1

/-- The rows of rounds `0` to `n - 1`, in order.
Example: `allRounds false 1 = roundRows false 0`. -/
def allRounds (initial : Bool) : Nat → List Instr
  | 0 => []
  | n + 1 => allRounds initial n ++ roundRows initial n

/-! ## The other blocks -/

/-- `SHA256` rows 0–7: load the four state doublewords at `rs1`; the low word of doubleword `i`
stays in `vr(72 + 2i)` (with the high word above it) and the high word goes to `vr(73 + 2i)`.
Example: row 1 is `VirtualSRLI vr73, vr72, srli32Mask`. -/
def ivLoadRows (rs1 : regidx) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.LD .normal (.vreg (vr (72 + 2 * i))) (.xreg rs1) (BitVec.ofNat 64 (8 * i)),
     .VirtualSRLI (.vreg (vr (73 + 2 * i))) (.vreg (vr (72 + 2 * i))) srli32Mask]

/-- Load the eight block doublewords at `rs2`. `VirtualRev8W` reverses the bytes of each word,
so the low half of `vr(56 + 2i)` is big-endian word `2i` and `vr(57 + 2i)` gets word `2i + 1`.
Example: the first three rows are `LD vr56, 0(rs2)`, `VirtualRev8W vr56, vr56` and
`VirtualSRLI vr57, vr56, srli32Mask`. -/
def msgLoadRows (rs2 : regidx) : List Instr :=
  (List.range 8).flatMap fun i =>
    [.LD .normal (.vreg (vr (56 + 2 * i))) (.xreg rs2) (BitVec.ofNat 64 (8 * i)),
     .VirtualRev8W (.vreg (vr (56 + 2 * i))) (.vreg (vr (56 + 2 * i))) 0,
     .VirtualSRLI (.vreg (vr (57 + 2 * i))) (.vreg (vr (56 + 2 * i))) srli32Mask]

/-- After round 63, add the old state word `c` into working variable `c` in `vr(48 + c)`.
Example: `finalRows false` starts `ADD vr48, vr48, vr72`; `finalRows true` starts
`ADDI vr48, vr48, 0x6a09e667`. -/
def finalRows (initial : Bool) : List Instr :=
  (List.range 8).flatMap fun c => (add (.reg (vr (48 + c))) (ivVal initial c) (vr (48 + c))).1

/-- Pack working variables `2i` (low word) and `2i + 1` (high word) into `vr(48 + 2i)` and store
it at `rs1 + 8i`.
Example: the first four rows are `VirtualZeroExtendWord vr48, vr48`,
`VirtualMULI vr49, vr49, 2^32`, `OR vr48, vr49, vr48` and `SD vr48, 0(rs1)`. -/
def storeRows (rs1 : regidx) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.VirtualZeroExtendWord (.vreg (vr (48 + 2 * i))) (.vreg (vr (48 + 2 * i))) 0,
     .VirtualMULI (.vreg (vr (49 + 2 * i))) (.vreg (vr (49 + 2 * i))) 0x100000000,
     .OR (.vreg (vr (48 + 2 * i))) (.vreg (vr (49 + 2 * i))) (.vreg (vr (48 + 2 * i))),
     .SD (.xreg rs1) (.vreg (vr (48 + 2 * i))) (BitVec.ofNat 64 (8 * i))]

/-- The number of pool registers: 36 for `SHA256` (`vr48..83`), 28 for `SHA256_INIT`
(`vr48..75`).
Example: `poolSize true = 28`. -/
def poolSize (initial : Bool) : Nat := if initial then 28 else 36

/-- Reset the pool registers `vr48..` to zero.
Example: the first row is `ADDI vr48, x0, 0`. -/
def resetRows (initial : Bool) : List Instr :=
  (List.range (poolSize initial)).map fun k =>
    .ADDI (.vreg (vr (48 + k))) (.xreg (regidx.Regidx 0)) 0

/-- The load rows: the old state (for `SHA256` only), then the block.
Example: `(loadRows true rs1 rs2).length = 24`. -/
def loadRows (initial : Bool) (rs1 rs2 : regidx) : List Instr :=
  (if initial then [] else ivLoadRows rs1) ++ msgLoadRows rs2

/-- All rows of `SHA256` (`initial = false`) or `SHA256_INIT` (`initial = true`).
Example: `(sha256Rows false rs1 rs2).length = 1900`. -/
def sha256Rows (initial : Bool) (rs1 rs2 : regidx) : List Instr :=
  loadRows initial rs1 rs2 ++ allRounds initial 64 ++ finalRows initial ++ storeRows rs1 ++
    resetRows initial

end JoltISA.Inlines.Sha256
