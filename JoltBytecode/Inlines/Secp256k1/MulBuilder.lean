import JoltBytecode.Inlines.MacColumns
import JoltBytecode.Inlines.Generated.Secp256k1Mulq
import JoltBytecode.Inlines.Generated.Secp256k1Mulr
import JoltBytecode.Inlines.Generated.Secp256k1Squareq
import JoltBytecode.Inlines.Generated.Secp256k1Squarer
import JoltBytecode.Inlines.Generated.Secp256k1Divq
import JoltBytecode.Inlines.Generated.Secp256k1Divr

/-!
# A structured builder for the secp256k1 field inlines

The six inlines `SECP256K1_{MULQ, MULR, SQUAREQ, SQUARER, DIVQ, DIVR}` come from one Rust
builder, `MulqBuilder::inline_sequence` in `jolt-inlines/secp256k1/src/sequence_builder.rs`
(a16z/jolt `a6b6dc717`). This module transcribes that builder (`mulRows`) in terms of the
column rows of `MacColumns`, and checks segment by segment, each segment by `rfl`, that it
gives exactly the generated rows of each inline (`secp256k1MulqRowsAutoList_eq` and the five
like it). The proofs about the six inlines work on `mulRows`; the generated definitions stay
the trusted ones.

`mulRows` has these parts, in row order:

1. `prologueRows`: load the operands and take the quotient `w` (and, for division, the result)
   as advice;
2. `constRows`: load `p' = 2^256 - q`, one limb for the base field and two for the scalar field
   (the third limb of the scalar field's `p'` is `1`, added as the `word` terms);
3. column 0: `MUL r0, a0, b0`, then the term `low(w0, p)`;
4. columns 1 to 6 (`colTerms`), each followed by its output rows `outRows`: a store to `rs3`
   (multiplication and squaring) or a load-and-compare against the dividend (division) for
   columns 0 to 3, and a comparison with `w[k-4]` for columns 4 to 6;
5. `finalRows`: the top column, `r1 + hi(a3·b3) = w3` without overflow;
6. for division only, `storeRows`: the result stored to `rs3`, after every check;
7. `resetRows`: every pool register reset to zero.

Every lemma is proved; the module has no `sorry`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA.Inlines.Generated

set_option autoImplicit false

namespace JoltISA.Inlines.Secp256k1

/-- The three operations the builder implements. -/
inductive FieldOp where
  | mul
  | square
  | div
  deriving DecidableEq

/-- Virtual register `n`. Example: `vr 48` is the first pool register. -/
abbrev vr (n : Nat) : VReg := BitVec.ofNat 7 n

/-- The pool registers of one inline: the limbs `a`, `b` (for squaring, `b = a`) and `w`, the
`p'` limbs `p` and `p2` (`p2` only for the scalar field), the scratch registers `aux` and `aux2`
(`aux2` only for squaring), the two accumulators `r0`, `r1`, and how many pool registers the
inline allocates from `vr48`. Unused fields hold registers the rows never touch.
Example: `SECP256K1_MULQ` has `a = vr48..51`, `b = vr52..55`, `w = vr56..59`, `p = vr60`,
`aux = vr61`, `r0 = vr62`, `r1 = vr63`, 16 registers. -/
structure MulRegs where
  a : Nat → VReg
  b : Nat → VReg
  w : Nat → VReg
  p : VReg
  p2 : VReg
  aux : VReg
  aux2 : VReg
  r0 : VReg
  r1 : VReg
  count : Nat

namespace MulRegs

/-- The accumulator of column `k`: `r0` for even `k`, `r1` for odd `k`. -/
def r (L : MulRegs) (k : Nat) : VReg := if k % 2 = 0 then L.r0 else L.r1

/-- The column registers of column `k`: accumulator `r k`, carry register `r (k+1)`. -/
def col (L : MulRegs) (k : Nat) : MacRegs := ⟨L.r k, L.r (k + 1), L.aux, L.aux2⟩

end MulRegs

/-- `LD d, off(r)` with Jolt's plain fault class. -/
def ldRow (d : VReg) (r : regidx) (off : Nat) : Instr :=
  .LD .normal (.vreg d) (.xreg r) (BitVec.ofNat 64 off)

/-- `SD v, off(r)`. -/
def sdRow (r : regidx) (v : VReg) (off : Nat) : Instr :=
  .SD (.xreg r) (.vreg v) (BitVec.ofNat 64 off)

/-- The operand loads and advice rows, four rounds of them.
Example: for multiplication, round `i` is `LD a_i, 8i(rs1); LD b_i, 8i(rs2); VirtualAdvice w_i`. -/
def prologueRows (op : FieldOp) (L : MulRegs) (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    List Instr :=
  [0, 1, 2, 3].flatMap fun i =>
    match op with
    | .mul => [ldRow (L.a i) rs1 (8 * i), ldRow (L.b i) rs2 (8 * i),
        .VirtualAdvice (.vreg (L.w i)) (advice i) 0]
    | .square => [ldRow (L.a i) rs1 (8 * i), .VirtualAdvice (.vreg (L.w i)) (advice i) 0]
    | .div => [ldRow (L.b i) rs2 (8 * i), .VirtualAdvice (.vreg (L.a i)) (advice (2 * i)) 0,
        .VirtualAdvice (.vreg (L.w i)) (advice (2 * i + 1)) 0]

/-- The low limb of `p'` for the base field. -/
def pPrimeBase : BitVec 64 := 0x1000003d1

/-- The two low limbs of `p'` for the scalar field (its third limb is `1`). -/
def pPrimeScalar0 : BitVec 64 := 0x402da1732fc9bebf

/-- See `pPrimeScalar0`. -/
def pPrimeScalar1 : BitVec 64 := 0x4551231950b75fc4

/-- The `LUI` rows that load `p'`. -/
def constRows (scalar : Bool) (L : MulRegs) : List Instr :=
  if scalar then [.LUI (.vreg L.p) pPrimeScalar0, .LUI (.vreg L.p2) pPrimeScalar1]
  else [.LUI (.vreg L.p) pPrimeBase]

/-- The product terms of column `k`: `lo(a_i·b_j)` for `i + j = k`, then `hi(a_i·b_j)` for
`i + j = k - 1`. For squaring only `i ≤ j` appears, with the off-diagonal terms doubled. -/
def prodTerms (op : FieldOp) (L : MulRegs) (k : Nat) : List Mac :=
  ((List.range (k + 1)).filterMap fun i =>
    let j := k - i
    if i < 4 ∧ j < 4 then
      match op with
      | .square => if i < j then some (.low2 (L.a i) (L.a j))
          else if i = j then some (.low (L.a i) (L.a i)) else none
      | _ => some (.low (L.a i) (L.b j))
    else none) ++
  ((List.range k).filterMap fun i =>
    let j := k - 1 - i
    if i < 4 ∧ j < 4 then
      match op with
      | .square => if i < j then some (.high2 (L.a i) (L.a j))
          else if i = j then some (.high (L.a i) (L.a i)) else none
      | _ => some (.high (L.a i) (L.b j))
    else none)

/-- The terms of column `k` (`1 ≤ k ≤ 6`), in the order the builder emits them: the
`w·p'` terms, then the product terms.
Example: column 1 of `MULQ` is `[lo(w1·p), hi(w0·p), lo(a0·b1), lo(a1·b0), hi(a0·b0)]`. -/
def colTerms (op : FieldOp) (scalar : Bool) (L : MulRegs) (k : Nat) : List Mac :=
  (if k < 4 then [.low (L.w k) L.p] else []) ++
  (if k ≤ 4 then [.high (L.w (k - 1)) L.p] else []) ++
  (if scalar ∧ k ≤ 4 then [.low (L.w (k - 1)) L.p2] else []) ++
  (if scalar ∧ 2 ≤ k ∧ k ≤ 5 then [.high (L.w (k - 2)) L.p2, .word (L.w (k - 2))] else []) ++
  prodTerms op L k

/-- What happens to the finished column `k`: for `k < 4`, store it to `rs3` (division: load
dividend limb `k` and compare); for `k ≥ 4`, compare it with `w[k-4]`. -/
def outRows (op : FieldOp) (L : MulRegs) (rs1 rs3 : regidx) (k : Nat) : List Instr :=
  if k < 4 then
    match op with
    | .div => [ldRow L.aux rs1 (8 * k), .VirtualAssertEQ (.vreg (L.r k)) (.vreg L.aux) 0]
    | _ => [sdRow rs3 (L.r k) (8 * k)]
  else [.VirtualAssertEQ (.vreg (L.r k)) (.vreg (L.w (k - 4))) 0]

/-- Column 0 and its output. -/
def col0Rows (op : FieldOp) (L : MulRegs) (rs1 rs3 : regidx) : List Instr :=
  .MUL (.vreg L.r0) (.vreg (L.a 0)) (.vreg (L.b 0)) ::
    (colRows (L.col 0) true [.low (L.w 0) L.p] ++ outRows op L rs1 rs3 0)

/-- Column `k` (`1 ≤ k ≤ 6`) and its output. -/
def colKRows (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs3 : regidx) (k : Nat) :
    List Instr :=
  colRows (L.col k) true (colTerms op scalar L k) ++ outRows op L rs1 rs3 k

/-- The top column: `r1 + hi(a3·b3)` must equal `w3`, and the addition must not overflow. -/
def finalRows (L : MulRegs) : List Instr :=
  [.MULHU (.vreg L.aux) (.vreg (L.a 3)) (.vreg (L.b 3)),
    .ADD (.vreg L.r1) (.vreg L.r1) (.vreg L.aux),
    .VirtualAssertEQ (.vreg L.r1) (.vreg (L.w 3)) 0,
    .VirtualAssertLTE (.vreg L.aux) (.vreg L.r1) 0]

/-- Division stores its result, held in `a`, after every check. -/
def storeRows (L : MulRegs) (rs3 : regidx) : List Instr :=
  [0, 1, 2, 3].map fun i => sdRow rs3 (L.a i) (8 * i)

/-- The rows of one field inline, as `MulqBuilder::inline_sequence` emits them. -/
def mulRows (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs2 rs3 : regidx)
    (advice : Nat → BitVec 64) : List Instr :=
  prologueRows op L rs1 rs2 advice ++ constRows scalar L ++ col0Rows op L rs1 rs3 ++
    ((List.range' 1 6).flatMap fun k => colKRows op scalar L rs1 rs3 k) ++ finalRows L ++
    (if op = .div then storeRows L rs3 else []) ++
    resetRows ((List.range L.count).map fun i => vr (48 + i))

/-! ## Register layouts -/

/-- `MULQ` and `DIVQ`. -/
def mulqRegs : MulRegs where
  a i := vr (48 + i)
  b i := vr (52 + i)
  w i := vr (56 + i)
  p := vr 60
  p2 := vr 126
  aux := vr 61
  aux2 := vr 127
  r0 := vr 62
  r1 := vr 63
  count := 16

/-- `MULR` and `DIVR`. -/
def mulrRegs : MulRegs where
  a i := vr (48 + i)
  b i := vr (52 + i)
  w i := vr (56 + i)
  p := vr 60
  p2 := vr 61
  aux := vr 62
  aux2 := vr 127
  r0 := vr 63
  r1 := vr 64
  count := 17

/-- `SQUAREQ`. -/
def squareqRegs : MulRegs where
  a i := vr (48 + i)
  b i := vr (48 + i)
  w i := vr (52 + i)
  p := vr 56
  p2 := vr 126
  aux := vr 57
  aux2 := vr 58
  r0 := vr 59
  r1 := vr 60
  count := 13

/-- `SQUARER`. -/
def squarerRegs : MulRegs where
  a i := vr (48 + i)
  b i := vr (48 + i)
  w i := vr (52 + i)
  p := vr 56
  p2 := vr 57
  aux := vr 58
  aux2 := vr 59
  r0 := vr 60
  r1 := vr 61
  count := 14

/-! ## The builder gives the generated rows

A single `rfl` on a whole inline compares two lists of about 190 rows in one go and exceeds the
recursion limit. The proofs below instead split `mulRows` into its segments (prologue, constants,
one block per column, final rows, stores, resets) and check each segment against the matching
slice of the generated list with `rfl`. -/

/-- A list is `A ++ B` when its first `A.length` entries are `A` and the rest is `B`.
Example: `[1, 2, 3] = [1] ++ [2, 3]`. -/
theorem eq_append_of_take_drop {α : Type} {l A B : List α} (h1 : l.take A.length = A)
    (h2 : l.drop A.length = B) : l = A ++ B := by
  rw [← h1, ← h2, List.take_append_drop]

/-- Splits `mulRows` into its segments and checks each against the generated rows. -/
macro "mul_rows_eq" : tactic => `(tactic| (
  simp only [mulRows, List.range', List.flatMap_cons, List.flatMap_nil, List.append_assoc,
    List.append_nil, List.nil_append, reduceCtorEq, ↓reduceIte, Nat.reduceAdd]
  repeat refine eq_append_of_take_drop rfl ?_
  rfl))

/-- The generated `SECP256K1_MULQ` rows are `mulRows` for that inline.
Example: both lists start with the prologue row `LD vr48, 0(rs1)`. -/
theorem secp256k1MulqRowsAutoList_eq (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    secp256k1MulqRowsAutoList rs1 rs2 rs3 advice =
      mulRows .mul false mulqRegs rs1 rs2 rs3 advice := by mul_rows_eq

/-- The generated `SECP256K1_MULR` rows are `mulRows` for that inline.
Example: both lists start with the prologue row `LD vr48, 0(rs1)`. -/
theorem secp256k1MulrRowsAutoList_eq (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    secp256k1MulrRowsAutoList rs1 rs2 rs3 advice =
      mulRows .mul true mulrRegs rs1 rs2 rs3 advice := by mul_rows_eq

/-- The generated `SECP256K1_SQUAREQ` rows are `mulRows` for that inline.
Example: both lists start with the prologue row `LD vr48, 0(rs1)`. -/
theorem secp256k1SquareqRowsAutoList_eq (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    secp256k1SquareqRowsAutoList rs1 rs2 rs3 advice =
      mulRows .square false squareqRegs rs1 rs2 rs3 advice := by mul_rows_eq

/-- The generated `SECP256K1_SQUARER` rows are `mulRows` for that inline.
Example: both lists start with the prologue row `LD vr48, 0(rs1)`. -/
theorem secp256k1SquarerRowsAutoList_eq (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    secp256k1SquarerRowsAutoList rs1 rs2 rs3 advice =
      mulRows .square true squarerRegs rs1 rs2 rs3 advice := by mul_rows_eq

/-- The generated `SECP256K1_DIVQ` rows are `mulRows` for that inline.
Example: both lists start with the prologue row `LD vr52, 0(rs2)`. -/
theorem secp256k1DivqRowsAutoList_eq (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    secp256k1DivqRowsAutoList rs1 rs2 rs3 advice =
      mulRows .div false mulqRegs rs1 rs2 rs3 advice := by mul_rows_eq

/-- The generated `SECP256K1_DIVR` rows are `mulRows` for that inline.
Example: both lists start with the prologue row `LD vr52, 0(rs2)`. -/
theorem secp256k1DivrRowsAutoList_eq (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    secp256k1DivrRowsAutoList rs1 rs2 rs3 advice =
      mulRows .div true mulrRegs rs1 rs2 rs3 advice := by mul_rows_eq

end JoltISA.Inlines.Secp256k1
