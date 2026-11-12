import JoltBytecode.Inlines.Secp256k1.MulBuilder
import JoltBytecode.Inlines.Secp256k1.GlvrAdv

/-!
# secp256k1 `MUL` and `SQUARE`: soundness and completeness of the rows

The four inlines `SECP256K1_MULQ`, `SECP256K1_MULR`, `SECP256K1_SQUAREQ` and
`SECP256K1_SQUARER` multiply two 256-bit operands (or square one) modulo the base-field prime
`p` (`Q`) or the group order `n` (`R`). The rows load the operands from `rs1` and `rs2` and take
four quotient words `w` as advice. With `p' = 2^256 - q`, columns 0 to 3 compute the low limbs
`c` of `a·b + w·p'` with carries and store them to the buffer at `rs3`; columns 4 to 7 check
that the high limbs equal `w`. So `a·b + w·p' = c + 2^256·w`, that is `a·b = w·q + c`
(`MulRel`).

* `mulRows_sound`: every run of the rows from a state whose output buffer lies in RAM reads
  operands `a`, `b`, writes four words `c` with `MulRel q a b w c` for some `w`, and changes
  nothing else (`FieldMulSpec`).
* `mulRows_jolt_advice_complete`: with Jolt's quotient advice, from a state where the operands
  and the buffer can be read and written (`FieldMulPre`), the rows run, and the stored result is
  canonical, below `q` (`FieldMulCanonical`).
* `secp256k1Mulq_rows_sound` … `secp256k1Squarer_rows_jolt_advice_complete`: the two theorems
  for each of the four generated row sequences. Completeness assumes operands below `q`, which
  is what makes Jolt's advice exist.

The concrete known-answer instances are in `JoltTests.Inlines.Secp256k1FieldMulInstance`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Generated

set_option autoImplicit false

namespace JoltISA.Inlines.Secp256k1

/-! ## The column identity -/

/-- The sum of the terms of column `k` in register file `F`.
Example: column 1 of `MULQ` sums `lo(vr57·vr60)`, `hi(vr56·vr60)`, `lo(vr48·vr53)`,
`lo(vr49·vr52)` and `hi(vr48·vr52)`; with `vr48 = 2^63`, `vr52 = 2` and every other register
`0`, the sum is `hi(2^63·2) = 1`. -/
def colSum (op : FieldOp) (scalar : Bool) (L : MulRegs) (F : VReg → BitVec 64) (k : Nat) : Nat :=
  ((colTerms op scalar L k).map (Mac.val F)).sum

/-- The value of four little-endian limb registers `r 0, …, r 3` in register file `F`.
Example: if `F (r 1) = 1` and the other three are `0`, the value is `2^64`. -/
def limbVal (r : Nat → VReg) (F : VReg → BitVec 64) : Nat :=
  (F (r 0)).toNat + 2 ^ 64 * (F (r 1)).toNat + 2 ^ 128 * (F (r 2)).toNat +
    2 ^ 192 * (F (r 3)).toNat

private theorem mah (x y : BitVec 64) :
    ((x * y).toNat : ℤ) + 2 ^ 64 * ((jolt_mulhu_value x y).toNat : ℤ) =
      (x.toNat : ℤ) * y.toNat := by
  exact_mod_cast mul_add_mulhu x y


private theorem two_pow_128 : (2 : ℤ) ^ 128 = (2 ^ 64) ^ 2 := by rw [← pow_mul]

private theorem two_pow_192 : (2 : ℤ) ^ 192 = (2 ^ 64) ^ 3 := by rw [← pow_mul]

private theorem two_pow_256 : (2 : ℤ) ^ 256 = (2 ^ 64) ^ 4 := by rw [← pow_mul]

private theorem two_pow_320 : (2 : ℤ) ^ 320 = (2 ^ 64) ^ 5 := by rw [← pow_mul]

private theorem two_pow_384 : (2 : ℤ) ^ 384 = (2 ^ 64) ^ 6 := by rw [← pow_mul]

private theorem two_pow_448 : (2 : ℤ) ^ 448 = (2 ^ 64) ^ 7 := by rw [← pow_mul]

/-- The weighted sum of all columns, as the rows compute it: the two low terms of column 0,
the terms of columns 1 to 6 at weight `2^(64k)`, and the high product `hi(a3·b3)` of the top
column at weight `2^448`.
Example: for `MULQ` with `a = 2`, `b = (p+1)/2` and `w = 1`, it is `2^256 + 1`. -/
def colTotal (op : FieldOp) (scalar : Bool) (L : MulRegs) (F : VReg → BitVec 64) : Nat :=
  (F (L.a 0) * F (L.b 0)).toNat + (F (L.w 0) * F L.p).toNat +
    2 ^ 64 * colSum op scalar L F 1 + 2 ^ 128 * colSum op scalar L F 2 +
    2 ^ 192 * colSum op scalar L F 3 + 2 ^ 256 * colSum op scalar L F 4 +
    2 ^ 320 * colSum op scalar L F 5 + 2 ^ 384 * colSum op scalar L F 6 +
    2 ^ 448 * (jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat

/-- The `p'` terms of column `k`, the part of `colTerms` that does not depend on the operation.
Example: for `mulqRegs`, column 1 is `[lo(vr57·vr60), hi(vr56·vr60)]`; with `vr56 = 0`,
`vr57 = 1` and `vr60 = 2^32 + 977`, the base-field `p'`, the terms sum to `2^32 + 977`. -/
def corrTerms (scalar : Bool) (L : MulRegs) (k : Nat) : List Mac :=
  (if k < 4 then [.low (L.w k) L.p] else []) ++
  (if k ≤ 4 then [.high (L.w (k - 1)) L.p] else []) ++
  (if scalar ∧ k ≤ 4 then [.low (L.w (k - 1)) L.p2] else []) ++
  (if scalar ∧ 2 ≤ k ∧ k ≤ 5 then [.high (L.w (k - 2)) L.p2, .word (L.w (k - 2))] else [])

/-- The terms of a column are its `p'` terms followed by its product terms.
Example: column 1 of `MULQ` is
`[lo(vr57·vr60), hi(vr56·vr60)] ++ [lo(vr48·vr53), lo(vr49·vr52), hi(vr48·vr52)]`. -/
theorem colTerms_eq_append (op : FieldOp) (scalar : Bool) (L : MulRegs) (k : Nat) :
    colTerms op scalar L k = corrTerms scalar L k ++ prodTerms op L k := rfl

/-- The product part of `colTotal`: `lo(a0·b0)`, the product terms of columns 1 to 6, and
`hi(a3·b3)`.
Example: for `MULQ` with `a = 2` and `b = (p+1)/2`, it is `p + 1`. -/
def prodTotal (op : FieldOp) (L : MulRegs) (F : VReg → BitVec 64) : Nat :=
  (F (L.a 0) * F (L.b 0)).toNat +
    2 ^ 64 * ((prodTerms op L 1).map (Mac.val F)).sum +
    2 ^ 128 * ((prodTerms op L 2).map (Mac.val F)).sum +
    2 ^ 192 * ((prodTerms op L 3).map (Mac.val F)).sum +
    2 ^ 256 * ((prodTerms op L 4).map (Mac.val F)).sum +
    2 ^ 320 * ((prodTerms op L 5).map (Mac.val F)).sum +
    2 ^ 384 * ((prodTerms op L 6).map (Mac.val F)).sum +
    2 ^ 448 * (jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat

/-- The `p'` part of `colTotal`: `lo(w0·p)` and the `p'` terms of columns 1 to 6.
Example: for `MULQ` with `w = 1`, it is `p' = 2^32 + 977`. -/
def corrTotal (scalar : Bool) (L : MulRegs) (F : VReg → BitVec 64) : Nat :=
  (F (L.w 0) * F L.p).toNat +
    2 ^ 64 * ((corrTerms scalar L 1).map (Mac.val F)).sum +
    2 ^ 128 * ((corrTerms scalar L 2).map (Mac.val F)).sum +
    2 ^ 192 * ((corrTerms scalar L 3).map (Mac.val F)).sum +
    2 ^ 256 * ((corrTerms scalar L 4).map (Mac.val F)).sum +
    2 ^ 320 * ((corrTerms scalar L 5).map (Mac.val F)).sum +
    2 ^ 384 * ((corrTerms scalar L 6).map (Mac.val F)).sum

/-- The column sum splits into its product part and its `p'` part.
Example: for `MULQ` with `a = 2`, `b = (p+1)/2` and `w = 1`, `2^256 + 1 = (p + 1) + p'`. -/
theorem colTotal_eq_add (op : FieldOp) (scalar : Bool) (L : MulRegs) (F : VReg → BitVec 64) :
    colTotal op scalar L F = prodTotal op L F + corrTotal scalar L F := by
  simp only [colTotal, prodTotal, corrTotal, colSum, colTerms_eq_append, List.map_append,
    List.sum_append, Nat.mul_add]
  omega

/-- Division has the product terms of multiplication.
Example: with `mulqRegs`, column 1 of both is `[lo(vr48·vr53), lo(vr49·vr52), hi(vr48·vr52)]`. -/
theorem prodTotal_div (L : MulRegs) (F : VReg → BitVec 64) :
    prodTotal .div L F = prodTotal .mul L F := rfl

private theorem prodTotal_mul (L : MulRegs) (F : VReg → BitVec 64) :
    prodTotal .mul L F = limbVal L.a F * limbVal L.b F := by
  unfold prodTotal
  simp only [prodTerms, List.range_succ, List.range_zero, List.nil_append,
    List.filterMap_cons, List.filterMap_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
    and_self, and_false, ↓reduceIte, Nat.lt_irrefl,
    List.cons_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Mac.val, Nat.add_zero, false_and, limbVal]
  zify
  linear_combination (norm := skip) 2^0 * mah (F (L.a 0)) (F (L.b 0)) +
      2^64 * mah (F (L.a 0)) (F (L.b 1)) + 2^128 * mah (F (L.a 0)) (F (L.b 2)) +
      2^192 * mah (F (L.a 0)) (F (L.b 3)) + 2^64 * mah (F (L.a 1)) (F (L.b 0)) +
      2^128 * mah (F (L.a 1)) (F (L.b 1)) + 2^192 * mah (F (L.a 1)) (F (L.b 2)) +
      2^256 * mah (F (L.a 1)) (F (L.b 3)) + 2^128 * mah (F (L.a 2)) (F (L.b 0)) +
      2^192 * mah (F (L.a 2)) (F (L.b 1)) + 2^256 * mah (F (L.a 2)) (F (L.b 2)) +
      2^320 * mah (F (L.a 2)) (F (L.b 3)) + 2^192 * mah (F (L.a 3)) (F (L.b 0)) +
      2^256 * mah (F (L.a 3)) (F (L.b 1)) + 2^320 * mah (F (L.a 3)) (F (L.b 2)) +
      2^384 * mah (F (L.a 3)) (F (L.b 3))
  simp only [two_pow_128, two_pow_192, two_pow_256, two_pow_320, two_pow_384, two_pow_448]
  generalize (2 : ℤ) ^ 64 = B
  ring1

private theorem prodTotal_square (L : MulRegs) (F : VReg → BitVec 64) (hsq : L.b = L.a) :
    prodTotal .square L F = limbVal L.a F * limbVal L.b F := by
  unfold prodTotal
  rw [hsq]
  simp only [prodTerms, List.range_succ, List.range_zero, List.nil_append,
    List.filterMap_cons, List.filterMap_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, and_self, and_false, ↓reduceIte, Nat.lt_irrefl,
    List.cons_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Mac.val, Nat.add_zero, false_and, limbVal]
  zify
  linear_combination (norm := skip) 2^0 * mah (F (L.a 0)) (F (L.a 0)) +
      2 * 2^64 * mah (F (L.a 0)) (F (L.a 1)) + 2 * 2^128 * mah (F (L.a 0)) (F (L.a 2)) +
      2 * 2^192 * mah (F (L.a 0)) (F (L.a 3)) + 2^128 * mah (F (L.a 1)) (F (L.a 1)) +
      2 * 2^192 * mah (F (L.a 1)) (F (L.a 2)) + 2 * 2^256 * mah (F (L.a 1)) (F (L.a 3)) +
      2^256 * mah (F (L.a 2)) (F (L.a 2)) + 2 * 2^320 * mah (F (L.a 2)) (F (L.a 3)) +
      2^384 * mah (F (L.a 3)) (F (L.a 3))
  simp only [two_pow_128, two_pow_192, two_pow_256, two_pow_320, two_pow_384, two_pow_448]
  generalize (2 : ℤ) ^ 64 = B
  ring1

private theorem corrTotal_base (L : MulRegs) (F : VReg → BitVec 64)
    (hp : ((F L.p).toNat : ℤ) = (2 : ℤ) ^ 32 + 977) :
    corrTotal false L F = limbVal L.w F * pPrime p := by
  unfold corrTotal
  simp only [corrTerms, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
    and_self, and_false, ↓reduceIte, Nat.lt_irrefl, Bool.false_eq_true, false_and,
    List.cons_append, List.nil_append, List.append_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Mac.val, Nat.add_zero, Nat.mul_zero, limbVal]
  rw [pPrime_p]
  zify
  linear_combination (norm := skip) 2^0 * mah (F (L.w 0)) (F L.p) +
      2^64 * mah (F (L.w 1)) (F L.p) + 2^128 * mah (F (L.w 2)) (F L.p) +
      2^192 * mah (F (L.w 3)) (F L.p) + (2^0 * ((F (L.w 0)).toNat : ℤ) +
      2^64 * ((F (L.w 1)).toNat : ℤ) + 2^128 * ((F (L.w 2)).toNat : ℤ) +
      2^192 * ((F (L.w 3)).toNat : ℤ)) * hp
  simp only [two_pow_128, two_pow_192, two_pow_256]
  generalize (2 : ℤ) ^ 64 = B
  ring1

private theorem corrTotal_scalar (L : MulRegs) (F : VReg → BitVec 64)
    (hp : ((F L.p).toNat : ℤ) = 0x402da1732fc9bebf)
    (hp2 : ((F L.p2).toNat : ℤ) = 0x4551231950b75fc4) :
    corrTotal true L F = limbVal L.w F * pPrime n := by
  unfold corrTotal
  simp only [corrTerms, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
    and_self, and_false, ↓reduceIte, Nat.lt_irrefl, false_and,
    List.cons_append, List.nil_append, List.append_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Mac.val, Nat.add_zero, Nat.mul_zero, limbVal]
  rw [pPrime_n]
  zify
  linear_combination (norm := skip) 2^0 * mah (F (L.w 0)) (F L.p) +
      2^64 * mah (F (L.w 0)) (F L.p2) + 2^64 * mah (F (L.w 1)) (F L.p) +
      2^128 * mah (F (L.w 1)) (F L.p2) + 2^128 * mah (F (L.w 2)) (F L.p) +
      2^192 * mah (F (L.w 2)) (F L.p2) + 2^192 * mah (F (L.w 3)) (F L.p) +
      2^256 * mah (F (L.w 3)) (F L.p2) + (2^0 * ((F (L.w 0)).toNat : ℤ) +
      2^64 * ((F (L.w 1)).toNat : ℤ) + 2^128 * ((F (L.w 2)).toNat : ℤ) +
      2^192 * ((F (L.w 3)).toNat : ℤ)) * hp + 2^64 * (2^0 * ((F (L.w 0)).toNat : ℤ) +
      2^64 * ((F (L.w 1)).toNat : ℤ) + 2^128 * ((F (L.w 2)).toNat : ℤ) +
      2^192 * ((F (L.w 3)).toNat : ℤ)) * hp2
  simp only [two_pow_128, two_pow_192, two_pow_256, two_pow_320]
  generalize (2 : ℤ) ^ 64 = B
  ring1

/-- **The column identity.** With `p'` loaded as the rows load it, the weighted column sum is
`A·B + W·p'`, where `A`, `B`, `W` are the values of the limb registers `a`, `b`, `w`. For
squaring, `b` is `a`.
Example: for `MULQ` with `A = 2`, `B = (p+1)/2`, `W = 1`, both sides are `2^256 + 1`. -/
theorem colTotal_eq {op : FieldOp} {scalar : Bool} {L : MulRegs} {F : VReg → BitVec 64}
    (hsq : op = .square → L.b = L.a)
    (hp : F L.p = if scalar then pPrimeScalar0 else pPrimeBase)
    (hp2 : scalar = true → F L.p2 = pPrimeScalar1) :
    colTotal op scalar L F =
      limbVal L.a F * limbVal L.b F + limbVal L.w F * pPrime (if scalar then n else p) := by
  have hprod : prodTotal op L F = limbVal L.a F * limbVal L.b F := by
    cases op
    · exact prodTotal_mul L F
    · exact prodTotal_square L F (hsq rfl)
    · rw [prodTotal_div]; exact prodTotal_mul L F
  rw [colTotal_eq_add, hprod]
  cases scalar
  · have h : ((F L.p).toNat : ℤ) = (2 : ℤ) ^ 32 + 977 := by
      rw [hp]; decide
    rw [corrTotal_base L F h]
    rfl
  · have h : ((F L.p).toNat : ℤ) = 0x402da1732fc9bebf := by
      rw [hp]; decide
    have h2 : ((F L.p2).toNat : ℤ) = 0x4551231950b75fc4 := by
      rw [hp2 rfl]; decide
    rw [corrTotal_scalar L F h h2]
    rfl

/-! ## The register file after the prologue -/

/-- The registers that the prologue and constant rows write, with the values they write, in
row order. `x` is the limbs at `rs1`, `y` the limbs at `rs2`.
Example: for `MULQ` the list starts `(vr48, x[0]), (vr52, y[0]), (vr56, advice 0)`. -/
def preWrites (op : FieldOp) (scalar : Bool) (L : MulRegs) (x y : Limbs)
    (advice : Nat → BitVec 64) : List (VReg × BitVec 64) :=
  (match op with
    | .mul => [(L.a 0, x[0]), (L.b 0, y[0]), (L.w 0, advice 0),
        (L.a 1, x[1]), (L.b 1, y[1]), (L.w 1, advice 1),
        (L.a 2, x[2]), (L.b 2, y[2]), (L.w 2, advice 2),
        (L.a 3, x[3]), (L.b 3, y[3]), (L.w 3, advice 3)]
    | .square => [(L.a 0, x[0]), (L.w 0, advice 0), (L.a 1, x[1]), (L.w 1, advice 1),
        (L.a 2, x[2]), (L.w 2, advice 2), (L.a 3, x[3]), (L.w 3, advice 3)]
    | .div => [(L.b 0, y[0]), (L.a 0, advice 0), (L.w 0, advice 1),
        (L.b 1, y[1]), (L.a 1, advice 2), (L.w 1, advice 3),
        (L.b 2, y[2]), (L.a 2, advice 4), (L.w 2, advice 5),
        (L.b 3, y[3]), (L.a 3, advice 6), (L.w 3, advice 7)]) ++
  (if scalar then [(L.p, pPrimeScalar0), (L.p2, pPrimeScalar1)] else [(L.p, pPrimeBase)])

/-- The registers of `preWrites`, in row order.
Example: for `SQUAREQ`, `vr48, vr52, vr49, vr53, vr50, vr54, vr51, vr55, vr56`. -/
def preRegs (op : FieldOp) (scalar : Bool) (L : MulRegs) : List VReg :=
  (match op with
    | .mul => [L.a 0, L.b 0, L.w 0, L.a 1, L.b 1, L.w 1, L.a 2, L.b 2, L.w 2,
        L.a 3, L.b 3, L.w 3]
    | .square => [L.a 0, L.w 0, L.a 1, L.w 1, L.a 2, L.w 2, L.a 3, L.w 3]
    | .div => [L.b 0, L.a 0, L.w 0, L.b 1, L.a 1, L.w 1, L.b 2, L.a 2, L.w 2,
        L.b 3, L.a 3, L.w 3]) ++
  (if scalar then [L.p, L.p2] else [L.p])

/-- The registers of `preWrites` are `preRegs`.
Example: for `SQUAREQ`, the first register of both lists is `vr48`. -/
theorem preWrites_fst (op : FieldOp) (scalar : Bool) (L : MulRegs) (x y : Limbs)
    (advice : Nat → BitVec 64) :
    (preWrites op scalar L x y advice).map Prod.fst = preRegs op scalar L := by
  cases op <;> cases scalar <;> rfl

/-- The register file after writing `ws` in order.
Example: `writeAll f [(vr48, 1)]` is `setV f vr48 1`. -/
def writeAll (f : VReg → BitVec 64) (ws : List (VReg × BitVec 64)) : VReg → BitVec 64 :=
  ws.foldl (fun f w => setV f w.1 w.2) f

/-- Writes to other registers leave a register alone.
Example: `writeAll f [(vr48, 1)] vr49 = f vr49`. -/
theorem writeAll_of_not_mem (f : VReg → BitVec 64) {ws : List (VReg × BitVec 64)} {d : VReg}
    (h : d ∉ ws.map Prod.fst) : writeAll f ws d = f d := by
  induction ws generalizing f with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [writeAll, List.foldl_cons] at ih ⊢
    rw [ih _ h.2]
    exact setV_ne _ _ h.1

/-- After writes to distinct registers, each written register holds its value.
Example: `writeAll f [(vr48, 1), (vr49, 2)] vr48 = 1`. -/
theorem writeAll_of_mem (f : VReg → BitVec 64) {ws : List (VReg × BitVec 64)}
    (hnd : (ws.map Prod.fst).Nodup) {d : VReg} {v : BitVec 64} (h : (d, v) ∈ ws) :
    writeAll f ws d = v := by
  induction ws generalizing f with
  | nil => cases h
  | cons w ws ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have e : writeAll f (w :: ws) = writeAll (setV f w.1 w.2) ws := rfl
    rw [e]
    rcases List.mem_cons.1 h with h | h
    · subst h
      rw [writeAll_of_not_mem _ hnd.1, setV_same]
    · exact ih _ hnd.2 h

/-- A register other than the two accumulators `L.r0`, `L.r1` and the two scratch registers
`L.aux`, `L.aux2`, so the column rows never write it. The operand and constant registers are
examples.
Example: for `mulqRegs`, `vr48..vr60` and also `vr32` satisfy it; `vr61`, `vr62`, `vr63` and
`vr127` do not. -/
def MulRegs.OpFree (L : MulRegs) (r : VReg) : Prop := (L.col 0).Free r

/-- Whether a register is free of the column registers can be decided.
Example: `decide (mulqRegs.OpFree (vr 48))` evaluates to `true`. -/
instance (L : MulRegs) (r : VReg) : Decidable (L.OpFree r) := by
  unfold MulRegs.OpFree; infer_instance

/-- The conditions on a register layout under which the proofs go through. Each concrete layout
meets them by `decide` (`mulqRegs_valid` and the three like it).
Example: `mulqRegs.Valid .mul false`. -/
structure MulRegs.Valid (op : FieldOp) (scalar : Bool) (L : MulRegs) : Prop where
  pre_nodup : (preRegs op scalar L).Nodup
  pre_ge : ∀ r ∈ preRegs op scalar L, 32 ≤ r.toNat
  pre_free : ∀ r ∈ preRegs op scalar L, L.OpFree r
  col0 : (L.col 0).Valid
  col1 : (L.col 1).Valid
  terms : ∀ k ∈ List.range' 1 6, 0 < (colTerms op scalar L k).length ∧
    2 * (colTerms op scalar L k).length < 2 ^ 63 ∧
    ∀ m ∈ colTerms op scalar L k, ∀ r ∈ m.ops, L.OpFree r
  square : op = .square → L.b = L.a
  pool : ∀ i < L.count, 32 ≤ (vr (48 + i)).toNat

/-- A register free of column 0's registers is free of every column's registers: the columns
alternate between the same two accumulators.
Example: `vr48` is free in every column of `mulqRegs`. -/
theorem MulRegs.col_free {L : MulRegs} {r : VReg} (h : L.OpFree r) (k : Nat) :
    (L.col k).Free r := by
  unfold MulRegs.OpFree MulRegs.col MulRegs.r MacRegs.Free at *
  simp only [Nat.zero_mod, Nat.reduceAdd, Nat.one_mod, ite_true, show ¬ (1 = 0) from by decide,
    ite_false] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  split <;> split <;> exact ⟨by assumption, by assumption, h3, h4⟩

/-- Every column's registers meet `MacRegs.Valid` when columns 0 and 1 do.
Example: column 5 of `mulqRegs` uses the registers of column 1. -/
theorem MulRegs.col_valid {op : FieldOp} {scalar : Bool} {L : MulRegs}
    (hv : L.Valid op scalar) (k : Nat) : (L.col k).Valid := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have e : L.col k = L.col 0 := by
      simp only [MulRegs.col, MulRegs.r, h, Nat.zero_mod, ite_true, Nat.add_mod,
        Nat.one_mod, Nat.zero_add]
    rw [e]; exact hv.col0
  · have e : L.col k = L.col 1 := by
      simp only [MulRegs.col, MulRegs.r, h, Nat.one_mod, Nat.add_mod, Nat.reduceAdd,
        Nat.mod_self, show ¬ (1 = 0) from by decide, ite_true, ite_false]
    rw [e]; exact hv.col1

/-! ## Rows from a register file -/

/-- A register row from `{s with vregs := f}` sets its destination.
Example: `MUL vr62, vr48, vr52`. -/
theorem run_regRow_vregs_iff {i : Instr} {d : VReg} {g : (VReg → BitVec 64) → BitVec 64}
    (hi : i.regRow? = some (d, g)) (hd : 32 ≤ d.toNat) (s : SailJoltState)
    (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (i :: rest)).Run { s with vregs := f } s' ↔
      (Program.seq rest).Run { s with vregs := setV f d (g f) } s' := by
  have h : regRun [i] f = some (setV f d (g f)) := by
    simp only [regRun, hi, hd, ite_true]
  exact run_append_of_regRun (s := { s with vregs := f }) h rest s'

/-- Register rows from `{s with vregs := f}` change only the register file.
Example: the rows of column 1 of `MULQ`, which write only `vr61`, `vr62` and `vr63`. -/
theorem run_regs_vregs_iff {l : List Instr} {f g : VReg → BitVec 64} (h : regRun l f = some g)
    (s : SailJoltState) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (l ++ rest)).Run { s with vregs := f } s' ↔
      (Program.seq rest).Run { s with vregs := g } s' :=
  run_append_of_regRun (s := { s with vregs := f }) h rest s'

/-- An `LD` from `{s with vregs := f}` loads from the memory of `s`.
Example: `LD vr48, 0(x10)`. -/
theorem run_ld_vregs_iff {fc : LoadFaultClass} {d : VReg} (hd : 32 ≤ d.toNat) {r : regidx}
    {imm : BitVec 64} {s : SailJoltState} {base : BitVec 64} (hr : XReads s r base)
    (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (.LD fc (.vreg d) (.xreg r) imm :: rest)).Run { s with vregs := f } s' ↔
      ∃ v, loadDword? s (base + imm) = some v ∧
        (Program.seq rest).Run { s with vregs := setV f d v } s' := by
  rw [run_ld_iff hd (XReads.vregs f hr), loadDword?_vregs]

/-- The state after a RAM doubleword store of `v` at `ea`.
Example: `memWrite s 0x80020000 1` stores `1` at `0x8002_0000`. -/
def memWrite (s : SailJoltState) (ea : Nat) (v : BitVec 64) : SailJoltState :=
  { s with sail := { s.sail with mem := Mmu.write_ram_doubleword s.sail.mem ea v } }

/-- A store keeps the architectural registers.
Example: after `memWrite s 0x80020000 1`, `x12` still holds what it held in `s`. -/
theorem memWrite_regs {t s : SailJoltState} (h : t.sail.regs = s.sail.regs) (ea : Nat)
    (v : BitVec 64) : (memWrite t ea v).sail.regs = s.sail.regs := h

/-- A store keeps the device description.
Example: `(memWrite s 0x80020000 1).jolt_device = s.jolt_device`. -/
@[simp] theorem memWrite_jolt_device (t : SailJoltState) (ea : Nat) (v : BitVec 64) :
    (memWrite t ea v).jolt_device = t.jolt_device := rfl

/-- Four stores at consecutive doublewords write the list of the four values.
Example: storing `7, 9, 0, 1` at `0x8002_0000 + 8·k` for `k = 0, 1, 2, 3` gives
`writeDwords mem 0x8002_0000 [7, 9, 0, 1]`. -/
theorem memWrite_four (s : SailJoltState) (e : Nat) (v0 v1 v2 v3 : BitVec 64) :
    memWrite (memWrite (memWrite (memWrite s (e + 8 * 0) v0) (e + 8 * 1) v1) (e + 8 * 2) v2)
        (e + 8 * 3) v3 =
      { s with sail := { s.sail with mem := writeDwords s.sail.mem e [v0, v1, v2, v3] } } := by
  have h0 : e + 8 * 0 = e := by omega
  have h1 : e + 8 * 1 = e + 8 := by omega
  have h2 : e + 8 * 2 = e + 8 + 8 := by omega
  have h3 : e + 8 * 3 = e + 8 + 8 + 8 := by omega
  rw [h0, h1, h2, h3]
  rfl

/-- An `SD` to RAM from `{t with vregs := f}`, where `t` has the architectural registers of a
state `s₀` that reads the base: the run continues exactly when the doubleword is writable.
Example: `SD vr62, 0(x12)`. -/
theorem run_sd_vregs_iff {x : VReg} {r : regidx} {imm : BitVec 64} {s₀ : SailJoltState}
    {base : BitVec 64} (hr : XReads s₀ r base) {t : SailJoltState}
    (ht : t.sail.regs = s₀.sail.regs) (hram : RAM_START_ADDRESS ≤ (base + imm).toNat)
    (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (.SD (.xreg r) (.vreg x) imm :: rest)).Run { t with vregs := f } s' ↔
      DwordWritable t.jolt_device (base + imm).toNat ∧
        (Program.seq rest).Run { memWrite t (base + imm).toNat (f x) with vregs := f } s' := by
  rw [run_sd_iff (XReads.vregs f (XReads.of_regs ht.symm hr))]
  constructor
  · rintro ⟨t', ht', hrun⟩
    obtain ⟨hal, hok, rfl⟩ := storeDword?_ram_inv hram ht'
    exact ⟨⟨hal, hok⟩, hrun⟩
  · rintro ⟨⟨hal, hok⟩, hrun⟩
    exact ⟨_, storeDword?_ram _ hal hram hok, hrun⟩

/-- `readLimbs?` succeeds exactly when its four loads do.
Example: if the doublewords at `0x8001_0000 + 8i` are `1, 0, 0, 0`, the limbs read are
`#v[1, 0, 0, 0]`. -/
theorem readLimbs?_eq_some_iff (s : SailJoltState) (a : BitVec 64) (x : Limbs) :
    readLimbs? s a = some x ↔
      loadDword? s a = some x[0] ∧ loadDword? s (a + 8) = some x[1] ∧
        loadDword? s (a + 16) = some x[2] ∧ loadDword? s (a + 24) = some x[3] := by
  unfold readLimbs?
  cases h0 : loadDword? s a <;> cases h1 : loadDword? s (a + 8) <;>
    cases h2 : loadDword? s (a + 16) <;> cases h3 : loadDword? s (a + 24) <;>
    simp only [Option.bind_eq_bind, Option.pure_def,
      reduceCtorEq, Option.some.injEq, false_and, and_false, Option.bind]
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext i hi
    interval_cases i <;> rfl

/-- A `VirtualAdvice` row from `{s with vregs := f}` writes its word.
Example: `VirtualAdvice vr56, advice 0`. -/
theorem run_va_vregs_iff {d : VReg} (hd : 32 ≤ d.toNat) {v imm : BitVec 64} (s : SailJoltState)
    (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (.VirtualAdvice (.vreg d) v imm :: rest)).Run { s with vregs := f } s' ↔
      (Program.seq rest).Run { s with vregs := setV f d v } s' :=
  run_regRow_vregs_iff (i := .VirtualAdvice (.vreg d) v imm) rfl hd s f rest s'

/-- A `LUI` row from `{s with vregs := f}` writes its immediate.
Example: `LUI vr60, 0x1000003d1`. -/
theorem run_lui_vregs_iff {d : VReg} (hd : 32 ≤ d.toNat) {imm : BitVec 64} (s : SailJoltState)
    (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (.LUI (.vreg d) imm :: rest)).Run { s with vregs := f } s' ↔
      (Program.seq rest).Run { s with vregs := setV f d imm } s' :=
  run_regRow_vregs_iff (i := .LUI (.vreg d) imm) rfl hd s f rest s'

/-! ## The prologue -/

/-- The registers and values the constant rows write.
Example: for the base field, `[(p, 0x1000003d1)]`; for `MULQ`, `p = vr60`. -/
def constWrites (scalar : Bool) (L : MulRegs) : List (VReg × BitVec 64) :=
  if scalar then [(L.p, pPrimeScalar0), (L.p2, pPrimeScalar1)] else [(L.p, pPrimeBase)]

/-- **The constant rows.** From register file `f`, the `LUI` rows of `p'` run and write
`constWrites`.
Example: for `MULQ`, `LUI vr60, 0x1000003d1` sets `vr60`. -/
theorem run_constRows_iff {op : FieldOp} {scalar : Bool} {L : MulRegs} (hv : L.Valid op scalar)
    (s : SailJoltState) (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (constRows scalar L ++ rest)).Run { s with vregs := f } s' ↔
      (Program.seq rest).Run { s with vregs := writeAll f (constWrites scalar L) } s' := by
  have g := hv.pre_ge
  cases scalar
  · simp only [constRows, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
      run_lui_vregs_iff (g L.p (by cases op <;> simp [preRegs]))]
    exact Iff.rfl
  · simp only [constRows, ite_true, List.cons_append, List.nil_append,
      run_lui_vregs_iff (g L.p (by cases op <;> simp [preRegs])),
      run_lui_vregs_iff (g L.p2 (by cases op <;> simp [preRegs]))]
    exact Iff.rfl

/-- **The prologue of `MUL`.** From register file `f`, the operand loads, advice rows and
constant rows run exactly when both operands can be read, and they write `preWrites`.
Example: `MULQ` with `x10 = 0x8001_0000` and `x11 = 0x8001_0020` in readable RAM loads
`vr48..vr51` from `0x8001_0000` and `vr52..vr55` from `0x8001_0020`. -/
theorem run_prologue_mul_iff {scalar : Bool} {L : MulRegs} (hv : L.Valid .mul scalar)
    {rs1 rs2 : regidx} {advice : Nat → BitVec 64} {s : SailJoltState} {B1 B2 : BitVec 64}
    (h1 : XReads s rs1 B1) (h2 : XReads s rs2 B2) (f : VReg → BitVec 64)
    (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (prologueRows .mul L rs1 rs2 advice ++ constRows scalar L ++ rest)).Run
        { s with vregs := f } s' ↔
      ∃ x y : Limbs, readLimbs? s B1 = some x ∧ readLimbs? s B2 = some y ∧
        (Program.seq rest).Run
          { s with vregs := writeAll f (preWrites .mul scalar L x y advice) } s' := by
  have g := hv.pre_ge
  rw [List.append_assoc]
  simp only [prologueRows, ldRow, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, Nat.reduceMul,
    run_ld_vregs_iff (g (L.a 0) (by simp [preRegs])) h1,
    run_ld_vregs_iff (g (L.a 1) (by simp [preRegs])) h1,
    run_ld_vregs_iff (g (L.a 2) (by simp [preRegs])) h1,
    run_ld_vregs_iff (g (L.a 3) (by simp [preRegs])) h1,
    run_ld_vregs_iff (g (L.b 0) (by simp [preRegs])) h2,
    run_ld_vregs_iff (g (L.b 1) (by simp [preRegs])) h2,
    run_ld_vregs_iff (g (L.b 2) (by simp [preRegs])) h2,
    run_ld_vregs_iff (g (L.b 3) (by simp [preRegs])) h2,
    run_va_vregs_iff (g (L.w 0) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 1) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 2) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 3) (by simp [preRegs])),
    run_constRows_iff hv]
  constructor
  · rintro ⟨x0, hx0, y0, hy0, x1, hx1, y1, hy1, x2, hx2, y2, hy2, x3, hx3, y3, hy3, hrun⟩
    exact ⟨#v[x0, x1, x2, x3], #v[y0, y1, y2, y3],
      (readLimbs?_eq_some_iff _ _ _).2 ⟨by simpa using hx0, by simpa using hx1,
        by simpa using hx2, by simpa using hx3⟩,
      (readLimbs?_eq_some_iff _ _ _).2 ⟨by simpa using hy0, by simpa using hy1,
        by simpa using hy2, by simpa using hy3⟩, hrun⟩
  · rintro ⟨x, y, hx, hy, hrun⟩
    obtain ⟨hx0, hx1, hx2, hx3⟩ := (readLimbs?_eq_some_iff _ _ _).1 hx
    obtain ⟨hy0, hy1, hy2, hy3⟩ := (readLimbs?_eq_some_iff _ _ _).1 hy
    exact ⟨x[0], by simpa using hx0, y[0], by simpa using hy0, x[1], hx1, y[1], hy1,
      x[2], hx2, y[2], hy2, x[3], hx3, y[3], hy3, hrun⟩

/-- **The prologue of `SQUARE`.** From register file `f`, the operand loads, advice rows and
constant rows run exactly when the operand can be read, and they write `preWrites`.
Example: `SQUAREQ` with `x10 = 0x8001_0000` in readable RAM loads `vr48..vr51` from
`0x8001_0000`. -/
theorem run_prologue_square_iff {scalar : Bool} {L : MulRegs} (hv : L.Valid .square scalar)
    {rs1 rs2 : regidx} {advice : Nat → BitVec 64} {s : SailJoltState} {B1 : BitVec 64}
    (h1 : XReads s rs1 B1) (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (prologueRows .square L rs1 rs2 advice ++ constRows scalar L ++ rest)).Run
        { s with vregs := f } s' ↔
      ∃ x : Limbs, readLimbs? s B1 = some x ∧
        (Program.seq rest).Run
          { s with vregs := writeAll f (preWrites .square scalar L x x advice) } s' := by
  have g := hv.pre_ge
  rw [List.append_assoc]
  simp only [prologueRows, ldRow, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, Nat.reduceMul,
    run_ld_vregs_iff (g (L.a 0) (by simp [preRegs])) h1,
    run_ld_vregs_iff (g (L.a 1) (by simp [preRegs])) h1,
    run_ld_vregs_iff (g (L.a 2) (by simp [preRegs])) h1,
    run_ld_vregs_iff (g (L.a 3) (by simp [preRegs])) h1,
    run_va_vregs_iff (g (L.w 0) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 1) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 2) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 3) (by simp [preRegs])),
    run_constRows_iff hv]
  constructor
  · rintro ⟨x0, hx0, x1, hx1, x2, hx2, x3, hx3, hrun⟩
    exact ⟨#v[x0, x1, x2, x3],
      (readLimbs?_eq_some_iff _ _ _).2 ⟨by simpa using hx0, by simpa using hx1,
        by simpa using hx2, by simpa using hx3⟩, hrun⟩
  · rintro ⟨x, hx, hrun⟩
    obtain ⟨hx0, hx1, hx2, hx3⟩ := (readLimbs?_eq_some_iff _ _ _).1 hx
    exact ⟨x[0], by simpa using hx0, x[1], hx1, x[2], hx2, x[3], hx3, hrun⟩

/-! ## The columns -/

/-- The pool registers of a layout: `vr48` and the `count - 1` registers after it.
Example: for `MULQ`, `vr48..vr63`. -/
def MulRegs.pool (L : MulRegs) : List VReg := (List.range L.count).map fun i => vr (48 + i)

/-- The rows after the prologue and constant rows: the columns with their outputs, the top
column, the division stores, and the resets.
Example: for `MULQ` they start with `MUL vr62, vr48, vr52`. -/
def tailRows (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs3 : regidx) : List Instr :=
  col0Rows op L rs1 rs3 ++ ((List.range' 1 6).flatMap fun k => colKRows op scalar L rs1 rs3 k) ++
    finalRows L ++ (if op = .div then storeRows L rs3 else []) ++ resetRows L.pool

/-- `mulRows` is the prologue, the constant rows, and `tailRows`.
Example: for `MULQ`, 13 rows and then the rest. -/
theorem mulRows_eq_append (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs2 rs3 : regidx)
    (advice : Nat → BitVec 64) :
    mulRows op scalar L rs1 rs2 rs3 advice =
      prologueRows op L rs1 rs2 advice ++ constRows scalar L ++ tailRows op scalar L rs1 rs3 := by
  simp only [mulRows, tailRows, MulRegs.pool, List.append_assoc]

/-- For `MUL` and `SQUARE`, the output of columns 0 to 3 is a store to the output buffer.
Example: for `MULQ` (`mulqRegs`) with `rs3 = x12`, column 2 ends with `SD x12, vr62, 16`. -/
theorem outRows_store {op : FieldOp} (hop : op ≠ .div) (L : MulRegs) (rs1 rs3 : regidx)
    {k : Nat} (hk : k < 4) : outRows op L rs1 rs3 k = [sdRow rs3 (L.r k) (8 * k)] := by
  cases op
  · simp [outRows, hk]
  · simp [outRows, hk]
  · exact absurd rfl hop

/-- The output of columns 4 to 6 is a check against a quotient limb.
Example: for `mulqRegs`, column 4 ends with `VirtualAssertEQ vr62, vr56`. -/
theorem outRows_assert (op : FieldOp) (L : MulRegs) (rs1 rs3 : regidx) {k : Nat}
    (hk : ¬ k < 4) :
    outRows op L rs1 rs3 k = [.VirtualAssertEQ (.vreg (L.r k)) (.vreg (L.w (k - 4))) 0] := by
  simp [outRows, hk]

/-- A run of register rows to the end ends in their register file.
Example: `ADDI vr48, x0, 0` as the last row of `MULQ`. -/
theorem run_regs_end_iff {l : List Instr} {f g : VReg → BitVec 64} (h : regRun l f = some g)
    (s s' : SailJoltState) :
    (Program.seq l).Run { s with vregs := f } s' ↔ s' = { s with vregs := g } := by
  have := run_regs_vregs_iff h s [] s'
  rw [List.append_nil] at this
  rw [this, run_nil_iff]

/-- A column's terms have the same value in every register file that agrees on the operand
registers.
Example: column 1 of `MULQ` has the same sum in two files that agree on `vr48..vr60`. -/
theorem colSum_congr {op : FieldOp} {scalar : Bool} {L : MulRegs} {k : Nat}
    (hops : ∀ m ∈ colTerms op scalar L k, ∀ r ∈ m.ops, L.OpFree r) {F G : VReg → BitVec 64}
    (h : ∀ r, L.OpFree r → G r = F r) :
    ((colTerms op scalar L k).map (Mac.val G)).sum = colSum op scalar L F k := by
  unfold colSum
  congr 1
  apply List.map_congr_left
  intro m hm
  exact Mac.val_congr m (fun r hr => h r (hops m hm r hr))

/-- One column `k` of `1..6`, from a register file `G` that agrees with `F` on the operands:
the column's register rows end in a file `G'` that still agrees with `F`, and
`R + 2^64·C' = C + colSum k`, where `C`, `C'` are the carries in and out and `R` the column.
Example: column 1 of `MULQ` adds five terms into `vr63` and `vr62`. -/
theorem col_step {op : FieldOp} {scalar : Bool} {L : MulRegs} (hv : L.Valid op scalar)
    {k : Nat} (hk : k ∈ List.range' 1 6) {F G : VReg → BitVec 64}
    (hG : ∀ r, L.OpFree r → G r = F r) :
    ∃ G', regRun (colRows (L.col k) true (colTerms op scalar L k)) G = some G' ∧
      (G' (L.r k)).toNat + 2 ^ 64 * (G' (L.r (k + 1))).toNat =
        (G (L.r k)).toNat + colSum op scalar L F k ∧
      ∀ r, L.OpFree r → G' r = F r := by
  obtain ⟨hpos, hlen, hops⟩ := hv.terms k hk
  obtain ⟨G', hrun, heq, -, hfr⟩ := colRows_spec (MulRegs.col_valid hv k) (colTerms op scalar L k)
    (List.ne_nil_of_length_pos hpos) (fun m hm r hr => MulRegs.col_free (hops m hm r hr) k)
    hlen G
  refine ⟨G', hrun, ?_, fun r hr => (hfr r (MulRegs.col_free hr k)).trans (hG r hr)⟩
  rw [← colSum_congr hops hG]
  exact heq

/-- A `k`-th output address is `out + 8k` when the four outputs do not wrap.
Example: `0x80020000 + 16`. -/
theorem out_addr {out : BitVec 64} (hwrap : out.toNat + 32 ≤ 2 ^ 64) {k : Nat} (hk : k < 4) :
    (out + BitVec.ofNat 64 (8 * k)).toNat = out.toNat + 8 * k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : 8 * k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

/-- No overflow in `x + y` is the same as `y ≤ x + y`. Example: `x = 2^64 - 1`, `y = 1` wraps
to `0 < 1`. -/
theorem toNat_add_of_le {x y : BitVec 64} (h : y.toNat ≤ (x + y).toNat) :
    (x + y).toNat = x.toNat + y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_add] at h ⊢
  omega

/-- **The rows after the prologue, for `MUL` and `SQUARE`.** From register file `F`, with the
output buffer `out` in RAM, the rows compute column values `R0, …, R6` and a top carry `C` with

`R0 + 2^64·R1 + … + 2^384·R6 + 2^448·(C + hi(a3·b3)) = colTotal F`.

They run exactly when the four output doublewords are writable, `R4, R5, R6` equal the
quotient limbs `w0, w1, w2`, and `C + hi(a3·b3)` equals `w3` without overflow; the run stores
`R0, …, R3` at `out`.
Example: for `MULQ` with `a = 2`, `b = (p+1)/2` and Jolt's quotient `w = 1`, the columns are
`1, 0, 0, 0, 1, 0, 0` and the top column is `0`. -/
theorem run_tail_iff {op : FieldOp} {scalar : Bool} {L : MulRegs} (hop : op ≠ .div)
    (hv : L.Valid op scalar) {rs1 rs3 : regidx} {s : SailJoltState} {out : BitVec 64}
    (h3 : XReads s rs3 out) (hram : RAM_START_ADDRESS ≤ out.toNat)
    (hwrap : out.toNat + 32 ≤ 2 ^ 64) (F : VReg → BitVec 64) :
    ∃ R0 R1 R2 R3 R4 R5 R6 C : BitVec 64, ∃ V : VReg → BitVec 64,
      R0.toNat + 2 ^ 64 * R1.toNat + 2 ^ 128 * R2.toNat + 2 ^ 192 * R3.toNat +
          2 ^ 256 * R4.toNat + 2 ^ 320 * R5.toNat + 2 ^ 384 * R6.toNat +
          2 ^ 448 * (C.toNat + (jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat) =
        colTotal op scalar L F ∧
      ∀ s', (Program.seq (tailRows op scalar L rs1 rs3)).Run { s with vregs := F } s' ↔
        (∀ k < 4, DwordWritable s.jolt_device (out.toNat + 8 * k)) ∧
        R4 = F (L.w 0) ∧ R5 = F (L.w 1) ∧ R6 = F (L.w 2) ∧
        C + jolt_mulhu_value (F (L.a 3)) (F (L.b 3)) = F (L.w 3) ∧
        (jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat ≤
          (C + jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat ∧
        s' = { s with vregs := V,
                      sail := { s.sail with
                        mem := writeDwords s.sail.mem out.toNat [R0, R1, R2, R3] } } := by
  -- The operand registers are never column registers.
  have oa : ∀ i, i < 4 → L.OpFree (L.a i) := by
    intro i hi
    apply hv.pre_free
    interval_cases i <;> cases op <;> cases scalar <;> simp [preRegs]
  have ow : ∀ i, i < 4 → L.OpFree (L.w i) := by
    intro i hi
    apply hv.pre_free
    interval_cases i <;> cases op <;> cases scalar <;> simp [preRegs]
  have ob : ∀ i, i < 4 → L.OpFree (L.b i) := by
    intro i hi
    cases op
    · apply hv.pre_free
      interval_cases i <;> cases scalar <;> simp [preRegs]
    · rw [hv.square rfl]; exact oa i hi
    · exact absurd rfl hop
  have opp : L.OpFree L.p := by
    apply hv.pre_free
    cases op <;> cases scalar <;> simp [preRegs]
  have c0 : 32 ≤ L.r0.toNat ∧ 32 ≤ L.r1.toNat ∧ 32 ≤ L.aux.toNat ∧ 32 ≤ L.aux2.toNat ∧
      L.r0 ≠ L.r1 ∧ L.aux ≠ L.r0 ∧ L.aux ≠ L.r1 ∧ L.aux2 ≠ L.r0 ∧ L.aux2 ≠ L.r1 ∧
      L.aux ≠ L.aux2 := hv.col0
  have free : ∀ {r}, L.OpFree r → r ≠ L.r0 ∧ r ≠ L.r1 ∧ r ≠ L.aux ∧ r ≠ L.aux2 :=
    fun h => h
  -- Column 0: `MUL r0, a0, b0`, then the term `lo(w0·p)`.
  obtain ⟨g0, hg0, e0, -, fr0⟩ := colRows_spec hv.col0 [.low (L.w 0) L.p] (by simp)
    (by
      intro m hm r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      simp only [Mac.ops, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ow 0 (by decide)
      · exact opp)
    (by simp) (setV F L.r0 (F (L.a 0) * F (L.b 0)))
  have A0 : ∀ r, L.OpFree r → g0 r = F r := fun r hr =>
    (fr0 r hr).trans (setV_ne _ _ (free hr).1)
  have e0' : (g0 L.r0).toNat + 2 ^ 64 * (g0 L.r1).toNat =
      (F (L.a 0) * F (L.b 0)).toNat + (F (L.w 0) * F L.p).toNat := by
    have hc1 : (L.col 0).c1 = L.r0 := rfl
    have hc2 : (L.col 0).c2 = L.r1 := rfl
    rw [hc1, hc2] at e0
    have h : (g0 L.r0).toNat + 2 ^ 64 * (g0 L.r1).toNat =
        (setV F L.r0 (F (L.a 0) * F (L.b 0)) L.r0).toNat +
          (setV F L.r0 (F (L.a 0) * F (L.b 0)) (L.w 0) *
            setV F L.r0 (F (L.a 0) * F (L.b 0)) L.p).toNat := by
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mac.val,
        Nat.add_zero] using e0
    rwa [setV_same, setV_ne _ _ (free (ow 0 (by decide))).1, setV_ne _ _ (free opp).1] at h
  -- Columns 1 to 6.
  obtain ⟨g1, hg1, e1, A1⟩ := col_step hv (k := 1) (by decide) A0
  obtain ⟨g2, hg2, e2, A2⟩ := col_step hv (k := 2) (by decide) A1
  obtain ⟨g3, hg3, e3, A3⟩ := col_step hv (k := 3) (by decide) A2
  obtain ⟨g4, hg4, e4, A4⟩ := col_step hv (k := 4) (by decide) A3
  obtain ⟨g5, hg5, e5, A5⟩ := col_step hv (k := 5) (by decide) A4
  obtain ⟨g6, hg6, e6, A6⟩ := col_step hv (k := 6) (by decide) A5
  have e1' : (g1 L.r1).toNat + 2 ^ 64 * (g1 L.r0).toNat =
      (g0 L.r1).toNat + colSum op scalar L F 1 := e1
  have e2' : (g2 L.r0).toNat + 2 ^ 64 * (g2 L.r1).toNat =
      (g1 L.r0).toNat + colSum op scalar L F 2 := e2
  have e3' : (g3 L.r1).toNat + 2 ^ 64 * (g3 L.r0).toNat =
      (g2 L.r1).toNat + colSum op scalar L F 3 := e3
  have e4' : (g4 L.r0).toNat + 2 ^ 64 * (g4 L.r1).toNat =
      (g3 L.r0).toNat + colSum op scalar L F 4 := e4
  have e5' : (g5 L.r1).toNat + 2 ^ 64 * (g5 L.r0).toNat =
      (g4 L.r1).toNat + colSum op scalar L F 5 := e5
  have e6' : (g6 L.r0).toNat + 2 ^ 64 * (g6 L.r1).toNat =
      (g5 L.r0).toNat + colSum op scalar L F 6 := e6
  -- The top column and the resets.
  have hH : jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3)) =
      jolt_mulhu_value (F (L.a 3)) (F (L.b 3)) := by
    rw [A6 _ (oa 3 (by decide)), A6 _ (ob 3 (by decide))]
  have hpool : ∀ r ∈ L.pool, 32 ≤ r.toNat := by
    intro r hr
    simp only [MulRegs.pool, List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    exact hv.pool i hi
  obtain ⟨V, hV, -⟩ := resetRows_spec L.pool hpool
    (setV (setV g6 L.aux (jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3)))) L.r1
      (setV g6 L.aux (jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3))) L.r1 +
        setV g6 L.aux (jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3))) L.aux))
  refine ⟨g0 L.r0, g1 L.r1, g2 L.r0, g3 L.r1, g4 L.r0, g5 L.r1, g6 L.r0, g6 L.r1, V, ?_,
    fun s' => ?_⟩
  · unfold colTotal
    omega
  -- The run, row group by row group.
  have hb : ∀ k, k < 4 → RAM_START_ADDRESS ≤ (out + BitVec.ofNat 64 (8 * k)).toNat :=
    fun k hk => by rw [out_addr hwrap hk]; omega
  simp only [tailRows, col0Rows, colKRows, List.range', List.flatMap_cons, List.flatMap_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil, hop, ite_false,
    outRows_store hop L rs1 rs3 (show 0 < 4 by decide),
    outRows_store hop L rs1 rs3 (show 1 < 4 by decide),
    outRows_store hop L rs1 rs3 (show 2 < 4 by decide),
    outRows_store hop L rs1 rs3 (show 3 < 4 by decide),
    outRows_assert op L rs1 rs3 (show ¬ 4 < 4 by decide),
    outRows_assert op L rs1 rs3 (show ¬ 5 < 4 by decide),
    outRows_assert op L rs1 rs3 (show ¬ 6 < 4 by decide),
    finalRows, sdRow, Nat.reduceAdd, Nat.reduceSub]
  rw [run_regRow_vregs_iff (i := .MUL (.vreg L.r0) (.vreg (L.a 0)) (.vreg (L.b 0))) rfl c0.1,
    run_regs_vregs_iff hg0, run_sd_vregs_iff h3 rfl (hb 0 (by decide)),
    run_regs_vregs_iff hg1, run_sd_vregs_iff h3 (memWrite_regs rfl _ _) (hb 1 (by decide)),
    run_regs_vregs_iff hg2,
    run_sd_vregs_iff h3 (memWrite_regs (memWrite_regs rfl _ _) _ _) (hb 2 (by decide)),
    run_regs_vregs_iff hg3,
    run_sd_vregs_iff h3 (memWrite_regs (memWrite_regs (memWrite_regs rfl _ _) _ _) _ _)
      (hb 3 (by decide)),
    run_regs_vregs_iff hg4, run_assertEq_iff,
    run_regs_vregs_iff hg5, run_assertEq_iff,
    run_regs_vregs_iff hg6, run_assertEq_iff,
    run_regRow_vregs_iff (i := .MULHU (.vreg L.aux) (.vreg (L.a 3)) (.vreg (L.b 3))) rfl c0.2.2.1,
    run_regRow_vregs_iff (i := .ADD (.vreg L.r1) (.vreg L.r1) (.vreg L.aux)) rfl c0.2.1,
    run_assertEq_iff, run_assertLTE_iff]
  rw [run_regs_end_iff hV]
  simp only [memWrite_jolt_device]
  rw [out_addr hwrap (k := 0) (by decide), out_addr hwrap (k := 1) (by decide),
    out_addr hwrap (k := 2) (by decide), out_addr hwrap (k := 3) (by decide), memWrite_four]
  have r0e : L.r 0 = L.r0 := rfl
  have r1e : L.r 1 = L.r1 := rfl
  have r2e : L.r 2 = L.r0 := rfl
  have r3e : L.r 3 = L.r1 := rfl
  have r4e : L.r 4 = L.r0 := rfl
  have r5e : L.r 5 = L.r1 := rfl
  have r6e : L.r 6 = L.r0 := rfl
  have fw3 := free (ow 3 (by decide))
  have nar1 : L.aux ≠ L.r1 := c0.2.2.2.2.2.2.1
  simp only [r0e, r1e, r2e, r3e, r4e, r5e, r6e, setV_same, setV_ne _ _ (Ne.symm nar1),
    setV_ne _ _ nar1, setV_ne _ _ fw3.2.1, setV_ne _ _ fw3.2.2.1, hH,
    A4 _ (ow 0 (by decide)), A5 _ (ow 1 (by decide)), A6 _ (ow 2 (by decide)),
    A6 _ (ow 3 (by decide))]
  constructor
  · rintro ⟨w0, w1, w2, w3, rest⟩
    refine ⟨fun k hk => ?_, rest⟩
    interval_cases k
    · simpa using w0
    · exact w1
    · exact w2
    · exact w3
  · rintro ⟨hw, rest⟩
    exact ⟨by simpa using hw 0 (by decide), hw 1 (by decide), hw 2 (by decide),
      hw 3 (by decide), rest⟩

/-! ## The register file after the prologue, in values -/

/-- After the prologue, the limb registers hold the operands and the advice, and `p` (and `p2`)
hold `p'`. For squaring, `y` is `x`.
Example: for `MULQ`, `vr48..vr51` hold the limbs of `a` and `vr56..vr59` the advice words. -/
theorem pre_vals {op : FieldOp} {scalar : Bool} {L : MulRegs} (hop : op ≠ .div)
    (hv : L.Valid op scalar) {x y : Limbs} (hy : op = .square → y = x)
    (advice : Nat → BitVec 64) (f : VReg → BitVec 64) :
    limbVal L.a (writeAll f (preWrites op scalar L x y advice)) = limbsToNat x ∧
    limbVal L.b (writeAll f (preWrites op scalar L x y advice)) = limbsToNat y ∧
    (∀ i, i < 4 → writeAll f (preWrites op scalar L x y advice) (L.w i) = advice i) ∧
    writeAll f (preWrites op scalar L x y advice) L.p =
      (if scalar then pPrimeScalar0 else pPrimeBase) ∧
    (scalar = true → writeAll f (preWrites op scalar L x y advice) L.p2 = pPrimeScalar1) := by
  have key : ∀ d v, (d, v) ∈ preWrites op scalar L x y advice →
      writeAll f (preWrites op scalar L x y advice) d = v := fun d v h =>
    writeAll_of_mem f (by rw [preWrites_fst]; exact hv.pre_nodup) h
  cases op
  · have a : ∀ i (hi : i < 4), writeAll f (preWrites .mul scalar L x y advice) (L.a i) = x[i] := by
      intro i hi
      interval_cases i <;> exact key _ _ (by simp [preWrites])
    have b : ∀ i (hi : i < 4), writeAll f (preWrites .mul scalar L x y advice) (L.b i) = y[i] := by
      intro i hi
      interval_cases i <;> exact key _ _ (by simp [preWrites])
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [limbVal, limbsToNat, a 0 (by decide), a 1 (by decide), a 2 (by decide),
        a 3 (by decide)]
    · simp only [limbVal, limbsToNat, b 0 (by decide), b 1 (by decide), b 2 (by decide),
        b 3 (by decide)]
    · intro i hi
      interval_cases i <;> exact key _ _ (by simp [preWrites])
    · cases scalar <;> exact key _ _ (by simp [preWrites])
    · rintro rfl
      exact key _ _ (by simp [preWrites])
  · rw [hy rfl] at key ⊢
    have hb := hv.square rfl
    have a : ∀ i (hi : i < 4),
        writeAll f (preWrites .square scalar L x x advice) (L.a i) = x[i] := by
      intro i hi
      interval_cases i <;> exact key _ _ (by simp [preWrites])
    have ha : limbVal L.a (writeAll f (preWrites .square scalar L x x advice)) =
        limbsToNat x := by
      simp only [limbVal, limbsToNat, a 0 (by decide), a 1 (by decide), a 2 (by decide),
        a 3 (by decide)]
    refine ⟨ha, by rw [hb]; exact ha, ?_, ?_, ?_⟩
    · intro i hi
      interval_cases i <;> exact key _ _ (by simp [preWrites])
    · cases scalar <;> exact key _ _ (by simp [preWrites])
    · rintro rfl
      exact key _ _ (by simp [preWrites])
  · exact absurd rfl hop

/-- A run of the rows after the prologue reads `rs3`: the first output store reads it.
Example: `MULQ` with `rs3 = x12` and `x12 = 0x8002_0000` reads `x12` at its first store. -/
theorem tail_reads3 {op : FieldOp} {scalar : Bool} {L : MulRegs} (hop : op ≠ .div)
    (hv : L.Valid op scalar) {rs1 rs3 : regidx} {s s' : SailJoltState} {F : VReg → BitVec 64}
    (h : (Program.seq (tailRows op scalar L rs1 rs3)).Run { s with vregs := F } s') :
    XReads s rs3 (sourceValue (.xreg rs3) s) := by
  obtain ⟨g0, hg0, -⟩ := colRows_spec hv.col0 [.low (L.w 0) L.p] (by simp)
    (by
      intro m hm r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      simp only [Mac.ops, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact MulRegs.col_free (hv.pre_free _ (by cases op <;> cases scalar <;> simp [preRegs])) 0)
    (by simp) (setV F L.r0 (F (L.a 0) * F (L.b 0)))
  simp only [tailRows, col0Rows, List.cons_append, List.append_assoc,
    outRows_store hop L rs1 rs3 (show 0 < 4 by decide), sdRow] at h
  rw [run_regRow_vregs_iff (i := .MUL (.vreg L.r0) (.vreg (L.a 0)) (.vreg (L.b 0))) rfl
    (hv.col0.1 : 32 ≤ L.r0.toNat), run_regs_vregs_iff hg0] at h
  exact XReads.of_run_sd (s := { s with vregs := g0 }) h

/-! ## The specification -/

/-- The output buffer of a field multiplication: the address in `rs3`.
Example: `0x8002_0000` when `x12 = 0x8002_0000` and `rs3 = x12`. -/
abbrev fieldOut (rs3 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs3) s

/-- Where the output buffer must lie for soundness: in RAM, with its 32 bytes below `2^64`.
Example: a buffer at `0x8002_0000`. -/
structure FieldMulBuffer (rs3 : regidx) (s : SailJoltState) : Prop where
  ram : RAM_START_ADDRESS ≤ (fieldOut rs3 s).toNat
  no_wrap : (fieldOut rs3 s).toNat + 32 ≤ 2 ^ 64

/-- The value-level result of a call of `MUL` (`op = .mul`) or `SQUARE` (`op = .square`) modulo
`q`: the operands `a` (at `rs1`) and `b` (at `rs2`, or `a` again for squaring) read from
memory, and some `w` and `c` with `a·b = w·q + c`, both below `2^256`. The call stores `c` at
the output buffer, changes only virtual registers otherwise, and `c` reads back.
Example: for `MULQ` with `a = 2` and `b = (p+1)/2`, `a·b = p + 1`, so `w = 1` and `c = 1`
satisfy it, and so do `w = 0`, `c = p + 1`. -/
def FieldMulSpec (q : Nat) (op : FieldOp) (rs1 rs2 rs3 : regidx) (s s' : SailJoltState) :
    Prop :=
  ∃ a b w c : Limbs,
    readLimbs? s (sourceValue (.xreg rs1) s) = some a ∧
    (op = .square → b = a) ∧
    (op ≠ .square → readLimbs? s (sourceValue (.xreg rs2) s) = some b) ∧
    MulRel q (limbsToNat a) (limbsToNat b) (limbsToNat w) (limbsToNat c) ∧
    (∃ V : VReg → BitVec 64,
      s' = { s with vregs := V,
                    sail := { s.sail with
                      mem := writeDwords s.sail.mem (fieldOut rs3 s).toNat c.toList } }) ∧
    ∀ i < 4, loadDword? s' (fieldOut rs3 s + BitVec.ofNat 64 (8 * i)) = c.toList[i]?

/-- **Soundness of the `MUL` and `SQUARE` rows.** Every run of the rows, for every advice, from a
state whose output buffer lies in RAM, meets `FieldMulSpec` for the modulus of the layout.
Example: for `MULQ` with `a = 2` and `b = (p+1)/2`, every run stores some `c ≡ 1 (mod p)`. -/
theorem mulRows_sound {op : FieldOp} {scalar : Bool} {L : MulRegs} (hop : op ≠ .div)
    (hv : L.Valid op scalar) {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (Program.seq (mulRows op scalar L rs1 rs2 rs3 advice)).Run s s') :
    FieldMulSpec (if scalar then n else p) op rs1 rs2 rs3 s s' := by
  rw [mulRows_eq_append] at run
  -- The prologue: read the operands.
  obtain ⟨x, y, hx, hy, hsq, tail⟩ : ∃ x y : Limbs,
      readLimbs? s (sourceValue (.xreg rs1) s) = some x ∧
      (op ≠ .square → readLimbs? s (sourceValue (.xreg rs2) s) = some y) ∧
      (op = .square → y = x) ∧
      (Program.seq (tailRows op scalar L rs1 rs3)).Run
        { s with vregs := writeAll s.vregs (preWrites op scalar L x y advice) } s' := by
    have h1 : XReads s rs1 (sourceValue (.xreg rs1) s) := by
      have h := run
      cases op <;> first
        | exact absurd rfl hop
        | (simp only [prologueRows, List.flatMap_cons, ldRow, List.cons_append] at h
           exact XReads.of_run_ld h)
    change (Program.seq _).Run { s with vregs := s.vregs } s' at run
    cases op
    · have h2 : XReads s rs2 (sourceValue (.xreg rs2) s) := by
        have h := run
        simp only [prologueRows, List.flatMap_cons, ldRow, List.cons_append] at h
        rw [run_ld_vregs_iff (hv.pre_ge _ (by simp [preRegs])) h1] at h
        obtain ⟨v0, _, h⟩ := h
        exact XReads.of_run_ld (s := { s with vregs := setV s.vregs (L.a 0) v0 }) h
      obtain ⟨x, y, hx, hy, h⟩ := (run_prologue_mul_iff hv h1 h2 _ _ _).1 run
      exact ⟨x, y, hx, fun _ => hy, fun h => absurd h (by decide), h⟩
    · obtain ⟨x, hx, h⟩ := (run_prologue_square_iff hv h1 _ _ _).1 run
      exact ⟨x, x, hx, fun h => absurd rfl h, fun _ => rfl, h⟩
    · exact absurd rfl hop
  -- The columns.
  obtain ⟨fa, fb, -, fp, fp2⟩ := pre_vals hop hv hsq advice s.vregs
  have h3 := tail_reads3 hop hv tail
  obtain ⟨R0, R1, R2, R3, R4, R5, R6, C, V, heq, hiff⟩ :=
    run_tail_iff hop hv h3 buf.ram buf.no_wrap (writeAll s.vregs (preWrites op scalar L x y advice))
  obtain ⟨hw, e4, e5, e6, e7, hle, rfl⟩ := (hiff s').1 tail
  have hct := colTotal_eq hv.square fp fp2
  set F := writeAll s.vregs (preWrites op scalar L x y advice)
  set H := jolt_mulhu_value (F (L.a 3)) (F (L.b 3))
  have hCH := toNat_add_of_le hle
  rw [e7] at hCH
  have hW : limbVal L.w F = limbsToNat #v[F (L.w 0), F (L.w 1), F (L.w 2), F (L.w 3)] := rfl
  have hc : limbsToNat #v[R0, R1, R2, R3] =
      R0.toNat + 2 ^ 64 * R1.toNat + 2 ^ 128 * R2.toNat + 2 ^ 192 * R3.toNat := rfl
  have hq : (if scalar then n else p) ≤ 2 ^ 256 := by cases scalar <;> decide
  refine ⟨x, y, #v[F (L.w 0), F (L.w 1), F (L.w 2), F (L.w 3)], #v[R0, R1, R2, R3], hx,
    hsq, hy, ⟨?_, limbsToNat_lt _, limbsToNat_lt _⟩, ⟨V, rfl⟩, fun i hi => ?_⟩
  · rw [← rows_identity_iff _ _ _ _ _ hq, ← fa, ← fb, ← hW, hc, ← hct, ← heq]
    simp only [limbVal]
    subst e4 e5 e6
    omega
  · let m' := writeDwords s.sail.mem (fieldOut rs3 s).toNat (#v[R0, R1, R2, R3] : Limbs).toList
    exact loadDword?_of_mem_writeDwords
      (t := { s with vregs := V, sail := { s.sail with mem := m' } }) rfl buf.ram
      (by simpa using buf.no_wrap)
      (fun j hj => hw j (by simpa using hj)) (by simpa using hi)

/-! ## Completeness with Jolt's advice -/

/-- The caller's obligations for a `MUL` or `SQUARE` call: the buffer conditions, readable
`rs1`, `rs2` (unless squaring) and `rs3`, and four aligned doublewords that Jolt may store to.
Example: operands at `0x8002_0000` and `0x8002_0020`, output at `0x8002_0040`. -/
structure FieldMulPre (op : FieldOp) (rs1 rs2 rs3 : regidx) (s : SailJoltState) : Prop
    extends FieldMulBuffer rs3 s where
  reads1 : XReads s rs1 (sourceValue (.xreg rs1) s)
  reads2 : op ≠ .square → XReads s rs2 (sourceValue (.xreg rs2) s)
  reads3 : XReads s rs3 (fieldOut rs3 s)
  writable : ∀ k < 4, DwordWritable s.jolt_device ((fieldOut rs3 s).toNat + 8 * k)

/-- Jolt's quotient `w` as row advice: `VirtualAdvice` row `i` writes limb `i` of `w`, the
word `(quotientWords w)[i]`.
Example: `quotientAdvice (natToLimbs 1) 0 = 1`, and every index from `4` on gives `0`. -/
def quotientAdvice (w : Limbs) (i : Nat) : BitVec 64 :=
  if h : i < 4 then w[i] else 0

/-- The output is canonical: the stored result `c` is below `q`.
Example: for `MULQ` with `a·b = p + 1`, the stored result is `1`, not `p + 1`. -/
def FieldMulCanonical (q : Nat) (rs3 : regidx) (s s' : SailJoltState) : Prop :=
  ∃ c : Limbs, Canonical q (limbsToNat c) ∧
    ∀ i < 4, loadDword? s' (fieldOut rs3 s + BitVec.ofNat 64 (8 * i)) = c.toList[i]?

/-- **Completeness of the `MUL` and `SQUARE` rows with Jolt's advice.** For a call that meets
its obligations, with operands `a` and `b` (for squaring, `b = a`) for which Jolt's quotient
advice `w = ⌊a·b / q⌋` exists, the rows run with that advice; the end state meets the
specification, and the stored result is `a·b mod q`, which is below `q`.
Example: for `MULQ` with `a = 2` and `b = (p+1)/2`, the rows run with `w = 1` and store `1`. -/
theorem mulRows_jolt_advice_complete {op : FieldOp} {scalar : Bool} {L : MulRegs}
    (hop : op ≠ .div) (hv : L.Valid op scalar) {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre op rs1 rs2 rs3 s) {a b w : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a)
    (hb : op ≠ .square → readLimbs? s (sourceValue (.xreg rs2) s) = some b)
    (hsq : op = .square → b = a)
    (hw : mulqQuotientAdvice (if scalar then n else p) a b = some w) :
    ∃ s', (Program.seq (mulRows op scalar L rs1 rs2 rs3 (quotientAdvice w))).Run s s' ∧
      FieldMulSpec (if scalar then n else p) op rs1 rs2 rs3 s s' ∧
      FieldMulCanonical (if scalar then n else p) rs3 s s' := by
  set q := if scalar then n else p with hqdef
  have hq : q ≤ 2 ^ 256 := by rw [hqdef]; cases scalar <;> decide
  have hq0 : 0 < q := by rw [hqdef]; cases scalar <;> decide
  -- Jolt's quotient.
  have hwv : limbsToNat w = limbsToNat a * limbsToNat b / q := by
    simp only [mulqQuotientAdvice, fieldLimbs?] at hw
    split at hw
    · cases hw
      rw [limbsToNat_natToLimbs, Nat.mod_eq_of_lt ‹_›]
    · cases hw
  -- The register file after the prologue.
  obtain ⟨fa, fb, fw, fp, fp2⟩ := pre_vals hop hv (fun h => hsq h) (quotientAdvice w) s.vregs
  set F := writeAll s.vregs (preWrites op scalar L a b (quotientAdvice w))
  have hW : limbVal L.w F = limbsToNat w := by
    simp only [limbVal, limbsToNat, fw 0 (by decide), fw 1 (by decide), fw 2 (by decide),
      fw 3 (by decide), quotientAdvice]
    rfl
  have hct := colTotal_eq hv.square fp fp2
  obtain ⟨R0, R1, R2, R3, R4, R5, R6, C, V, heq, hiff⟩ :=
    run_tail_iff hop hv pre.reads3 pre.ram pre.no_wrap F
  set H := jolt_mulhu_value (F (L.a 3)) (F (L.b 3))
  -- The digits of the column sum.
  have hc0 : limbsToNat a * limbsToNat b % q < q := Nat.mod_lt _ hq0
  have hid : limbsToNat a * limbsToNat b + limbsToNat w * pPrime q =
      limbsToNat a * limbsToNat b % q + 2 ^ 256 * limbsToNat w := by
    rw [rows_identity_iff _ _ _ _ _ hq, hwv]
    exact (Nat.div_add_mod' _ _).symm
  rw [hct, fa, fb, hW, hid] at heq
  have hw0 := (F (L.w 0)).isLt
  have hw1 := (F (L.w 1)).isLt
  have hw2 := (F (L.w 2)).isLt
  have hw3 := (F (L.w 3)).isLt
  have hwF : limbsToNat w = (F (L.w 0)).toNat + 2 ^ 64 * (F (L.w 1)).toNat +
      2 ^ 128 * (F (L.w 2)).toNat + 2 ^ 192 * (F (L.w 3)).toNat := by
    rw [← hW]; rfl
  have r0 := R0.isLt
  have r1 := R1.isLt
  have r2 := R2.isLt
  have r3 := R3.isLt
  have r4 := R4.isLt
  have r5 := R5.isLt
  have r6 := R6.isLt
  have hC := C.isLt
  have hH := H.isLt
  have hsplit : R0.toNat + 2 ^ 64 * R1.toNat + 2 ^ 128 * R2.toNat + 2 ^ 192 * R3.toNat =
        limbsToNat a * limbsToNat b % q ∧
      R4.toNat + 2 ^ 64 * R5.toNat + 2 ^ 128 * R6.toNat + 2 ^ 192 * (C.toNat + H.toNat) =
        limbsToNat w := by
    omega
  have d4 : R4.toNat = (F (L.w 0)).toNat := by omega
  have d5 : R5.toNat = (F (L.w 1)).toNat := by omega
  have d6 : R6.toNat = (F (L.w 2)).toNat := by omega
  have d7 : C.toNat + H.toNat = (F (L.w 3)).toNat := by omega
  have hCH : (C + H).toNat = C.toNat + H.toNat := by
    rw [BitVec.toNat_add]; omega
  -- The run.
  set m1 := writeDwords s.sail.mem (fieldOut rs3 s).toNat [R0, R1, R2, R3]
  set s1 : SailJoltState := { s with vregs := V, sail := { s.sail with mem := m1 } }
  have tail := (hiff s1).2 ⟨pre.writable, BitVec.eq_of_toNat_eq d4, BitVec.eq_of_toNat_eq d5,
    BitVec.eq_of_toNat_eq d6, BitVec.eq_of_toNat_eq (by rw [hCH, d7]), by omega, rfl⟩
  have run : (Program.seq (mulRows op scalar L rs1 rs2 rs3 (quotientAdvice w))).Run s s1 := by
    rw [mulRows_eq_append]
    cases op
    · exact (run_prologue_mul_iff hv pre.reads1 (pre.reads2 (by decide)) _ _ _).2
        ⟨a, b, ha, hb (by decide), tail⟩
    · have e : F = writeAll s.vregs (preWrites .square scalar L a a (quotientAdvice w)) := by
        simp only [F, hsq rfl]
      rw [e] at tail
      exact (run_prologue_square_iff hv pre.reads1 _ _ _).2 ⟨a, ha, tail⟩
    · exact absurd rfl hop
  refine ⟨s1, run, mulRows_sound hop hv pre.toFieldMulBuffer run,
    #v[R0, R1, R2, R3], ?_, fun i hi => ?_⟩
  · show limbsToNat #v[R0, R1, R2, R3] < q
    have : limbsToNat #v[R0, R1, R2, R3] =
        R0.toNat + 2 ^ 64 * R1.toNat + 2 ^ 128 * R2.toNat + 2 ^ 192 * R3.toNat := rfl
    omega
  · exact loadDword?_of_mem_writeDwords (t := s1) rfl pre.ram (by simpa using pre.no_wrap)
      (fun j hj => pre.writable j (by simpa using hj)) (by simpa using hi)

/-- Row advice from a word list, as the trace reads it: word `i`, or `0` past the end, is the
same as `quotientAdvice` for the quotient's words.
Example: for `w = natToLimbs 1`, both give `1, 0, 0, 0, 0, …`. -/
theorem getD_quotientWords (w : Limbs) :
    (fun i => (quotientWords w).getD i 0) = quotientAdvice w := by
  funext i
  unfold quotientAdvice quotientWords
  split
  · simp [*]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

/-- **Completeness for operands below the modulus.** When both operands are below `q`, Jolt's
quotient advice exists, and the rows run with it as in `mulRows_jolt_advice_complete`.
Example: for `MULQ` with `a = 2` and `b = (p+1)/2`, the rows run with `w = 1` and store `1`. -/
theorem mulRows_jolt_advice_complete_of_lt {op : FieldOp} {scalar : Bool} {L : MulRegs}
    (hop : op ≠ .div) (hv : L.Valid op scalar) {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre op rs1 rs2 rs3 s) {a b : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a)
    (hb : op ≠ .square → readLimbs? s (sourceValue (.xreg rs2) s) = some b)
    (hsq : op = .square → b = a)
    (hca : limbsToNat a < (if scalar then n else p))
    (hcb : limbsToNat b < (if scalar then n else p)) :
    ∃ w, mulqQuotientAdvice (if scalar then n else p) a b = some w ∧
      ∃ s', (Program.seq (mulRows op scalar L rs1 rs2 rs3
          (fun i => (quotientWords w).getD i 0))).Run s s' ∧
        FieldMulSpec (if scalar then n else p) op rs1 rs2 rs3 s s' ∧
        FieldMulCanonical (if scalar then n else p) rs3 s s' := by
  have hq : (if scalar then n else p) ≤ 2 ^ 256 := by cases scalar <;> decide
  have hlt : limbsToNat a * limbsToNat b / (if scalar then n else p) < 2 ^ 256 := by
    apply Nat.div_lt_of_lt_mul
    calc limbsToNat a * limbsToNat b
        < (if scalar then n else p) * (if scalar then n else p) := Nat.mul_lt_mul'' hca hcb
      _ ≤ (if scalar then n else p) * 2 ^ 256 := Nat.mul_le_mul_left _ hq
  have hw : mulqQuotientAdvice (if scalar then n else p) a b =
      some (natToLimbs (limbsToNat a * limbsToNat b / (if scalar then n else p))) := by
    simp only [mulqQuotientAdvice, fieldLimbs?, hlt, ↓reduceIte]
  refine ⟨_, hw, ?_⟩
  rw [getD_quotientWords]
  exact mulRows_jolt_advice_complete hop hv pre ha hb hsq hw

/-! ## The four layouts -/

/-- The `SECP256K1_MULQ` layout meets the conditions of the proofs.
Example: its operand, quotient and `p'` registers `vr48..vr60` are distinct, and the column
registers `vr61..vr63` are none of them. -/
theorem mulqRegs_valid : mulqRegs.Valid .mul false where
  pre_nodup := by decide
  pre_ge := by decide
  pre_free := by decide
  col0 := by decide
  col1 := by decide
  terms := by decide
  square := fun h => absurd h (by decide)
  pool := by decide

/-- The `SECP256K1_MULR` layout meets the conditions of the proofs.
Example: its operand, quotient and `p'` registers `vr48..vr61` are distinct, and the column
registers `vr62..vr64` are none of them. -/
theorem mulrRegs_valid : mulrRegs.Valid .mul true where
  pre_nodup := by decide
  pre_ge := by decide
  pre_free := by decide
  col0 := by decide
  col1 := by decide
  terms := by decide
  square := fun h => absurd h (by decide)
  pool := by decide

/-- The `SECP256K1_SQUAREQ` layout meets the conditions of the proofs.
Example: its operand, quotient and `p'` registers `vr48..vr56` are distinct, and the column
registers `vr57..vr60` are none of them. -/
theorem squareqRegs_valid : squareqRegs.Valid .square false where
  pre_nodup := by decide
  pre_ge := by decide
  pre_free := by decide
  col0 := by decide
  col1 := by decide
  terms := by decide
  square := fun _ => rfl
  pool := by decide

/-- The `SECP256K1_SQUARER` layout meets the conditions of the proofs.
Example: its operand, quotient and `p'` registers `vr48..vr57` are distinct, and the column
registers `vr58..vr61` are none of them. -/
theorem squarerRegs_valid : squarerRegs.Valid .square true where
  pre_nodup := by decide
  pre_ge := by decide
  pre_free := by decide
  col0 := by decide
  col1 := by decide
  terms := by decide
  square := fun _ => rfl
  pool := by decide

/-! ## The four inlines -/

/-- **Soundness of `SECP256K1_MULQ`.** Every run of the rows, for every advice, from a state whose
output buffer lies in RAM, stores at `rs3` a value `c` with `a·b = w·p + c` for some
`w < 2^256`, where `a` and `b` are read at `rs1` and `rs2`; only virtual registers and the
output buffer change.
Example: with `a = 2` at `x10 = 0x8001_0000`, `b = (p+1)/2` at `x11 = 0x8001_0020` and the
buffer at `x12 = 0x8002_0000`, every run stores some `c ≡ 1 (mod p)` at `0x8002_0000`. -/
theorem secp256k1Mulq_rows_sound {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (secp256k1MulqRowsAuto rs1 rs2 rs3 advice).Run s s') :
    FieldMulSpec p .mul rs1 rs2 rs3 s s' := by
  unfold secp256k1MulqRowsAuto at run
  rw [secp256k1MulqRowsAutoList_eq] at run
  exact mulRows_sound (by decide) mulqRegs_valid buf run

/-- **Completeness of `SECP256K1_MULQ` with Jolt's advice.** For a call that meets its
obligations, with operands below `p`, Jolt's quotient advice exists and the rows run with it;
the end state meets the specification, and the stored result is below `p`.
Example: with `a = 2` at `x10 = 0x8001_0000`, `b = (p+1)/2` at `x11 = 0x8001_0020` and the
buffer at `x12 = 0x8002_0000`, the rows run with quotient `w = 1` and store `1`. -/
theorem secp256k1Mulq_rows_jolt_advice_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre .mul rs1 rs2 rs3 s) {a b : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a)
    (hb : readLimbs? s (sourceValue (.xreg rs2) s) = some b)
    (hca : limbsToNat a < p) (hcb : limbsToNat b < p) :
    ∃ ws, joltAdvice .mulq a b = some ws ∧
      ∃ s', (secp256k1MulqRowsAuto rs1 rs2 rs3 (fun i => ws.getD i 0)).Run s s' ∧
        FieldMulSpec p .mul rs1 rs2 rs3 s s' ∧ FieldMulCanonical p rs3 s s' := by
  obtain ⟨w, hw, s', run, spec, can⟩ :=
    mulRows_jolt_advice_complete_of_lt (L := mulqRegs) (by decide) mulqRegs_valid pre ha
      (fun _ => hb) (fun h => absurd h (by decide)) hca hcb
  refine ⟨quotientWords w, ?_, s', ?_, spec, can⟩
  · show quotientWords <$> mulqQuotientAdvice p a b = _
    rw [show mulqQuotientAdvice p a b = some w from hw]
    rfl
  · unfold secp256k1MulqRowsAuto
    rw [secp256k1MulqRowsAutoList_eq]
    exact run

/-- **Soundness of `SECP256K1_MULR`.** Every run of the rows, for every advice, from a state whose
output buffer lies in RAM, stores at `rs3` a value `c` with `a·b = w·n + c` for some
`w < 2^256`, where `a` and `b` are read at `rs1` and `rs2`; only virtual registers and the
output buffer change.
Example: with `a = 2` at `x10 = 0x8001_0000`, `b = (n+1)/2` at `x11 = 0x8001_0020` and the
buffer at `x12 = 0x8002_0000`, every run stores some `c ≡ 1 (mod n)` at `0x8002_0000`. -/
theorem secp256k1Mulr_rows_sound {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (secp256k1MulrRowsAuto rs1 rs2 rs3 advice).Run s s') :
    FieldMulSpec n .mul rs1 rs2 rs3 s s' := by
  unfold secp256k1MulrRowsAuto at run
  rw [secp256k1MulrRowsAutoList_eq] at run
  exact mulRows_sound (by decide) mulrRegs_valid buf run

/-- **Completeness of `SECP256K1_MULR` with Jolt's advice.** For a call that meets its
obligations, with operands below `n`, Jolt's quotient advice exists and the rows run with it;
the end state meets the specification, and the stored result is below `n`.
Example: with `a = 2` at `x10 = 0x8001_0000`, `b = (n+1)/2` at `x11 = 0x8001_0020` and the
buffer at `x12 = 0x8002_0000`, the rows run with quotient `w = 1` and store `1`. -/
theorem secp256k1Mulr_rows_jolt_advice_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre .mul rs1 rs2 rs3 s) {a b : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a)
    (hb : readLimbs? s (sourceValue (.xreg rs2) s) = some b)
    (hca : limbsToNat a < n) (hcb : limbsToNat b < n) :
    ∃ ws, joltAdvice .mulr a b = some ws ∧
      ∃ s', (secp256k1MulrRowsAuto rs1 rs2 rs3 (fun i => ws.getD i 0)).Run s s' ∧
        FieldMulSpec n .mul rs1 rs2 rs3 s s' ∧ FieldMulCanonical n rs3 s s' := by
  obtain ⟨w, hw, s', run, spec, can⟩ :=
    mulRows_jolt_advice_complete_of_lt (L := mulrRegs) (by decide) mulrRegs_valid pre ha
      (fun _ => hb) (fun h => absurd h (by decide)) hca hcb
  refine ⟨quotientWords w, ?_, s', ?_, spec, can⟩
  · show quotientWords <$> mulqQuotientAdvice n a b = _
    rw [show mulqQuotientAdvice n a b = some w from hw]
    rfl
  · unfold secp256k1MulrRowsAuto
    rw [secp256k1MulrRowsAutoList_eq]
    exact run

/-- **Soundness of `SECP256K1_SQUAREQ`.** Every run of the rows, for every advice, from a state
whose output buffer lies in RAM, stores at `rs3` a value `c` with `a·a = w·p + c` for some
`w < 2^256`, where `a` is read at `rs1`; only virtual registers and the
output buffer change.
Example: with `a = 2^128` at `x10 = 0x8001_0000` and the buffer at `x12 = 0x8002_0000`, every
run stores some `c ≡ 2^256 ≡ 0x1000003d1 (mod p)` at `0x8002_0000`. -/
theorem secp256k1Squareq_rows_sound {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (secp256k1SquareqRowsAuto rs1 rs2 rs3 advice).Run s s') :
    FieldMulSpec p .square rs1 rs2 rs3 s s' := by
  unfold secp256k1SquareqRowsAuto at run
  rw [secp256k1SquareqRowsAutoList_eq] at run
  exact mulRows_sound (by decide) squareqRegs_valid buf run

/-- **Completeness of `SECP256K1_SQUAREQ` with Jolt's advice.** For a call that meets its
obligations, with operand below `p`, Jolt's quotient advice exists and the rows run with it;
the end state meets the specification, and the stored result is below `p`.
Example: with `a = 2^128` at `x10 = 0x8001_0000` and the buffer at `x12 = 0x8002_0000`, the
rows run with quotient `w = 1` and store `2^256 - p = 0x1000003d1`. -/
theorem secp256k1Squareq_rows_jolt_advice_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre .square rs1 rs2 rs3 s) {a : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a) (hca : limbsToNat a < p) :
    ∃ ws, joltAdvice .squareq a a = some ws ∧
      ∃ s', (secp256k1SquareqRowsAuto rs1 rs2 rs3 (fun i => ws.getD i 0)).Run s s' ∧
        FieldMulSpec p .square rs1 rs2 rs3 s s' ∧ FieldMulCanonical p rs3 s s' := by
  obtain ⟨w, hw, s', run, spec, can⟩ :=
    mulRows_jolt_advice_complete_of_lt (L := squareqRegs) (by decide) squareqRegs_valid pre ha
      (fun h => absurd rfl h) (fun _ => rfl) hca hca
  refine ⟨quotientWords w, ?_, s', ?_, spec, can⟩
  · show quotientWords <$> mulqQuotientAdvice p a a = _
    rw [show mulqQuotientAdvice p a a = some w from hw]
    rfl
  · unfold secp256k1SquareqRowsAuto
    rw [secp256k1SquareqRowsAutoList_eq]
    exact run

/-- **Soundness of `SECP256K1_SQUARER`.** Every run of the rows, for every advice, from a state
whose output buffer lies in RAM, stores at `rs3` a value `c` with `a·a = w·n + c` for some
`w < 2^256`, where `a` is read at `rs1`; only virtual registers and the
output buffer change.
Example: with `a = 2^128` at `x10 = 0x8001_0000` and the buffer at `x12 = 0x8002_0000`, every
run stores some `c ≡ 2^256 (mod n)` at `0x8002_0000`. -/
theorem secp256k1Squarer_rows_sound {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (secp256k1SquarerRowsAuto rs1 rs2 rs3 advice).Run s s') :
    FieldMulSpec n .square rs1 rs2 rs3 s s' := by
  unfold secp256k1SquarerRowsAuto at run
  rw [secp256k1SquarerRowsAutoList_eq] at run
  exact mulRows_sound (by decide) squarerRegs_valid buf run

/-- **Completeness of `SECP256K1_SQUARER` with Jolt's advice.** For a call that meets its
obligations, with operand below `n`, Jolt's quotient advice exists and the rows run with it;
the end state meets the specification, and the stored result is below `n`.
Example: with `a = 2^128` at `x10 = 0x8001_0000` and the buffer at `x12 = 0x8002_0000`, the
rows run with quotient `w = 1` and store `2^256 - n`. -/
theorem secp256k1Squarer_rows_jolt_advice_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre .square rs1 rs2 rs3 s) {a : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a) (hca : limbsToNat a < n) :
    ∃ ws, joltAdvice .squarer a a = some ws ∧
      ∃ s', (secp256k1SquarerRowsAuto rs1 rs2 rs3 (fun i => ws.getD i 0)).Run s s' ∧
        FieldMulSpec n .square rs1 rs2 rs3 s s' ∧ FieldMulCanonical n rs3 s s' := by
  obtain ⟨w, hw, s', run, spec, can⟩ :=
    mulRows_jolt_advice_complete_of_lt (L := squarerRegs) (by decide) squarerRegs_valid pre ha
      (fun h => absurd rfl h) (fun _ => rfl) hca hca
  refine ⟨quotientWords w, ?_, s', ?_, spec, can⟩
  · show quotientWords <$> mulqQuotientAdvice n a a = _
    rw [show mulqQuotientAdvice n a a = some w from hw]
    rfl
  · unfold secp256k1SquarerRowsAuto
    rw [secp256k1SquarerRowsAutoList_eq]
    exact run
end JoltISA.Inlines.Secp256k1
