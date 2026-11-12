import JoltBytecode.Inlines.StraightLine

/-!
# Multiply-accumulate columns

The secp256k1 field inlines (and later the P-256 ones) compute a wide product column by column
in two accumulator registers: `c1` holds the current 64-bit column and `c2` collects the carries
out of it, which become the start of the next column. Each term of a column is added by a short
group of rows (`MulqBuilder::mac_low`, `mac_high`, `m2ac_low`, ... in
`jolt-inlines/secp256k1/src/sequence_builder.rs`):

```text
MUL  aux, a, b          -- or MULHU for the high half
ADD  c1, c1, aux
SLTU c2, c1, aux        -- first term of a column: c2 := carry
-- later terms instead: SLTU aux, c1, aux;  ADD c2, c2, aux
```

`Mac` names the five kinds of term, `Mac.rows` emits their rows, and `colRows` a whole column.
`colRows_spec` is the column lemma: running a column from register file `f` gives a file `g` with

`g c1 + 2^64 · g c2 = f c1 + Σ (value of each term in f)`,

with `g c2` small and every register outside `c1, c2, aux, aux2` unchanged. Nothing here depends
on the modulus or the number of limbs; the secp256k1 files only list which terms go in which
column.

Every lemma is proved; the module has no `sorry`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-- Reading another register. Example: `setV f vr48 7 vr49 = f vr49`. -/
theorem setV_ne (f : VReg → BitVec 64) {d r : VReg} (v : BitVec 64) (h : r ≠ d) :
    setV f d v r = f r := by simp [setV, h]

/-- The evaluator of a concatenation.
Example: `regRun ([LUI vr60 5] ++ [ADD vr62 vr60 vr60]) f` runs `LUI` to get
`setV f vr60 5`, then runs `ADD` from that file, which ends with `vr62 = 10`. -/
theorem regRun_append (l₁ l₂ : List Instr) (f : VReg → BitVec 64) :
    regRun (l₁ ++ l₂) f = (regRun l₁ f).bind (regRun l₂) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [List.cons_append, regRun]
    split
    · split
      · exact ih _
      · rfl
    · rfl

/-! ## Carries -/

/-- The carry out of a 64-bit addition is `SLTU` of the sum and an addend.
Example: `x = 2^64 - 1`, `t = 1`: the sum is `0`, the carry `1`. -/
theorem add_carry (x t : BitVec 64) :
    (x + t).toNat + 2 ^ 64 * (jolt_sltu_value (x + t) t).toNat = x.toNat + t.toNat := by
  have hx := x.isLt
  have ht := t.isLt
  rw [jolt_sltu_value_toNat, BitVec.toNat_add]
  split <;> omega

/-- A carry is `0` or `1`.
Example: `jolt_sltu_value 0 1 = 1` (the carry of `(2^64 - 1) + 1`) and
`jolt_sltu_value 7 1 = 0`. -/
theorem sltu_le_one (x y : BitVec 64) : (jolt_sltu_value x y).toNat ≤ 1 := by
  rw [jolt_sltu_value_toNat]
  split <;> omega

/-- The value of `MULHU`: the high 64 bits of the 128-bit product.
Example: for `x = y = 2^32`, the product is `2^64` and `MULHU` gives `1`. -/
theorem jolt_mulhu_value_toNat (x y : BitVec 64) :
    (jolt_mulhu_value x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have hx := x.isLt
  have hy := y.isLt
  have hlt : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    exact Nat.mul_lt_mul'' hx hy
  simp only [jolt_mulhu_value, JoltISA.mulWide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The low and high halves of a 64-bit product make up the product.
Example: for `x = y = 2^32 + 1`, the product `2^64 + 2^33 + 1` has low half `2^33 + 1` and
high half `1`. -/
theorem mul_add_mulhu (x y : BitVec 64) :
    (x * y).toNat + 2 ^ 64 * (jolt_mulhu_value x y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, jolt_mulhu_value_toNat]
  exact Nat.mod_add_div _ _

/-! ## Terms and their rows -/

/-- The registers of one column: the accumulator `c1`, the carry register `c2` (the next
column's accumulator), and the scratch registers `aux` and `aux2` (`aux2` only for the doubled
terms of squaring).
Example: `SECP256K1_MULQ` column 1 uses `c1 = vr63`, `c2 = vr62`, `aux = vr61`, `aux2 = vr127`. -/
structure MacRegs where
  c1 : VReg
  c2 : VReg
  aux : VReg
  aux2 : VReg

/-- The four registers are distinct writable virtual registers (registers `vr32` and above), so
the rows that use them never alias them.
Example: `⟨vr63, vr62, vr61, vr127⟩` is valid; `⟨vr63, vr63, vr61, vr127⟩` is not
(`c1 = c2`). -/
def MacRegs.Valid (R : MacRegs) : Prop :=
  32 ≤ R.c1.toNat ∧ 32 ≤ R.c2.toNat ∧ 32 ≤ R.aux.toNat ∧ 32 ≤ R.aux2.toNat ∧
    R.c1 ≠ R.c2 ∧ R.aux ≠ R.c1 ∧ R.aux ≠ R.c2 ∧ R.aux2 ≠ R.c1 ∧ R.aux2 ≠ R.c2 ∧ R.aux ≠ R.aux2

/-- `MacRegs.Valid` is decidable, so `decide` checks it for a concrete layout.
Example: `decide` proves `MacRegs.Valid ⟨vr63, vr62, vr61, vr127⟩`, the `col1` field of
`mulqRegs_valid`. -/
instance (R : MacRegs) : Decidable R.Valid := by unfold MacRegs.Valid; infer_instance

/-- A register the column rows do not write.
Example: for `⟨vr63, vr62, vr61, vr127⟩`, `vr48` is free and `vr61` is not. -/
def MacRegs.Free (R : MacRegs) (r : VReg) : Prop :=
  r ≠ R.c1 ∧ r ≠ R.c2 ∧ r ≠ R.aux ∧ r ≠ R.aux2

/-- `MacRegs.Free` is decidable.
Example: for `R = ⟨vr63, vr62, vr61, vr127⟩`, `decide (R.Free vr48)` evaluates to `true`. -/
instance (R : MacRegs) (r : VReg) : Decidable (R.Free r) := by
  unfold MacRegs.Free; infer_instance

/-- One term of a column: the low or high half of a product, twice the low or high half (the
off-diagonal terms of a square), or a register value added as it is.
Example: column 1 of `SECP256K1_MULQ` has the term `low vr57 vr60`, the low half of `w1·p`. -/
inductive Mac where
  | low (a b : VReg)
  | high (a b : VReg)
  | low2 (a b : VReg)
  | high2 (a b : VReg)
  | word (a : VReg)

namespace Mac

/-- The registers a term reads.
Example: `(low vr48 vr52).ops = [vr48, vr52]` and `(word vr56).ops = [vr56]`. -/
def ops : Mac → List VReg
  | low a b => [a, b]
  | high a b => [a, b]
  | low2 a b => [a, b]
  | high2 a b => [a, b]
  | word a => [a]

/-- The value a term adds to its column, in register file `f`.
Example: if `f vr48 = f vr52 = 2^32 + 1`, then `(low vr48 vr52).val f = 2^33 + 1`,
`(high vr48 vr52).val f = 1` and `(low2 vr48 vr52).val f = 2^34 + 2`. -/
def val (f : VReg → BitVec 64) : Mac → Nat
  | low a b => (f a * f b).toNat
  | high a b => (jolt_mulhu_value (f a) (f b)).toNat
  | low2 a b => 2 * (f a * f b).toNat
  | high2 a b => 2 * (jolt_mulhu_value (f a) (f b)).toNat
  | word a => (f a).toNat

/-- `ADD c1, c1, t; SLTU c2, c1, t`: add `t` and set the carry register to the carry.
Example: for `⟨vr63, vr62, vr61, vr127⟩` and `t = vr61`, the values `vr63 = 2^64 - 1` and
`vr61 = 1` give `vr63 = 0` and `vr62 = 1`. -/
def addFirst (R : MacRegs) (t : VReg) : List Instr :=
  [.ADD (.vreg R.c1) (.vreg R.c1) (.vreg t), .SLTU (.vreg R.c2) (.vreg R.c1) (.vreg t)]

/-- `ADD c1, c1, t; SLTU k, c1, t; ADD c2, c2, k`: add `t` and add the carry to the carry
register, through scratch register `k`.
Example: for `⟨vr63, vr62, vr61, vr127⟩` and `t = k = vr61`, the values `vr63 = 2^64 - 1`,
`vr61 = 1` and `vr62 = 4` give `vr63 = 0` and `vr62 = 5`. -/
def addCarry (R : MacRegs) (t k : VReg) : List Instr :=
  [.ADD (.vreg R.c1) (.vreg R.c1) (.vreg t), .SLTU (.vreg k) (.vreg R.c1) (.vreg t),
    .ADD (.vreg R.c2) (.vreg R.c2) (.vreg k)]

/-- The rows of a term, as `MulqBuilder` emits them: `first` for the first term of a column
(`mac_low`, `mac_high`, `m2ac_low`, `m2ac_high`), otherwise the `_w_carry` variants.
Example: for `R = ⟨vr63, vr62, vr61, vr127⟩`, `(low vr48 vr53).rows R false` is
`MUL vr61, vr48, vr53; ADD vr63, vr63, vr61; SLTU vr61, vr63, vr61; ADD vr62, vr62, vr61`. -/
def rows (R : MacRegs) (first : Bool) : Mac → List Instr
  | low a b => .MUL (.vreg R.aux) (.vreg a) (.vreg b) ::
      (if first then addFirst R R.aux else addCarry R R.aux R.aux)
  | high a b => .MULHU (.vreg R.aux) (.vreg a) (.vreg b) ::
      (if first then addFirst R R.aux else addCarry R R.aux R.aux)
  | low2 a b => .MUL (.vreg R.aux) (.vreg a) (.vreg b) ::
      (if first then addFirst R R.aux ++ addCarry R R.aux R.aux
       else addCarry R R.aux R.aux2 ++ addCarry R R.aux R.aux2)
  | high2 a b => .MULHU (.vreg R.aux) (.vreg a) (.vreg b) ::
      (if first then addFirst R R.aux ++ addCarry R R.aux R.aux
       else addCarry R R.aux R.aux2 ++ addCarry R R.aux R.aux2)
  | word a => if first then addFirst R a else addCarry R a R.aux

/-- A term's value depends only on the registers it reads.
Example: `(low vr48 vr52).val` reads only `vr48` and `vr52`, so writing `vr61` keeps it. -/
theorem val_congr {f g : VReg → BitVec 64} (m : Mac) (h : ∀ r ∈ m.ops, g r = f r) :
    m.val g = m.val f := by
  cases m <;> simp_all [ops, val]

end Mac

/-- The rows of a column: the first term in its `first` form, the rest with carry.
Example: column 1 of `SECP256K1_MULQ` is `colRows ⟨vr63, vr62, vr61, vr127⟩ true
[low vr57 vr60, high vr56 vr60, low vr48 vr53, low vr49 vr52, high vr48 vr52]`. -/
def colRows (R : MacRegs) : Bool → List Mac → List Instr
  | _, [] => []
  | first, m :: ms => m.rows R first ++ colRows R false ms

/-! ## The rows of one term -/

/-- One register row, evaluated.
Example: `regRun (ADD vr62, vr62, vr61 :: l) f = regRun l (setV f vr62 (f vr62 + f vr61))`. -/
theorem regRun_cons {i : Instr} {d : VReg} {g : (VReg → BitVec 64) → BitVec 64}
    (hi : i.regRow? = some (d, g)) (hd : 32 ≤ d.toNat) (l : List Instr) (f : VReg → BitVec 64) :
    regRun (i :: l) f = regRun l (setV f d (g f)) := by
  simp only [regRun, hi, hd, ↓reduceIte]

section Steps

variable {R : MacRegs}

private theorem addFirst_spec (hv : R.Valid) {t : VReg} (ht1 : t ≠ R.c1) (f : VReg → BitVec 64) :
    ∃ g, regRun (Mac.addFirst R t) f = some g ∧
      (g R.c1).toNat + 2 ^ 64 * (g R.c2).toNat = (f R.c1).toNat + (f t).toNat ∧
      (g R.c2).toNat ≤ 1 ∧ ∀ r, r ≠ R.c1 → r ≠ R.c2 → g r = f r := by
  obtain ⟨h1, h2, -, -, h12, -⟩ := hv
  refine ⟨setV (setV f R.c1 (f R.c1 + f t)) R.c2 (jolt_sltu_value (f R.c1 + f t) (f t)),
    ?_, ?_, ?_, ?_⟩
  · rw [Mac.addFirst, regRun_cons rfl h1, regRun_cons rfl h2]
    simp only [regRun, setV_same, setV_ne _ _ ht1]
  · rw [setV_ne _ _ h12, setV_same, setV_same]
    exact add_carry _ _
  · rw [setV_same]
    exact sltu_le_one _ _
  · intro r hr1 hr2
    rw [setV_ne _ _ hr2, setV_ne _ _ hr1]

private theorem addCarry_spec (hv : R.Valid) {t k : VReg} (ht1 : t ≠ R.c1)
    (hk1 : k ≠ R.c1) (hk2 : k ≠ R.c2) (hk : 32 ≤ k.toNat) (f : VReg → BitVec 64)
    (hb : (f R.c2).toNat + 1 < 2 ^ 64) :
    ∃ g, regRun (Mac.addCarry R t k) f = some g ∧
      (g R.c1).toNat + 2 ^ 64 * (g R.c2).toNat =
        (f R.c1).toNat + (f t).toNat + 2 ^ 64 * (f R.c2).toNat ∧
      (g R.c2).toNat ≤ (f R.c2).toNat + 1 ∧ ∀ r, r ≠ R.c1 → r ≠ R.c2 → r ≠ k → g r = f r := by
  obtain ⟨h1, h2, -, -, h12, -⟩ := hv
  have hc := sltu_le_one (f R.c1 + f t) (f t)
  have hsum : (f R.c2 + jolt_sltu_value (f R.c1 + f t) (f t)).toNat =
      (f R.c2).toNat + (jolt_sltu_value (f R.c1 + f t) (f t)).toNat := by
    rw [BitVec.toNat_add]
    omega
  refine ⟨setV (setV (setV f R.c1 (f R.c1 + f t)) k (jolt_sltu_value (f R.c1 + f t) (f t))) R.c2
    (f R.c2 + jolt_sltu_value (f R.c1 + f t) (f t)), ?_, ?_, ?_, ?_⟩
  · rw [Mac.addCarry, regRun_cons rfl h1, regRun_cons rfl hk, regRun_cons rfl h2]
    simp only [regRun, setV_same, setV_ne _ _ ht1, setV_ne _ _ hk2.symm, setV_ne _ _ h12.symm]
  · rw [setV_ne _ _ h12, setV_ne _ _ hk1.symm, setV_same, setV_same, hsum]
    have := add_carry (f R.c1) (f t)
    omega
  · rw [setV_same, hsum]
    omega
  · intro r hr1 hr2 hrk
    rw [setV_ne _ _ hr2, setV_ne _ _ hrk, setV_ne _ _ hr1]

/-- The product row `MUL aux, a, b` or `MULHU aux, a, b` of a term. -/
private theorem prod_cons (hv : R.Valid) (i : Instr) (P : (VReg → BitVec 64) → BitVec 64)
    (hi : i.regRow? = some (R.aux, P)) (l : List Instr) (f : VReg → BitVec 64) :
    regRun (i :: l) f = regRun l (setV f R.aux (P f)) :=
  regRun_cons hi hv.2.2.1 l f

/-- **The first term of a column.** Its rows set the pair `(c1, c2)` to the old `c1` plus the
term's value (overwriting the old carry register), with `c2 ≤ 2`, and keep every free register.
Example: for `⟨vr63, vr62, vr61, vr127⟩`, `low vr48 vr52` with `vr48 = 3`, `vr52 = 5`,
`vr63 = 2^64 - 1` gives `vr63 = 14` and `vr62 = 1`, whatever `vr62` held before. -/
theorem Mac.rows_first_spec (hv : R.Valid) (m : Mac) (hops : ∀ r ∈ m.ops, R.Free r)
    (f : VReg → BitVec 64) :
    ∃ g, regRun (m.rows R true) f = some g ∧
      (g R.c1).toNat + 2 ^ 64 * (g R.c2).toNat = (f R.c1).toNat + m.val f ∧
      (g R.c2).toNat ≤ 2 ∧ ∀ r, R.Free r → g r = f r := by
  have hv' := hv
  obtain ⟨-, -, -, -, -, hx1, hxc2, -, -, -⟩ := hv'
  cases m with
  | word a =>
    have ha : R.Free a := hops a (by simp [Mac.ops])
    obtain ⟨g, hg, he, hle, hfr⟩ := addFirst_spec hv ha.1 f
    exact ⟨g, hg, by simpa [Mac.val] using he, by omega, fun r hr => hfr r hr.1 hr.2.1⟩
  | low a b | high a b =>
    have ha : R.Free a := hops a (by simp [Mac.ops])
    have hb : R.Free b := hops b (by simp [Mac.ops])
    simp only [Mac.rows, ↓reduceIte]
    rw [prod_cons hv _ _ rfl]
    obtain ⟨g, hg, he, hle, hfr⟩ := addFirst_spec hv hx1 (setV f R.aux _)
    refine ⟨g, hg, ?_, by omega, fun r hr => ?_⟩
    · rw [he, setV_ne _ _ hx1.symm, setV_same]
      simp only [Mac.val]
    · rw [hfr r hr.1 hr.2.1, setV_ne _ _ hr.2.2.1]
  | low2 a b | high2 a b =>
    have ha : R.Free a := hops a (by simp [Mac.ops])
    have hb : R.Free b := hops b (by simp [Mac.ops])
    simp only [Mac.rows, ↓reduceIte]
    rw [prod_cons hv _ _ rfl, regRun_append]
    obtain ⟨g1, hg1, he1, hle1, hfr1⟩ := addFirst_spec hv hx1 (setV f R.aux _)
    have g1x := hfr1 _ hx1 hxc2
    rw [setV_same] at g1x
    obtain ⟨g, hg, he, hle, hfr⟩ := addCarry_spec hv hx1 hx1 hxc2 hv.2.2.1 g1 (by omega)
    refine ⟨g, by rw [hg1]; exact hg, ?_, by omega, fun r hr => ?_⟩
    · rw [he, g1x]
      rw [setV_ne _ _ hx1.symm, setV_same] at he1
      simp only [Mac.val] at he1 ⊢
      omega
    · rw [hfr r hr.1 hr.2.1 hr.2.2.1, hfr1 r hr.1 hr.2.1, setV_ne _ _ hr.2.2.1]

/-- **A later term of a column.** Running its rows adds the term's value to the pair
`(c1, c2)`, raises `c2` by at most `2`, and keeps every free register.
Example: for `⟨vr63, vr62, vr61, vr127⟩` and the term `low vr48 vr52`, the values `vr48 = 3`,
`vr52 = 5`, `vr63 = 2^64 - 1`, `vr62 = 4` give `vr63 = 14` and `vr62 = 5`. -/
theorem Mac.rows_carry_spec (hv : R.Valid) (m : Mac) (hops : ∀ r ∈ m.ops, R.Free r)
    (f : VReg → BitVec 64) (hb : (f R.c2).toNat + 2 < 2 ^ 64) :
    ∃ g, regRun (m.rows R false) f = some g ∧
      (g R.c1).toNat + 2 ^ 64 * (g R.c2).toNat =
        (f R.c1).toNat + m.val f + 2 ^ 64 * (f R.c2).toNat ∧
      (g R.c2).toNat ≤ (f R.c2).toNat + 2 ∧ ∀ r, R.Free r → g r = f r := by
  have hv' := hv
  obtain ⟨-, -, hx, hx2, -, hx1, hxc2, hy1, hy2, hxy⟩ := hv'
  cases m with
  | word a =>
    have ha : R.Free a := hops a (by simp [Mac.ops])
    obtain ⟨g, hg, he, hle, hfr⟩ := addCarry_spec hv ha.1 hx1 hxc2 hx f (by omega)
    exact ⟨g, hg, by simpa [Mac.val] using he, by omega,
      fun r hr => hfr r hr.1 hr.2.1 hr.2.2.1⟩
  | low a b | high a b =>
    have ha : R.Free a := hops a (by simp [Mac.ops])
    have hb' : R.Free b := hops b (by simp [Mac.ops])
    simp only [Mac.rows, Bool.false_eq_true, ↓reduceIte]
    rw [prod_cons hv _ _ rfl]
    have f1c2 : ∀ v, setV f R.aux v R.c2 = f R.c2 := fun _ => setV_ne _ _ hxc2.symm
    have hb1 : ∀ v, (setV f R.aux v R.c2).toNat + 1 < 2 ^ 64 := fun v => by rw [f1c2]; omega
    obtain ⟨g, hg, he, hle, hfr⟩ :=
      addCarry_spec hv hx1 hx1 hxc2 hx (setV f R.aux _) (hb1 _)
    refine ⟨g, hg, ?_, by rw [f1c2] at hle; omega, fun r hr => ?_⟩
    · rw [he, setV_ne _ _ hx1.symm, f1c2, setV_same]
      simp only [Mac.val]
    · rw [hfr r hr.1 hr.2.1 hr.2.2.1, setV_ne _ _ hr.2.2.1]
  | low2 a b | high2 a b =>
    have ha : R.Free a := hops a (by simp [Mac.ops])
    have hb' : R.Free b := hops b (by simp [Mac.ops])
    simp only [Mac.rows, Bool.false_eq_true, ↓reduceIte]
    rw [prod_cons hv _ _ rfl, regRun_append]
    have f1c2 : ∀ v, setV f R.aux v R.c2 = f R.c2 := fun _ => setV_ne _ _ hxc2.symm
    have hb1 : ∀ v, (setV f R.aux v R.c2).toNat + 1 < 2 ^ 64 := fun v => by rw [f1c2]; omega
    obtain ⟨g1, hg1, he1, hle1, hfr1⟩ :=
      addCarry_spec hv hx1 hy1 hy2 hx2 (setV f R.aux _) (hb1 _)
    have g1x := hfr1 _ hx1 hxc2 hxy
    rw [setV_same] at g1x
    rw [f1c2] at hle1
    obtain ⟨g, hg, he, hle, hfr⟩ := addCarry_spec hv hx1 hy1 hy2 hx2 g1 (by omega)
    refine ⟨g, by rw [hg1]; exact hg, ?_, by omega, fun r hr => ?_⟩
    · rw [he, g1x]
      rw [setV_ne _ _ hx1.symm, f1c2, setV_same] at he1
      simp only [Mac.val] at he1 ⊢
      omega
    · rw [hfr r hr.1 hr.2.1 hr.2.2.2, hfr1 r hr.1 hr.2.1 hr.2.2.2, setV_ne _ _ hr.2.2.1]

end Steps

/-! ## Columns -/

/-- The terms after the first: each adds its value to the pair `(c1, c2)`.
Example: for `⟨vr63, vr62, vr61, vr127⟩`, the terms `[low vr48 vr52, word vr56]` with
`vr48 = 3`, `vr52 = 5`, `vr56 = 2`, `vr63 = 1`, `vr62 = 0` give `vr63 = 18`, `vr62 = 0`. -/
theorem colRows_carry_spec {R : MacRegs} (hv : R.Valid) (ms : List Mac)
    (hops : ∀ m ∈ ms, ∀ r ∈ m.ops, R.Free r) (f : VReg → BitVec 64)
    (hb : (f R.c2).toNat + 2 * ms.length < 2 ^ 64) :
    ∃ g, regRun (colRows R false ms) f = some g ∧
      (g R.c1).toNat + 2 ^ 64 * (g R.c2).toNat =
        (f R.c1).toNat + 2 ^ 64 * (f R.c2).toNat + (ms.map (Mac.val f)).sum ∧
      (g R.c2).toNat ≤ (f R.c2).toNat + 2 * ms.length ∧ ∀ r, R.Free r → g r = f r := by
  induction ms generalizing f with
  | nil => exact ⟨f, rfl, by simp, by simp, fun _ _ => rfl⟩
  | cons m ms ih =>
    simp only [List.length_cons] at hb
    obtain ⟨g1, hg1, he1, hle1, hfr1⟩ :=
      Mac.rows_carry_spec hv m (hops m List.mem_cons_self) f (by omega)
    obtain ⟨g, hg, he, hle, hfr⟩ :=
      ih (fun m' hm' => hops m' (List.mem_cons_of_mem _ hm')) g1 (by omega)
    have hsum : (ms.map (Mac.val g1)).sum = (ms.map (Mac.val f)).sum := by
      congr 1
      apply List.map_congr_left
      intro m' hm'
      exact Mac.val_congr m' (fun r hr => hfr1 r (hops m' (List.mem_cons_of_mem _ hm') r hr))
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · simp only [colRows, regRun_append, hg1, Option.bind_some, hg]
    · rw [he, hsum, List.map_cons, List.sum_cons]
      omega
    · simp only [List.length_cons]
      omega
    · intro r hr
      rw [hfr r hr, hfr1 r hr]

/-- **The column lemma.** Running a nonempty column whose operands the column does not write,
from register file `f`, gives `g` with `g c1 + 2^64·g c2 = f c1 + Σ val f`; the carry register
ends at most `2·(number of terms)`, and every free register keeps its value. The old carry
register is ignored: the first term overwrites it.
Example: `SECP256K1_MULQ` column 1 has five terms, so its carry register `vr62` ends `≤ 10`. -/
theorem colRows_spec {R : MacRegs} (hv : R.Valid) (ms : List Mac) (hne : ms ≠ [])
    (hops : ∀ m ∈ ms, ∀ r ∈ m.ops, R.Free r) (hlen : 2 * ms.length < 2 ^ 63)
    (f : VReg → BitVec 64) :
    ∃ g, regRun (colRows R true ms) f = some g ∧
      (g R.c1).toNat + 2 ^ 64 * (g R.c2).toNat = (f R.c1).toNat + (ms.map (Mac.val f)).sum ∧
      (g R.c2).toNat ≤ 2 * ms.length ∧ ∀ r, R.Free r → g r = f r := by
  cases ms with
  | nil => exact absurd rfl hne
  | cons m ms =>
    simp only [List.length_cons] at hlen
    obtain ⟨g1, hg1, he1, hle1, hfr1⟩ :=
      Mac.rows_first_spec hv m (hops m List.mem_cons_self) f
    obtain ⟨g, hg, he, hle, hfr⟩ := colRows_carry_spec hv ms
      (fun m' hm' => hops m' (List.mem_cons_of_mem _ hm')) g1 (by omega)
    have hsum : (ms.map (Mac.val g1)).sum = (ms.map (Mac.val f)).sum := by
      congr 1
      apply List.map_congr_left
      intro m' hm'
      exact Mac.val_congr m' (fun r hr => hfr1 r (hops m' (List.mem_cons_of_mem _ hm') r hr))
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · simp only [colRows, regRun_append, hg1, Option.bind_some, hg]
    · rw [he, hsum, List.map_cons, List.sum_cons]
      omega
    · simp only [List.length_cons]
      omega
    · intro r hr
      rw [hfr r hr, hfr1 r hr]

/-! ## Resets -/

/-- The rows `ADDI r, x0, 0` that zero the pool registers `rs` at the end of an inline.
Example: `resetRows [vr48]` is `[ADDI vr48, x0, 0]`. -/
def resetRows (rs : List VReg) : List Instr :=
  rs.map fun r => .ADDI (.vreg r) (.xreg (regidx.Regidx 0)) 0

/-- The resets always run, and they zero exactly the registers they name.
Example: after `resetRows [vr48, vr49]`, both registers read `0`. -/
theorem resetRows_spec (rs : List VReg) (h : ∀ r ∈ rs, 32 ≤ r.toNat) (f : VReg → BitVec 64) :
    ∃ g, regRun (resetRows rs) f = some g ∧ ∀ r, g r = if r ∈ rs then 0 else f r := by
  induction rs generalizing f with
  | nil => exact ⟨f, rfl, fun r => by simp⟩
  | cons r rs ih =>
    obtain ⟨g, hg, hgv⟩ := ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      (setV f r (0 + 0))
    refine ⟨g, ?_, fun r' => ?_⟩
    · simp only [resetRows, List.map_cons]
      rw [regRun_cons rfl (h r List.mem_cons_self)]
      exact hg
    · rw [hgv]
      by_cases h1 : r' ∈ rs
      · simp [h1]
      · by_cases h2 : r' = r
        · subst h2; simp
        · simp [h1, h2, setV_ne _ _ h2]

end JoltISA.Inlines
