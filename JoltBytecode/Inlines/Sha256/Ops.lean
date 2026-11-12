import JoltBytecode.Inlines.Sha256.Word

/-!
# The blocks of a SHA-256 round on low words

For each block of `Sha256.Rows` that a round uses (Σ1, Σ0, Ch, Maj and the message schedule
update), this module gives the registers the rows write and the low word they compute, for
register operands and folded constants alike. `Sha256.Rounds` composes them into a round.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines.Sha256

open JoltSpec.Sha256

/-! ## Registers -/

/-- The number of a virtual register below 128.
Example: `(vr 56).toNat = 56`. -/
theorem vr_toNat (a : Nat) (ha : a < 128) : (vr a).toNat = a := by
  simp only [vr, BitVec.toNat_ofNat]
  omega

/-- Virtual registers with different numbers below 128 differ.
Example: `vr 56 ≠ vr 57`. -/
theorem vr_ne {a b : Nat} (ha : a < 128) (hb : b < 128) (h : a ≠ b) : vr a ≠ vr b := by
  intro e
  have := congrArg BitVec.toNat e
  rw [vr_toNat a ha, vr_toNat b hb] at this
  exact h this

/-- The number of the register of message window word `j`.
Example: `(mReg 17).toNat = 57`. -/
theorem mReg_toNat (j : Nat) : (mReg j).toNat = 56 + j % 16 :=
  vr_toNat _ (by omega)

/-- Window words `n` and `n + k` live in different registers when `k` is not a multiple of 16.
Example: `mReg 17 ≠ mReg 16`. -/
theorem mReg_add_ne (n k : Nat) (hk : k % 16 ≠ 0) : mReg (n + k) ≠ mReg n := by
  intro e
  have := congrArg BitVec.toNat e
  rw [mReg_toNat, mReg_toNat] at this
  omega

/-! ## Low-word files -/

/-- Reading the register just set. -/
theorem set32_same (L : VReg → BitVec 32) (d : VReg) (v : BitVec 32) : set32 L d v d = v := by
  simp only [set32, ↓reduceIte]

/-- Reading another register than the one set. -/
theorem set32_ne (L : VReg → BitVec 32) {d r : VReg} (v : BitVec 32) (h : r ≠ d) :
    set32 L d v r = L r := by
  simp only [set32, h, ↓reduceIte]

/-- A round row in front of a run. -/
theorem Runs.cons {i : Instr} {d : VReg} {g : (VReg → BitVec 32) → BitVec 32} {l : List Instr}
    {L L' : VReg → BitVec 32} {W : VReg → Prop} (h : row32? i = some (d, g))
    (hd : 32 ≤ d.toNat) (hl : Runs l (set32 L d (g L)) L' W) :
    Runs (i :: l) L L' (fun r => r = d ∨ W r) :=
  Runs.append (l₁ := [i]) (Runs.single h hd L) hl

/-- The low word of a constant. -/
theorem Val.eval_imm (L : VReg → BitVec 32) (v : BitVec 64) : (Val.imm v).eval L = w32 v := rfl

/-- The low word of a register. -/
theorem Val.eval_reg (L : VReg → BitVec 32) (r : VReg) : (Val.reg r).eval L = L r := rfl

/-! ## Σ1 and Σ0 -/

/-- Rotating by a word mask amount is rotating right. -/
private theorem rotr_mask (x : BitVec 32) (k : Nat) (hk : k < 32) :
    rotater x (min (ctz (wordMask k)) 32) = x.rotateRight k := by
  rw [ctz_wordMask k hk, Nat.min_eq_left (by omega), rotater_eq_rotateRight x k hk]

/-- Shifting by a word mask amount is shifting right. -/
private theorem srliw_mask (x : BitVec 32) (k : Nat) (hk : k < 32) :
    (if wordMask k = 0 then 0 else x >>> ctz (wordMask k)) = x >>> k := by
  simp only [wordMask_ne_zero k hk, ↓reduceIte, ctz_wordMask k hk]

/-- **Σ1.** The rows write `rd` and `ss`, leave the result at `rd` (or fold it into a constant),
and compute `Spec.large1` of the low word of `x`, when `x` is neither `rd` nor `ss`. -/
theorem bigSigma1_spec (x : Val) (rd ss : VReg) (hrd : 32 ≤ rd.toNat) (hss : 32 ≤ ss.toNat)
    (hx : x.Avoids (fun r => r = rd ∨ r = ss)) (L : VReg → BitVec 32) :
    ∃ L', Runs (bigSigma1 x rd ss).1 L L' (fun r => r = rd ∨ r = ss) ∧
      (bigSigma1 x rd ss).2.eval L' = Spec.large1 (x.eval L) ∧ (bigSigma1 x rd ss).2.At rd := by
  cases x with
  | imm v =>
    refine ⟨L, Runs.nil L _, ?_, Or.inr ⟨_, rfl⟩⟩
    simp only [bigSigma1, Val.eval_imm, w32]
    exact BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq _)
  | reg x =>
    have hxd : x ≠ rd := fun h => hx x rfl (Or.inl h)
    have hxs : x ≠ ss := fun h => hx x rfl (Or.inr h)
    refine ⟨_, Runs.mono (Runs.cons rfl hss (Runs.cons rfl hrd (Runs.single rfl hrd _))) ?_,
      ?_, Or.inl rfl⟩
    · rintro r (h | h | h) <;> simp only [h, true_or, or_true]
    · simp only [bigSigma1, Val.eval_reg, set32_same, set32_ne _ _ hxd, set32_ne _ _ hxs,
        rotr_mask _ 18 (by decide), rotater_eq_rotateRight (w := 32) _ 19 (by decide),
        rotater_eq_rotateRight (w := 32) _ 6 (by decide)]
      exact large1_rows _

/-- **Σ0.** As `bigSigma1_spec`, for `Spec.large0`. -/
theorem bigSigma0_spec (x : Val) (rd ss : VReg) (hrd : 32 ≤ rd.toNat) (hss : 32 ≤ ss.toNat)
    (hx : x.Avoids (fun r => r = rd ∨ r = ss)) (L : VReg → BitVec 32) :
    ∃ L', Runs (bigSigma0 x rd ss).1 L L' (fun r => r = rd ∨ r = ss) ∧
      (bigSigma0 x rd ss).2.eval L' = Spec.large0 (x.eval L) ∧ (bigSigma0 x rd ss).2.At rd := by
  cases x with
  | imm v =>
    refine ⟨L, Runs.nil L _, ?_, Or.inr ⟨_, rfl⟩⟩
    simp only [bigSigma0, Val.eval_imm, w32]
    exact BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq _)
  | reg x =>
    have hxd : x ≠ rd := fun h => hx x rfl (Or.inl h)
    have hxs : x ≠ ss := fun h => hx x rfl (Or.inr h)
    refine ⟨_, Runs.mono (Runs.cons rfl hss (Runs.cons rfl hrd (Runs.single rfl hrd _))) ?_,
      ?_, Or.inl rfl⟩
    · rintro r (h | h | h) <;> simp only [h, true_or, or_true]
    · simp only [bigSigma0, Val.eval_reg, set32_same, set32_ne _ _ hxd, set32_ne _ _ hxs,
        rotr_mask _ 11 (by decide), rotater_eq_rotateRight (w := 32) _ 12 (by decide),
        rotater_eq_rotateRight (w := 32) _ 22 (by decide)]
      exact large0_rows _

/-! ## Ch and Maj -/

/-- `Ch` of the rows without `ANDN`. -/
theorem chGen_spec (e f g : Val) (rd ss : VReg) (hrd : 32 ≤ rd.toNat) (hss : 32 ≤ ss.toNat)
    (hne : rd ≠ ss) (he : e.Avoids (fun r => r = rd ∨ r = ss))
    (hg : g.Avoids (fun r => r = rd ∨ r = ss))
    (L : VReg → BitVec 32) :
    ∃ L', Runs (chGen e f g rd ss).1 L L' (fun r => r = rd ∨ r = ss) ∧
      (chGen e f g rd ss).2.eval L' = (e.eval L &&& f.eval L) ^^^ (~~~e.eval L &&& g.eval L) ∧
      (chGen e f g rd ss).2.At rd := by
  obtain ⟨L1, h1, v1, a1⟩ := and_spec e f ss hss L
  obtain ⟨L2, h2, v2, a2⟩ := xor_spec e (.imm 0xffffffff) rd hrd L1
  obtain ⟨L3, h3, v3, -⟩ := and_spec (xor e (.imm 0xffffffff) rd).2 g rd hrd L2
  obtain ⟨L4, h4, v4, a4⟩ :=
    xor_spec (and e f ss).2 (and (xor e (.imm 0xffffffff) rd).2 g rd).2 rd hrd L3
  refine ⟨L4, Runs.mono (((h1.append h2).append h3).append h4) ?_, ?_, a4⟩
  · rintro r (((h | h) | h) | h) <;> simp only [h, true_or, or_true]
  · have hss' : ¬ ss = rd := hne.symm
    simp only [chGen]
    rw [v4, h3.eval (a1.avoids hss'), h2.eval (a1.avoids hss'), v1, v3, v2,
      h2.eval (hg.mono fun r h => Or.inl h), h1.eval (hg.mono fun r h => Or.inr h),
      h1.eval (he.mono fun r h => Or.inr h), Val.eval_imm,
      show w32 (0xffffffff : BitVec 64) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes]

/-- **Ch.** The rows write `rd` and `ss`, leave the result at `rd` (or fold it), and compute
`(e & f) ^ (~e & g)` on low words, when `e` and `g` are not `rd` or `ss` (the rows read `f`
first). -/
theorem ch_spec (e f g : Val) (rd ss : VReg) (hrd : 32 ≤ rd.toNat) (hss : 32 ≤ ss.toNat)
    (hne : rd ≠ ss) (he : e.Avoids (fun r => r = rd ∨ r = ss))
    (hg : g.Avoids (fun r => r = rd ∨ r = ss))
    (L : VReg → BitVec 32) :
    ∃ L', Runs (ch e f g rd ss).1 L L' (fun r => r = rd ∨ r = ss) ∧
      (ch e f g rd ss).2.eval L' = (e.eval L &&& f.eval L) ^^^ (~~~e.eval L &&& g.eval L) ∧
      (ch e f g rd ss).2.At rd := by
  cases e with
  | imm v => exact chGen_spec (.imm v) f g rd ss hrd hss hne he hg L
  | reg re =>
    cases g with
    | imm v => exact chGen_spec (.reg re) f (.imm v) rd ss hrd hss hne he hg L
    | reg rg =>
      have hss' : ¬ ss = rd := hne.symm
      obtain ⟨L1, h1, v1, a1⟩ := and_spec (.reg re) f ss hss L
      have h2 := Runs.single (i := .ANDN (.vreg rd) (.vreg rg) (.vreg re)) rfl hrd L1
      obtain ⟨L3, h3, v3, a3⟩ := xor_spec (and (.reg re) f ss).2 (.reg rd) rd hrd
        (set32 L1 rd (L1 rg &&& ~~~L1 re))
      refine ⟨L3, Runs.mono ((h1.append h2).append h3) ?_, ?_, a3⟩
      · rintro r ((h | h) | h) <;> simp only [h, true_or, or_true]
      · simp only [ch]
        rw [v3, h2.eval (a1.avoids hss'), v1]
        simp only [Val.eval_reg, set32_same]
        rw [h1.frame rg fun h => hg rg rfl (Or.inr h), h1.frame re fun h => he re rfl (Or.inr h),
          BitVec.and_comm (L rg)]

/-- **Maj.** The rows write `rd` and `ss`, leave the result at `rd` (or fold it), and compute
`(b & c) ^ (a & (b ^ c))` on low words, when no operand is `rd` or `ss`. -/
theorem maj_spec (a b c : Val) (rd ss : VReg) (hrd : 32 ≤ rd.toNat) (hss : 32 ≤ ss.toNat)
    (hne : rd ≠ ss) (ha : a.Avoids (fun r => r = rd ∨ r = ss))
    (hb : b.Avoids (fun r => r = rd ∨ r = ss)) (hc : c.Avoids (fun r => r = rd ∨ r = ss))
    (L : VReg → BitVec 32) :
    ∃ L', Runs (maj a b c rd ss).1 L L' (fun r => r = rd ∨ r = ss) ∧
      (maj a b c rd ss).2.eval L' =
        (b.eval L &&& c.eval L) ^^^ (a.eval L &&& (b.eval L ^^^ c.eval L)) ∧
      (maj a b c rd ss).2.At rd := by
  have hss' : ¬ ss = rd := hne.symm
  obtain ⟨L1, h1, v1, a1⟩ := and_spec b c ss hss L
  obtain ⟨L2, h2, v2, -⟩ := xor_spec b c rd hrd L1
  obtain ⟨L3, h3, v3, -⟩ := and_spec a (xor b c rd).2 rd hrd L2
  obtain ⟨L4, h4, v4, a4⟩ := xor_spec (and b c ss).2 (and a (xor b c rd).2 rd).2 rd hrd L3
  refine ⟨L4, Runs.mono (((h1.append h2).append h3).append h4) ?_, ?_, a4⟩
  · rintro r (((h | h) | h) | h) <;> simp only [h, true_or, or_true]
  · simp only [maj]
    rw [v4, h3.eval (a1.avoids hss'), h2.eval (a1.avoids hss'), v1, v3, v2,
      h2.eval (ha.mono fun r h => Or.inl h), h1.eval (ha.mono fun r h => Or.inr h),
      h1.eval (hb.mono fun r h => Or.inr h), h1.eval (hc.mono fun r h => Or.inr h)]

/-- The majority of the rows is the majority of the specification. -/
theorem maj_eq (a b c : BitVec 32) :
    (b &&& c) ^^^ (a &&& (b ^^^ c)) = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-! ## The message schedule update -/

/-- **The message schedule update.** The rows write the window word `n` and the scratch
registers, and set word `n` to `w[n + 9] + (w[n] + σ0(w[n + 1])) + σ1(w[n + 14])` (indices mod
16), when the scratch registers are outside the window. -/
theorem updateRows_spec (n : Nat) (ss ss2 : VReg) (hss : 32 ≤ ss.toNat) (hss2 : 32 ≤ ss2.toNat)
    (hne : ss ≠ ss2) (hm : ∀ j, mReg j ≠ ss) (hm2 : ∀ j, mReg j ≠ ss2) (L : VReg → BitVec 32) :
    ∃ L', Runs (updateRows n ss ss2) L L' (fun r => r = mReg n ∨ r = ss ∨ r = ss2) ∧
      L' (mReg n) = L (mReg (n + 9)) + (L (mReg n) + Spec.small0 (L (mReg (n + 1)))) +
        Spec.small1 (L (mReg (n + 14))) := by
  have hmn : 32 ≤ (mReg n).toNat := by rw [mReg_toNat]; omega
  have h9 := mReg_add_ne n 9 (by decide)
  have h14 := mReg_add_ne n 14 (by decide)
  refine ⟨_, Runs.mono (Runs.cons rfl hss2 (Runs.cons rfl hss (Runs.cons rfl hss2
    (Runs.cons rfl hss (Runs.cons rfl hmn (Runs.cons rfl hmn (Runs.cons rfl hss2
    (Runs.cons rfl hss (Runs.cons rfl hss2 (Runs.cons rfl hss (Runs.single rfl hmn _)))))))))))
    ?_, ?_⟩
  · rintro r (h | h | h | h | h | h | h | h | h | h | h) <;> simp only [h, true_or, or_true]
  · simp only [set32_same, set32_ne _ _ (hm _), set32_ne _ _ (hm2 _), set32_ne _ _ hne,
      set32_ne _ _ h9, set32_ne _ _ h14,
      rotr_mask _ 11 (by decide), rotr_mask _ 30 (by decide), srliw_mask _ 3 (by decide),
      srliw_mask _ 10 (by decide), rotater_eq_rotateRight (w := 32) _ 7 (by decide),
      rotater_eq_rotateRight (w := 32) _ 19 (by decide), small0_rows, small1_rows]

end JoltISA.Inlines.Sha256
