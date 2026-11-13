import JoltBytecode.Inlines.Sha256.Ops
import JoltBytecode.Inlines.Sha256.RoundSpec

/-!
# The 64 rounds of SHA-256 on low words

`round_spec` proves that the rows of one round (`roundRows b n`) carry out one round of the
window form `Spec.roundR` on the low words: if the working variables `cur b n c` and the
message window `mReg j` hold a state and a window before the round, they hold the next state
and window after it. `rounds_spec` chains the 64 rounds. Both hold for `SHA256` (`b = false`)
and `SHA256_INIT` (`b = true`) and for every round, because the rows of a round are built from
the same blocks whether an operand is a register or a folded constant.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines.Sha256

open JoltSpec.Sha256 JoltSpec.Sha256.Spec

/-! ## Register numbers -/

/-- The number of the first temporary of a round: `vr72` for `SHA256_INIT`, `vr80` for
`SHA256`.
Example: `tBase false = 80`. -/
def tBase (b : Bool) : Nat := if b then 72 else 80

theorem tBase_false : tBase false = 80 := rfl

theorem tBase_true : tBase true = 72 := rfl

theorem tBase_ge (b : Bool) : 72 ≤ tBase b := by cases b <;> decide

theorem tBase_le (b : Bool) : tBase b ≤ 80 := by cases b <;> decide

/-- The number of a temporary.
Example: `(tReg false 2).toNat = 82`. -/
theorem tReg_toNat (b : Bool) (k : Nat) : (tReg b k).toNat = (tBase b + k) % 128 := by
  cases b <;> simp [tReg, tBase, vr, BitVec.toNat_ofNat]

/-- The number of the register of a working variable.
Example: `(sReg 1 0).toNat = 55`. -/
theorem sReg_toNat (n c : Nat) : (sReg n c).toNat = 48 + (c + 8 - n % 8) % 8 :=
  vr_toNat _ (by omega)

/-- The number of the register of an old state word.
Example: `(ivReg 7).toNat = 79`. -/
theorem ivReg_toNat (c : Nat) : (ivReg c).toNat = (72 + c) % 128 := by
  simp [ivReg, vr, BitVec.toNat_ofNat]

/-- The temporaries of a round: `vr72..75` for `SHA256_INIT`, `vr80..83` for `SHA256`. -/
def temps (b : Bool) (r : VReg) : Prop := tBase b ≤ r.toNat ∧ r.toNat < tBase b + 4

/-- The registers that round `n` writes before the new `e`: the temporaries, window word `n`
and the register of the new `a` (the old `h`). -/
def roundW0 (b : Bool) (n : Nat) (r : VReg) : Prop :=
  temps b r ∨ r = mReg n ∨ r = sReg (n + 1) 0

/-- The registers that round `n` writes: those of `roundW0` and the register of the new `e`
(the old `d`). -/
def roundW (b : Bool) (n : Nat) (r : VReg) : Prop := roundW0 b n r ∨ r = sReg (n + 1) 4

/-- The registers that the rounds write: the temporaries, the working variables and the
window, `vr48..71`. -/
def roundsW (b : Bool) (r : VReg) : Prop := temps b r ∨ (48 ≤ r.toNat ∧ r.toNat < 72)

/-- Decide a statement about registers by comparing their numbers. -/
local macro "regs" : tactic =>
  `(tactic| (simp only [BitVec.toNat_eq, tReg_toNat, mReg_toNat, sReg_toNat, ivReg_toNat,
    temps, roundW0, roundW, roundsW, tBase_false, tBase_true, ne_eq]; omega))

/-- Prove that one write set is inside another by comparing register numbers. -/
local macro "wsub" : tactic =>
  `(tactic| (intro r h; simp only [BitVec.toNat_eq, tReg_toNat, mReg_toNat, sReg_toNat,
    ivReg_toNat, temps, roundW0, roundW, roundsW, tBase_false, tBase_true] at h ⊢; omega))

/-! ## Working variables -/

/-- Round `n + 1` reads `b`, `c`, `d`, `f`, `g`, `h` where round `n` read `a`, `b`, `c`, `e`,
`f`, `g`.
Example: `cur false 1 1 = cur false 0 0 = .reg (ivReg 0)`. -/
theorem cur_succ (b : Bool) (n c : Nat) (hc : c < 8) (h0 : c % 4 ≠ 0) :
    cur b (n + 1) c = cur b n (c - 1) := by
  unfold cur
  split <;> split
  · congr 1
    omega
  · omega
  · omega
  · simp only [sReg, vr, Val.reg.injEq]
    congr 1
    omega

/-- After round `n`, `a` is in the register the round wrote. -/
theorem cur_succ_zero (b : Bool) (n : Nat) : cur b (n + 1) 0 = .reg (sReg (n + 1) 0) := by
  unfold cur
  split
  · omega
  · rfl

/-- After round `n`, `e` is in the register the round wrote. -/
theorem cur_succ_four (b : Bool) (n : Nat) : cur b (n + 1) 4 = .reg (sReg (n + 1) 4) := by
  unfold cur
  split
  · omega
  · rfl

/-- The working variables but `h` are not among the registers a round writes before the new
`e`. -/
theorem cur_avoids (b : Bool) (n c : Nat) (hc : c < 8) (h7 : c ≠ 7) :
    (cur b n c).Avoids (roundW0 b n) := by
  have hb1 := tBase_ge b
  have hb2 := tBase_le b
  intro r hr
  unfold cur ivVal at hr
  split at hr
  · cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Val.reg.injEq] at hr
      subst hr
      regs
    · simp at hr
  · simp only [Val.reg.injEq] at hr
    subst hr
    regs

/-- The working variables but `d` and `h` are not among the registers a round writes. -/
theorem cur_avoids' (b : Bool) (n c : Nat) (hc : c < 8) (h3 : c ≠ 3) (h7 : c ≠ 7) :
    (cur b n c).Avoids (roundW b n) := by
  have hb1 := tBase_ge b
  have hb2 := tBase_le b
  intro r hr
  unfold cur ivVal at hr
  split at hr
  · cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Val.reg.injEq] at hr
      subst hr
      regs
    · simp at hr
  · simp only [Val.reg.injEq] at hr
    subst hr
    regs

/-! ## One round -/

/-- `add` with a register on the right leaves its result in the destination. -/
theorem add_reg_right (x : Val) (y d : VReg) : (add x (.reg y) d).2 = .reg d := by
  cases x <;> rfl

/-- `add` with a register on the left leaves its result in the destination. -/
theorem add_reg_left (x : VReg) (y : Val) (d : VReg) : (add (.reg x) y d).2 = .reg d := by
  cases y <;> rfl

/-- The low word of a word widened to 64 bits. -/
theorem w32_setWidth (x : BitVec 32) : w32 (x.setWidth 64) = x :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq _)

/-- **The message schedule update of a round.** From round 16 on, the rows set window word
`n` as `windowStep` does; before, there are no rows. -/
theorem update_spec (b : Bool) (n : Nat) (L : VReg → BitVec 32) (w : Nat → Word)
    (hw : ∀ j, L (mReg j) = w j) :
    ∃ L', Runs (if 16 ≤ n then updateRows n (tReg b 2) (tReg b 3) else []) L L'
        (fun r => r = mReg n ∨ r = tReg b 2 ∨ r = tReg b 3) ∧
      ∀ j, L' (mReg j) = (if 16 ≤ n then windowStep n w else w) j := by
  have hb1 := tBase_ge b
  have hb2 := tBase_le b
  by_cases hn : 16 ≤ n
  · simp only [hn, ↓reduceIte]
    obtain ⟨L', h, v⟩ := updateRows_spec n (tReg b 2) (tReg b 3) (by regs) (by regs) (by regs)
      (fun j => by regs) (fun j => by regs) L
    refine ⟨L', h, fun j => ?_⟩
    by_cases hj : j % 16 = n % 16
    · have hm : mReg j = mReg n := by simp only [mReg, hj]
      rw [hm, v, hw, hw, hw, hw]
      simp only [windowStep, hj, ↓reduceIte]
      rw [BitVec.add_comm (w (n + 9))]
    · rw [h.frame (mReg j) (by regs), hw]
      simp only [windowStep, hj, ↓reduceIte]
  · simp only [hn, ↓reduceIte]
    exact ⟨L, Runs.nil L _, hw⟩

/-- The new `a` of the rows is the new `a` of the specification, up to the order of the sum. -/
private theorem new_a (k h s c w t : BitVec 32) :
    k + h + s + c + w + t = h + s + c + k + w + t := by
  ac_rfl

/-- The new `e` of the rows is the new `e` of the specification, up to the order of the sum. -/
private theorem new_e (k h s c w d : BitVec 32) :
    k + h + s + c + w + d = d + (h + s + c + k + w) := by
  ac_rfl

/-- **One round.** If before round `n` the working variables hold the state `p.1` and the
window holds `p.2`, then the rows of the round write only `roundW b n` and leave the next state
and window of `Spec.roundR` there. -/
theorem round_spec (b : Bool) (n : Nat) (L : VReg → BitVec 32) (p : State × (Nat → Word))
    (hs : ∀ c < 8, (cur b n c).eval L = p.1.get c) (hw : ∀ j, L (mReg j) = p.2 j) :
    ∃ L', Runs (roundRows b n) L L' (roundW b n) ∧
      (∀ c < 8, (cur b (n + 1) c).eval L' = (roundR n p).1.get c) ∧
      ∀ j, L' (mReg j) = (roundR n p).2 j := by
  have hb1 := tBase_ge b
  have hb2 := tBase_le b
  have hT0 : 32 ≤ (tReg b 0).toNat := by regs
  have hT1 : 32 ≤ (tReg b 1).toNat := by regs
  have hT2 : 32 ≤ (tReg b 2).toNat := by regs
  have hT3 : 32 ≤ (tReg b 3).toNat := by regs
  have hS0 : 32 ≤ (sReg (n + 1) 0).toNat := by regs
  have hS4 : 32 ≤ (sReg (n + 1) 4).toNat := by regs
  have h23 : tReg b 2 ≠ tReg b 3 := by regs
  have A : ∀ c < 8, c ≠ 7 → (cur b n c).Avoids (roundW0 b n) := cur_avoids b n
  have A23 : ∀ c < 8, c ≠ 7 → (cur b n c).Avoids (fun r => r = tReg b 2 ∨ r = tReg b 3) :=
    fun c hc h7 => (A c hc h7).mono (by wsub)
  have A12 : ∀ c < 8, c ≠ 7 → (cur b n c).Avoids (fun r => r = tReg b 1 ∨ r = tReg b 2) :=
    fun c hc h7 => (A c hc h7).mono (by wsub)
  have AT : ∀ c < 8, c ≠ 7 → (cur b n c).Avoids (temps b) :=
    fun c hc h7 => (A c hc h7).mono (by wsub)
  -- The blocks of `t1`.
  set hk := add (.imm (kImm n)) (cur b n 7) (tReg b 0) with hhk
  set s1 := bigSigma1 (cur b n 4) (tReg b 2) (tReg b 3) with hs1
  set a1 := add hk.2 s1.2 (tReg b 0) with ha1
  set ch' := ch (cur b n 4) (cur b n 5) (cur b n 6) (tReg b 2) (tReg b 3) with hch
  set a2 := add a1.2 ch'.2 (tReg b 0) with ha2
  set w' := if 16 ≤ n then windowStep n p.2 else p.2 with hw'
  set a3 := add a2.2 (.reg (mReg n)) (tReg b 0) with ha3
  -- The blocks of `t2`.
  set s0 := bigSigma0 (cur b n 0) (tReg b 1) (tReg b 2) with hs0
  set mj := maj (cur b n 0) (cur b n 1) (cur b n 2) (tReg b 2) (tReg b 3) with hmj
  set t2 := add s0.2 mj.2 (tReg b 1) with ht2
  obtain ⟨L1, r1, v1, b1⟩ := add_spec (.imm (kImm n)) (cur b n 7) (tReg b 0) hT0 L
  obtain ⟨L2, r2, v2, -⟩ := bigSigma1_spec (cur b n 4) (tReg b 2) (tReg b 3) hT2 hT3
    (A23 4 (by decide) (by decide)) L1
  obtain ⟨L3, r3, v3, b3⟩ := add_spec hk.2 s1.2 (tReg b 0) hT0 L2
  obtain ⟨L4, r4, v4, -⟩ := ch_spec (cur b n 4) (cur b n 5) (cur b n 6) (tReg b 2) (tReg b 3)
    hT2 hT3 h23 (A23 4 (by decide) (by decide)) (A23 6 (by decide) (by decide)) L3
  obtain ⟨L5, r5, v5, b5⟩ := add_spec a1.2 ch'.2 (tReg b 0) hT0 L4
  have Q5 := ((((r1.append r2).append r3).append r4).append r5).mono (W' := temps b) (by wsub)
  obtain ⟨L6, r6, v6⟩ := update_spec b n L5 p.2 fun j => by
    rw [Q5.frame (mReg j) (by regs), hw]
  obtain ⟨L7, r7, v7, b7⟩ := add_spec a2.2 (.reg (mReg n)) (tReg b 0) hT0 L6
  obtain ⟨L8, r8, v8, b8⟩ := bigSigma0_spec (cur b n 0) (tReg b 1) (tReg b 2) hT1 hT2
    (A12 0 (by decide) (by decide)) L7
  obtain ⟨L9, r9, v9, -⟩ := maj_spec (cur b n 0) (cur b n 1) (cur b n 2) (tReg b 2) (tReg b 3)
    hT2 hT3 h23 (A23 0 (by decide) (by decide)) (A23 1 (by decide) (by decide))
    (A23 2 (by decide) (by decide)) L8
  obtain ⟨L10, r10, v10, -⟩ := add_spec s0.2 mj.2 (tReg b 1) hT1 L9
  obtain ⟨L11, r11, v11, -⟩ := add_spec a3.2 t2.2 (sReg (n + 1) 0) hS0 L10
  obtain ⟨L12, r12, v12, -⟩ := add_spec a3.2 (cur b n 3) (sReg (n + 1) 4) hS4 L11
  have R7 := ((Q5.append r6).append r7).mono (W' := roundW0 b n) (by wsub)
  have R8 := (R7.append r8).mono (W' := roundW0 b n) (by wsub)
  have R11 := (((R8.append r9).append r10).append r11).mono (W' := roundW0 b n) (by wsub)
  have R12 : Runs (roundRows b n) L L12 (roundW b n) :=
    (R11.append r12).mono (W' := roundW b n) (by wsub)
  have F := (((((r7.append r8).append r9).append r10).append r11).append r12).mono
    (W' := fun r => r.toNat < 56 ∨ 72 ≤ r.toNat) (by wsub)
  -- The values.
  have ea : (cur b n 0).eval L = p.1.a := hs 0 (by decide)
  have eb : (cur b n 1).eval L = p.1.b := hs 1 (by decide)
  have ec : (cur b n 2).eval L = p.1.c := hs 2 (by decide)
  have ed : (cur b n 3).eval L = p.1.d := hs 3 (by decide)
  have ee : (cur b n 4).eval L = p.1.e := hs 4 (by decide)
  have ef : (cur b n 5).eval L = p.1.f := hs 5 (by decide)
  have eg : (cur b n 6).eval L = p.1.g := hs 6 (by decide)
  have eh : (cur b n 7).eval L = p.1.h := hs 7 (by decide)
  have x1 : hk.2.eval L1 = (K[n]!).toBitVec + p.1.h := by
    rw [v1, Val.eval_imm, kImm, w32_setWidth, eh]
  have x2 : s1.2.eval L2 = large1 p.1.e := by
    rw [v2, r1.eval ((AT 4 (by decide) (by decide)).mono (by wsub)), ee]
  have x3 : a1.2.eval L3 = (K[n]!).toBitVec + p.1.h + large1 p.1.e := by
    rw [v3, r2.eval (b1.avoids (by regs)), x1, x2]
  have Q3 := ((r1.append r2).append r3).mono (W' := temps b) (by wsub)
  have x4 : ch'.2.eval L4 = (p.1.e &&& p.1.f) ^^^ (~~~p.1.e &&& p.1.g) := by
    rw [v4, Q3.eval (AT 4 (by decide) (by decide)), Q3.eval (AT 5 (by decide) (by decide)),
      Q3.eval (AT 6 (by decide) (by decide)), ee, ef, eg]
  have x5 : a2.2.eval L5 = (K[n]!).toBitVec + p.1.h + large1 p.1.e +
      ((p.1.e &&& p.1.f) ^^^ (~~~p.1.e &&& p.1.g)) := by
    rw [v5, r4.eval (b3.avoids (by regs)), x3, x4]
  have x7 : a3.2.eval L7 = (K[n]!).toBitVec + p.1.h + large1 p.1.e +
      ((p.1.e &&& p.1.f) ^^^ (~~~p.1.e &&& p.1.g)) + w' n := by
    rw [v7, r6.eval (b5.avoids (by regs)), x5, Val.eval_reg, v6]
  have x8 : s0.2.eval L8 = large0 p.1.a := by
    rw [v8, R7.eval (A 0 (by decide) (by decide)), ea]
  have x9 : mj.2.eval L9 = (p.1.b &&& p.1.c) ^^^ (p.1.a &&& (p.1.b ^^^ p.1.c)) := by
    rw [v9, R8.eval (A 0 (by decide) (by decide)), R8.eval (A 1 (by decide) (by decide)),
      R8.eval (A 2 (by decide) (by decide)), ea, eb, ec]
  have x10 : t2.2.eval L10 = large0 p.1.a + ((p.1.b &&& p.1.c) ^^^ (p.1.a &&& (p.1.b ^^^ p.1.c))) := by
    rw [v10, r9.eval (b8.avoids (by regs)), x8, x9]
  have F810 := ((r8.append r9).append r10).mono
    (W' := fun r => r = tReg b 1 ∨ r = tReg b 2 ∨ r = tReg b 3) (by wsub)
  have x10' : a3.2.eval L10 = a3.2.eval L7 := F810.eval (b7.avoids (by regs))
  have x11' : a3.2.eval L11 = a3.2.eval L10 := r11.eval (b7.avoids (by regs))
  have ha3r : a3.2 = .reg (tReg b 0) := add_reg_right _ _ _
  have y11 : L11 (sReg (n + 1) 0) = a3.2.eval L10 + t2.2.eval L10 := by
    have := v11
    rw [ha3r, add_reg_left, Val.eval_reg] at this
    rw [this, ha3r]
  have y12 : L12 (sReg (n + 1) 4) = a3.2.eval L11 + (cur b n 3).eval L11 := by
    have := v12
    rw [ha3r, add_reg_left, Val.eval_reg] at this
    rw [this, ha3r]
  refine ⟨L12, R12, fun c hc => ?_, fun j => ?_⟩
  · by_cases h0 : c = 0
    · subst h0
      rw [cur_succ_zero, Val.eval_reg, r12.frame _ (by regs), y11, x10', x7, x10]
      simp only [roundR, State.get, step, ← hw', maj_eq]
      exact new_a _ _ _ _ _ _
    by_cases h4 : c = 4
    · subst h4
      rw [cur_succ_four, Val.eval_reg, y12, x11', x10', x7,
        R11.eval (A 3 (by decide) (by decide)), ed]
      simp only [roundR, State.get, step, ← hw']
      exact new_e _ _ _ _ _ _
    · rw [cur_succ b n c hc (by omega), R12.eval (cur_avoids' b n (c - 1) (by omega) (by omega)
        (by omega)), hs (c - 1) (by omega)]
      simp only [roundR]
      rw [step_get _ _ _ c hc h0 h4]
  · rw [F.frame (mReg j) (by regs), v6]
    rfl

/-! ## The 64 rounds -/

/-- **The rounds.** If the working variables hold `init` and the window holds the block, then
after the rows of `n` rounds, which write only `roundsW b`, they hold the state and window of
`roundsR`. -/
theorem rounds_spec (b : Bool) (input : Vector Word 16) (init : State) (L : VReg → BitVec 32)
    (hs : ∀ c < 8, (cur b 0 c).eval L = init.get c) (hw : ∀ j, L (mReg j) = input[j % 16])
    (n : Nat) :
    ∃ L', Runs (allRounds b n) L L' (roundsW b) ∧
      (∀ c < 8, (cur b n c).eval L' = (roundsR input init n).1.get c) ∧
      ∀ j, L' (mReg j) = (roundsR input init n).2 j := by
  have hb1 := tBase_ge b
  have hb2 := tBase_le b
  induction n with
  | zero => exact ⟨L, Runs.nil L _, hs, hw⟩
  | succ n ih =>
    obtain ⟨L', h, hs', hw'⟩ := ih
    obtain ⟨L'', h', hs'', hw''⟩ := round_spec b n L' _ hs' hw'
    exact ⟨L'', (h.append h').mono (by wsub), hs'', hw''⟩

end JoltISA.Inlines.Sha256
