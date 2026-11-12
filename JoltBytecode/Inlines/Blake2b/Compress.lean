import JoltBytecode.Inlines.Blake2b.Shape
import JoltBytecode.Inlines.StraightLine

/-!
# The rounds of `BLAKE2` compute the rounds of the specification

The 96 calls of G in `BLAKE2`'s rows (`Blake2b.Rows`) only read and write virtual registers, so
the pure evaluator `regRun` of `StraightLine` runs them. This module proves that they compute the
rounds of `JoltSpec.Blake2b.Spec`, reading the work vector from `vr48..63` (`wView`) and the
message from `vr64..79` (`mView`):

* `regRun_mixRows`, `wView_mixF`: one call of G computes `Spec.mix`. No distinctness of the four
  words is needed, because each row reads the registers the previous row wrote, as `Spec.mix`
  reads the vector the previous update set.
* `views_round`, `views_rounds`: a round computes `Spec.round`, and the calls of rounds `0` to
  `n - 1` compute `Spec.rounds`.

The lemmas about rows `ADD`, `XOR` and `VirtualXORROT*` on a register file are stated for any
register numbering, so SHA-256 and Keccak can reuse `regRun_append` and `xorrot_eq`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-! ## Rotation and register runs (any inline) -/

/-- Sail's `rotater` on a 64-bit word is `BitVec.rotateRight`, for shifts below 64.
Example: `rotater 1#64 1 = 0x8000000000000000#64`. -/
theorem rotater_eq_rotateRight (z : BitVec 64) (s : Nat) (hs : s < 64) :
    rotater z s = z.rotateRight s := by
  have h : rotater z s = (z >>> s) ||| (z <<< (64 - s)) := by
    unfold rotater
    have : (Sail.BitVec.length z -i (s : Int)) = ((64 - s : Nat) : Int) := by
      simp only [Sail.BitVec.length]; omega
    rw [this]
    rfl
  rw [h, BitVec.rotateRight_def, Nat.mod_eq_of_lt hs]

/-- The value of the `VirtualXORROT*` rows: XOR, then rotate right, for rotations below 64.
Example: `jolt_virtual_xorrot_value 32 x 0 = x.rotateRight 32`. -/
theorem xorrot_eq (n : Nat) (hn : n < 64) (x y : BitVec 64) :
    jolt_virtual_xorrot_value n x y = (x ^^^ y).rotateRight n :=
  rotater_eq_rotateRight _ n hn

/-- Evaluating a concatenation evaluates the first part, then the second.
Example: `regRun ([LUI vr60 5] ++ [LUI vr61 6]) f = some (setV (setV f vr60 5) vr61 6)`. -/
theorem regRun_append (l₁ l₂ : List Instr) (f : VReg → BitVec 64) :
    regRun (l₁ ++ l₂) f = (regRun l₁ f).bind (regRun l₂) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons i l ih =>
    rw [List.cons_append]
    cases h : i.regRow? with
    | none => simp only [regRun, h, Option.bind_none]
    | some p =>
      obtain ⟨d, g⟩ := p
      by_cases hd : 32 ≤ d.toNat
      · simp only [regRun, h, hd, ↓reduceIte, ih]
      · simp only [regRun, h, hd, ↓reduceIte, Option.bind_none]

/-- A register row with a writable destination: evaluation sets the destination and goes on.
Example: `regRun (LUI vr60 5 :: l) f = regRun l (setV f vr60 5)`. -/
theorem regRun_cons_of {i : Instr} {d : VReg} {g : (VReg → BitVec 64) → BitVec 64}
    (h : i.regRow? = some (d, g)) (hd : 32 ≤ d.toNat) (l : List Instr) (f : VReg → BitVec 64) :
    regRun (i :: l) f = regRun l (setV f d (g f)) := by
  simp only [regRun, h, hd, ↓reduceIte]

namespace Blake2b

open JoltSpec.Blake2b

/-! ## Register facts -/

theorem wReg_toNat (i : Fin 16) : (wReg i).toNat = 48 + i.val := by
  have := i.isLt
  show (48 + i.val) % 128 = 48 + i.val
  omega

theorem mReg_toNat (j : Fin 16) : (mReg j).toNat = 64 + j.val := by
  have := j.isLt
  show (64 + j.val) % 128 = 64 + j.val
  omega

theorem hReg_toNat (i : Fin 8) : (hReg i).toNat = 80 + i.val := by
  have := i.isLt
  show (80 + i.val) % 128 = 80 + i.val
  omega

/-- Work-vector registers are writable. Example: `32 ≤ (wReg 0).toNat`, as `wReg 0 = vr48`. -/
@[simp] theorem wReg_ge (i : Fin 16) : 32 ≤ (wReg i).toNat := by rw [wReg_toNat]; omega

theorem wReg_eq_iff (i j : Fin 16) : wReg i = wReg j ↔ i = j := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [wReg_toNat, wReg_toNat] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

theorem mReg_ne_wReg (j i : Fin 16) : mReg j ≠ wReg i := by
  intro h
  have := congrArg BitVec.toNat h
  rw [mReg_toNat, wReg_toNat] at this
  have := j.isLt
  have := i.isLt
  omega

/-! ## Views of the register file -/

/-- The work vector: word `i` is register `vr(48 + i)`.
Example: `(wView f)[12] = f vr60`. -/
def wView (f : VReg → BitVec 64) : Vector (BitVec 64) 16 := Vector.ofFn fun i => f (wReg i)

/-- The message block: word `j` is register `vr(64 + j)`.
Example: `(mView f)[0] = f vr64`. -/
def mView (f : VReg → BitVec 64) : Vector (BitVec 64) 16 := Vector.ofFn fun j => f (mReg j)

@[simp] theorem getElem_wView (f : VReg → BitVec 64) (i : Fin 16) : (wView f)[i] = f (wReg i) := by
  simp [wView]

@[simp] theorem getElem_mView (f : VReg → BitVec 64) (j : Fin 16) : (mView f)[j] = f (mReg j) := by
  simp [mView]

/-- Setting a work-vector register sets that word of the view.
Example: `wView (setV f vr60 7) = (wView f).set 12 7`. -/
theorem wView_setV (f : VReg → BitVec 64) (i : Fin 16) (v : BitVec 64) :
    wView (setV f (wReg i) v) = (wView f).set i v := by
  ext k hk
  simp only [wView, setV, Vector.getElem_ofFn, Vector.getElem_set, wReg_eq_iff]
  by_cases h : (i : Nat) = k
  · subst h
    simp
  · have h' : (⟨k, hk⟩ : Fin 16) ≠ i := fun he => h (by rw [← he])
    simp [h, h']

/-- Setting a work-vector register leaves the message view.
Example: `mView (setV f vr60 7) = mView f`. -/
theorem mView_setV (f : VReg → BitVec 64) (i : Fin 16) (v : BitVec 64) :
    mView (setV f (wReg i) v) = mView f := by
  ext k hk
  simp only [mView, setV, Vector.getElem_ofFn, mReg_ne_wReg, ↓reduceIte]

/-! ## One call of G -/

/-- A row `w[i] := op w[i] w[j]` on two work-vector words.
Example: `stepW (· + ·) 0 4 f` is `ADD vr48, vr48, vr52` on `f`. -/
def stepW (op : BitVec 64 → BitVec 64 → BitVec 64) (i j : Fin 16) (f : VReg → BitVec 64) :
    VReg → BitVec 64 :=
  setV f (wReg i) (op (f (wReg i)) (f (wReg j)))

/-- A row `w[i] := w[i] + m[j]` adding a message word.
Example: `stepM 0 14 f` is `ADD vr48, vr48, vr78` on `f`. -/
def stepM (i j : Fin 16) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  setV f (wReg i) (f (wReg i) + f (mReg j))

theorem wView_stepW (op : BitVec 64 → BitVec 64 → BitVec 64) (i j : Fin 16)
    (f : VReg → BitVec 64) :
    wView (stepW op i j f) = (wView f).set i (op (wView f)[i] (wView f)[j]) := by
  rw [stepW, wView_setV, getElem_wView, getElem_wView]

theorem wView_stepM (i j : Fin 16) (f : VReg → BitVec 64) :
    wView (stepM i j f) = (wView f).set i ((wView f)[i] + (mView f)[j]) := by
  rw [stepM, wView_setV, getElem_wView, getElem_mView]

theorem mView_stepW (op : BitVec 64 → BitVec 64 → BitVec 64) (i j : Fin 16)
    (f : VReg → BitVec 64) : mView (stepW op i j f) = mView f := mView_setV _ _ _

theorem mView_stepM (i j : Fin 16) (f : VReg → BitVec 64) : mView (stepM i j f) = mView f :=
  mView_setV _ _ _

/-- The register file after the ten rows of a call of G.
Example: for `⟨0, 4, 8, 12, 0, 1⟩` its first row adds `vr52` into `vr48`. -/
def mixF (M : Mix) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  let f := stepW (· + ·) M.a M.b f
  let f := stepM M.a M.x f
  let f := stepW (jolt_virtual_xorrot_value 32) M.d M.a f
  let f := stepW (· + ·) M.c M.d f
  let f := stepW (jolt_virtual_xorrot_value 24) M.b M.c f
  let f := stepW (· + ·) M.a M.b f
  let f := stepM M.a M.y f
  let f := stepW (jolt_virtual_xorrot_value 16) M.d M.a f
  let f := stepW (· + ·) M.c M.d f
  stepW (jolt_virtual_xorrot_value 63) M.b M.c f

/-- The ten rows of a call of G evaluate to `mixF`.
Example: `regRun (mixRows ⟨0, 4, 8, 12, 0, 1⟩) f = some (mixF ⟨0, 4, 8, 12, 0, 1⟩ f)`. -/
theorem regRun_mixRows (M : Mix) (f : VReg → BitVec 64) :
    regRun (mixRows M) f = some (mixF M f) := by
  simp only [mixRows, mixLo, mixHi, List.cons_append, List.nil_append]
  repeat rw [regRun_cons_of rfl (wReg_ge _)]
  rfl

/-- **One call of G is `Spec.mix`** on the work vector, with the message words `x` and `y`.
Example: for `⟨0, 4, 8, 12, 0, 1⟩`, the work vector after the rows is
`Spec.mix (wView f) 0 4 8 12 (f vr64) (f vr65)`. -/
theorem wView_mixF (M : Mix) (f : VReg → BitVec 64) :
    wView (mixF M f) =
      Spec.mix (wView f) M.a M.b M.c M.d (mView f)[M.x] (mView f)[M.y] := by
  simp only [mixF, wView_stepW, wView_stepM, mView_stepW, mView_stepM, Spec.mix,
    xorrot_eq 32 (by decide), xorrot_eq 24 (by decide), xorrot_eq 16 (by decide),
    xorrot_eq 63 (by decide), Fin.getElem_fin, Vector.getElem_set_self, Vector.set_set]

/-- A call of G leaves the message registers. -/
theorem mView_mixF (M : Mix) (f : VReg → BitVec 64) : mView (mixF M f) = mView f := by
  simp only [mixF, mView_stepW, mView_stepM]

/-! ## Rounds -/

/-- The register file after the calls `Ms`, in order.
Example: `mixesF [] f = f`. -/
def mixesF (Ms : List Mix) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  Ms.foldl (fun f M => mixF M f) f

/-- The rows of a list of calls evaluate to `mixesF`. -/
theorem regRun_mixes (Ms : List Mix) (f : VReg → BitVec 64) :
    regRun (Ms.flatMap mixRows) f = some (mixesF Ms f) := by
  induction Ms generalizing f with
  | nil => rfl
  | cons M Ms ih =>
    rw [List.flatMap_cons, regRun_append, regRun_mixRows]
    exact ih _

/-- **A round of the rows is `Spec.round`** on the work vector, and it leaves the message.
Example: for `n = 10` the rows use schedule row 0, as `Spec.round` does. -/
theorem views_round (n : Nat) (f : VReg → BitVec 64) :
    wView (mixesF (roundMixes SIGMA[n % 10]) f) = Spec.round (mView f) n (wView f) ∧
      mView (mixesF (roundMixes SIGMA[n % 10]) f) = mView f := by
  constructor <;>
  simp only [mixesF, roundMixes, List.foldl_cons, List.foldl_nil, wView_mixF, mView_mixF,
    Spec.round]

/-- **Rounds `0` to `n - 1` of the rows are `Spec.rounds`.**
Example: for `n = 12` this is the work vector of the compression function before the final XORs.
-/
theorem views_rounds (n : Nat) (f : VReg → BitVec 64) :
    wView (mixesF (roundsMixes n) f) = Spec.rounds (mView f) (wView f) n ∧
      mView (mixesF (roundsMixes n) f) = mView f := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h : mixesF (roundsMixes (n + 1)) f =
        mixesF (roundMixes SIGMA[n % 10]) (mixesF (roundsMixes n) f) := by
      simp only [roundsMixes, mixesF, List.foldl_append]
    rw [h, (views_round n _).1, (views_round n _).2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

end Blake2b

end JoltISA.Inlines
