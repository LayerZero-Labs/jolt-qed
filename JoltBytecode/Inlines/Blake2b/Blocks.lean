import JoltBytecode.Inlines.Blake2b.Compress
import JoltBytecode.Inlines.LoadStoreRows

/-!
# The load, init, final, store and reset blocks of `BLAKE2`

`Blake2b.Compress` runs the 96 calls of G. This module runs the other blocks of
`Blake2b.Rows`:

* the loads (`loadRows_eq`): `h` from `rs1` into `vr80..87`, `m` from `rs2` into `vr64..79`, the
  counter into `vr60` and the flag into `vr62`; `input` names the loaded words;
* the init rows (`regRun_initRows`, `wView_initF`): the work vector `initVec`;
* the final rows (`regRun_finalRows`, `finalF_hReg`): `h[i] ^ (v[i] ^ v[i + 8])` in `vr80..87`;
* the stores (`storeRows_eq`) and the resets (`regRun_resetRows`).

`rowsOut_eq_compress` proves that the result is `Spec.compress 12` when the flag is 0 or 1.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Blake2b

open JoltSpec.Blake2b

/-! ## Pool registers -/

/-- The pool registers of `BLAKE2`: `vr48..87`.
Example: `InPool vr60` holds and `InPool vr40` does not. -/
def InPool (r : VReg) : Prop := 48 ≤ r.toNat ∧ r.toNat < 88

instance (r : VReg) : Decidable (InPool r) := inferInstanceAs (Decidable (_ ∧ _))

private theorem wReg_pool (i : Fin 16) : InPool (wReg i) := by
  have := i.isLt; unfold InPool; rw [wReg_toNat]; omega

private theorem mReg_pool (j : Fin 16) : InPool (mReg j) := by
  have := j.isLt; unfold InPool; rw [mReg_toNat]; omega

private theorem hReg_pool (i : Fin 8) : InPool (hReg i) := by
  have := i.isLt; unfold InPool; rw [hReg_toNat]; omega

@[simp] private theorem hReg_ge (i : Fin 8) : 32 ≤ (hReg i).toNat := by rw [hReg_toNat]; omega

private theorem ne_of_pool {r d : VReg} (hr : ¬ InPool r) (hd : InPool d) : r ≠ d := by
  rintro rfl; exact hr hd

private theorem hReg_ne_wReg (i : Fin 8) (j : Fin 16) : hReg i ≠ wReg j := by
  intro h
  have := congrArg BitVec.toNat h
  rw [hReg_toNat, wReg_toNat] at this
  have := i.isLt; have := j.isLt
  omega

private theorem hReg_eq_iff (i j : Fin 8) : hReg i = hReg j ↔ i = j := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [hReg_toNat, hReg_toNat] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

private theorem setV_wReg_hReg (f : VReg → BitVec 64) (i : Fin 16) (v : BitVec 64) (j : Fin 8) :
    setV f (wReg i) v (hReg j) = f (hReg j) := by
  simp only [setV, hReg_ne_wReg, ↓reduceIte]

private theorem setV_hReg_wReg (f : VReg → BitVec 64) (i : Fin 8) (v : BitVec 64) (j : Fin 16) :
    setV f (hReg i) v (wReg j) = f (wReg j) := by
  simp only [setV, (hReg_ne_wReg i j).symm, ↓reduceIte]

private theorem setV_wReg_wReg (f : VReg → BitVec 64) (i j : Fin 16) (v : BitVec 64) :
    setV f (wReg i) v (wReg j) = if j = i then v else f (wReg j) := by
  simp only [setV, wReg_eq_iff]

/-! ## Loads -/

/-- The loads from `rs1`: `h[i]` at offset `8i` into `vr(80 + i)`.
Example: the second entry is `(vr81, 8)`. -/
def hLds : List (VReg × BitVec 64) :=
  (List.range 8).map fun i => (BitVec.ofNat 7 (80 + i), BitVec.ofNat 64 (8 * i))

/-- The loads from `rs2`: `m[j]` at offset `8j` into `vr(64 + j)`, then the counter at `128`
into `vr60` and the flag at `136` into `vr62`.
Example: the last entry is `(vr62, 136)`. -/
def mLds : List (VReg × BitVec 64) :=
  (List.range 16).map (fun j => (BitVec.ofNat 7 (64 + j), BitVec.ofNat 64 (8 * j))) ++
    [(BitVec.ofNat 7 60, 128), (BitVec.ofNat 7 62, 136)]

/-- The 26 load rows are the 8 loads of `h` from `rs1`, then the 18 loads from `rs2`.
Example: the first row is `LD vr80, 0(rs1)` and the ninth is `LD vr64, 0(rs2)`. -/
theorem loadRows_eq (rs1 rs2 : regidx) :
    loadRows rs1 rs2 = ldRows rs1 hLds ++ ldRows rs2 mLds := rfl

/-- Every load of `h` writes a register from `vr32` on.
Example: the first writes `vr80`. -/
theorem hLds_ge : ∀ p ∈ hLds, 32 ≤ p.1.toNat := by decide

/-- Every load from the message buffer writes a register from `vr32` on.
Example: the last writes `vr62`. -/
theorem mLds_ge : ∀ p ∈ mLds, 32 ≤ p.1.toNat := by decide

private theorem hLds_pool : ∀ p ∈ hLds, InPool p.1 := by decide

private theorem mLds_pool : ∀ p ∈ mLds, InPool p.1 := by decide

/-- The inputs of a call: the state `h`, the message `m`, the counter `t` and the final-block
flag. -/
structure Input where
  h : Vector (BitVec 64) 8
  m : Vector (BitVec 64) 16
  t : BitVec 64
  flag : BitVec 64

/-- The inputs that the loads read from `s`, with `h` at `A` and the message block at `B`; a
failed load counts as `0`.
Example: `(input s A B).t` is the doubleword at `B + 128`. -/
def input (s : SailJoltState) (A B : BitVec 64) : Input where
  h := Vector.ofFn fun i => (loadDword? s (A + BitVec.ofNat 64 (8 * i.val))).getD 0
  m := Vector.ofFn fun j => (loadDword? s (B + BitVec.ofNat 64 (8 * j.val))).getD 0
  t := (loadDword? s (B + 128)).getD 0
  flag := (loadDword? s (B + 136)).getD 0

/-- Every load of a call succeeds: the 8 doublewords at `A` and the 18 at `B`.
Example: it fails when `A` is not 8-aligned. -/
def Readable (s : SailJoltState) (A B : BitVec 64) : Prop :=
  (∀ i < 8, (loadDword? s (A + BitVec.ofNat 64 (8 * i))).isSome) ∧
    (∀ j < 16, (loadDword? s (B + BitVec.ofNat 64 (8 * j))).isSome) ∧
    (loadDword? s (B + 128)).isSome ∧ (loadDword? s (B + 136)).isSome

/-- `Readable` is the condition, list by list, that every load of the rows succeeds.
Example: both sides fail when `A` is not 8-aligned. -/
theorem readable_iff (s : SailJoltState) (A B : BitVec 64) :
    ((∀ p ∈ hLds, (loadDword? s (A + p.2)).isSome) ∧
      (∀ p ∈ mLds, (loadDword? s (B + p.2)).isSome)) ↔ Readable s A B := by
  simp only [hLds, mLds, Readable, List.forall_mem_map, List.forall_mem_append,
    List.forall_mem_cons, List.mem_range, List.not_mem_nil, false_implies, implies_true,
    and_true]

/-- The register file after the loads. -/
abbrev loadF (s : SailJoltState) (A B : BitVec 64) : VReg → BitVec 64 :=
  ldFile s B mLds (ldFile s A hLds s.vregs)

private theorem hLds_nodup : (hLds.map Prod.fst).Nodup := by decide

private theorem mLds_nodup : (mLds.map Prod.fst).Nodup := by decide

private theorem mLds_lt80 : ∀ p ∈ mLds, p.1.toNat < 80 := by decide

/-- After the loads, state register `hReg i` holds word `i` of the loaded state.
Example: `loadF s A B vr80` is the doubleword at `A`, or `0` when that load fails. -/
theorem loadF_hReg (s : SailJoltState) (A B : BitVec 64) (i : Fin 8) :
    loadF s A B (hReg i) = (input s A B).h[i] := by
  have hne : ∀ p ∈ mLds, p.1 ≠ hReg i := by
    intro p hp he
    have := mLds_lt80 p hp
    rw [he, hReg_toNat] at this
    omega
  rw [loadF, ldFile_apply_of_forall_ne _ _ _ _ _ hne,
    ldFile_apply_of_mem _ _ _ _ hLds_nodup (off := BitVec.ofNat 64 (8 * i.val))
      (List.mem_map.2 ⟨i.val, List.mem_range.2 i.isLt, rfl⟩)]
  simp [input]

/-- After the loads, message register `mReg j` holds word `j` of the loaded block.
Example: `loadF s A B vr65` is the doubleword at `B + 8`, or `0` when that load fails. -/
theorem loadF_mReg (s : SailJoltState) (A B : BitVec 64) (j : Fin 16) :
    loadF s A B (mReg j) = (input s A B).m[j] := by
  rw [loadF, ldFile_apply_of_mem _ _ _ _ mLds_nodup (off := BitVec.ofNat 64 (8 * j.val))
      (List.mem_append_left _ (List.mem_map.2 ⟨j.val, List.mem_range.2 j.isLt, rfl⟩))]
  simp [input]

/-- After the loads, `vr60` (work word 12) holds the counter.
Example: it is the doubleword at `B + 128`, or `0` when that load fails. -/
theorem loadF_t (s : SailJoltState) (A B : BitVec 64) :
    loadF s A B (wReg 12) = (input s A B).t := by
  rw [loadF, ldFile_apply_of_mem _ _ _ _ mLds_nodup (off := 128) (by decide)]
  rfl

/-- After the loads, `vr62` (work word 14) holds the final-block flag.
Example: it is the doubleword at `B + 136`, or `0` when that load fails. -/
theorem loadF_flag (s : SailJoltState) (A B : BitVec 64) :
    loadF s A B (wReg 14) = (input s A B).flag := by
  rw [loadF, ldFile_apply_of_mem _ _ _ _ mLds_nodup (off := 136) (by decide)]
  rfl

/-- The loads change no register outside the pool `vr48..87`.
Example: `loadF s A B vr40 = s.vregs vr40`. -/
theorem loadF_out (s : SailJoltState) (A B : BitVec 64) (r : VReg) (hr : ¬ InPool r) :
    loadF s A B r = s.vregs r := by
  rw [loadF, ldFile_apply_of_forall_ne _ _ _ _ _
      (fun p hp => (ne_of_pool hr (mLds_pool p hp)).symm),
    ldFile_apply_of_forall_ne _ _ _ _ _ (fun p hp => (ne_of_pool hr (hLds_pool p hp)).symm)]

/-! ## The state view -/

/-- The state view: word `i` is register `vr(80 + i)`.
Example: `(hView f)[7] = f vr87`. -/
def hView (f : VReg → BitVec 64) : Vector (BitVec 64) 8 := Vector.ofFn fun i => f (hReg i)

/-- Word `i` of the state view `hView f` is register `hReg i` of `f`.
Example: `(hView f)[2] = f vr82`. -/
@[simp] theorem getElem_hView (f : VReg → BitVec 64) (i : Fin 8) : (hView f)[i] = f (hReg i) := by
  simp [hView]

private theorem hView_setV_wReg (f : VReg → BitVec 64) (i : Fin 16) (v : BitVec 64) :
    hView (setV f (wReg i) v) = hView f := by
  apply Vector.ext
  intro k hk
  simp only [hView, Vector.getElem_ofFn, setV_wReg_hReg]

private theorem hView_setV_hReg (f : VReg → BitVec 64) (i : Fin 8) (v : BitVec 64) :
    hView (setV f (hReg i) v) = (hView f).set i v := by
  apply Vector.ext
  intro k hk
  simp only [hView, setV, Vector.getElem_ofFn, Vector.getElem_set, hReg_eq_iff]
  by_cases h : (i : Nat) = k
  · subst h
    simp
  · have h' : (⟨k, hk⟩ : Fin 8) ≠ i := fun he => h (by rw [← he])
    simp [h, h']

private theorem wView_setV_hReg (f : VReg → BitVec 64) (i : Fin 8) (v : BitVec 64) :
    wView (setV f (hReg i) v) = wView f := by
  apply Vector.ext
  intro k hk
  simp only [wView, Vector.getElem_ofFn, setV_hReg_wReg]

/-! ## Init -/

/-- The register file after the init rows.
Example: it sets `vr48` to `vr80 ^ 0` and `vr56` to the first IV word. -/
def initF (F : VReg → BitVec 64) : VReg → BitVec 64 :=
  let F := setV F (wReg 0) (jolt_xor_value (F (hReg 0)) 0)
  let F := setV F (wReg 1) (jolt_xor_value (F (hReg 1)) 0)
  let F := setV F (wReg 2) (jolt_xor_value (F (hReg 2)) 0)
  let F := setV F (wReg 3) (jolt_xor_value (F (hReg 3)) 0)
  let F := setV F (wReg 4) (jolt_xor_value (F (hReg 4)) 0)
  let F := setV F (wReg 5) (jolt_xor_value (F (hReg 5)) 0)
  let F := setV F (wReg 6) (jolt_xor_value (F (hReg 6)) 0)
  let F := setV F (wReg 7) (jolt_xor_value (F (hReg 7)) 0)
  let F := setV F (wReg 8) 0x6a09e667f3bcc908
  let F := setV F (wReg 9) 0xbb67ae8584caa73b
  let F := setV F (wReg 10) 0x3c6ef372fe94f82b
  let F := setV F (wReg 11) 0xa54ff53a5f1d36f1
  let F := setV F (wReg 13) 0x9b05688c2b3e6c1f
  let F := setV F (wReg 15) 0x5be0cd19137e2179
  let F := setV F (wReg 12) (jolt_xor_value (F (wReg 12)) 0x510e527fade682d1)
  let F := setV F (wReg 14) (0 - F (wReg 14))
  setV F (wReg 14) (jolt_xor_value (F (wReg 14)) 0x1f83d9abfb41bd6b)

/-- The 17 init rows evaluate to `initF`.
Example: from `F`, they set `vr56` to `0x6a09e667f3bcc908`. -/
theorem regRun_initRows (F : VReg → BitVec 64) : regRun initRows F = some (initF F) := rfl

/-- The work vector that the init rows set from `h`, the counter `t` and the flag.
Example: word 12 is `t ^ IV[4]`, and word 14 is `IV[6]` for flag 0 and `~IV[6]` for flag 1. -/
def initVec (h : Vector (BitVec 64) 8) (t flag : BitVec 64) : Vector (BitVec 64) 16 :=
  #v[h[0] ^^^ 0, h[1] ^^^ 0, h[2] ^^^ 0, h[3] ^^^ 0, h[4] ^^^ 0, h[5] ^^^ 0, h[6] ^^^ 0,
    h[7] ^^^ 0, 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    t ^^^ 0x510e527fade682d1, 0x9b05688c2b3e6c1f, (0 - flag) ^^^ 0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179]

/-- After the init rows, the work vector is `initVec` of the state registers, the counter and
the flag.
Example: word 8 is `IV[0] = 0x6a09e667f3bcc908`. -/
theorem wView_initF (F : VReg → BitVec 64) :
    wView (initF F) =
      initVec (Vector.ofFn fun i => F (hReg i)) (F (wReg 12)) (F (wReg 14)) := by
  simp only [initF, wView_setV, setV_wReg_hReg, setV_wReg_wReg]
  apply Vector.ext
  intro k hk
  interval_cases k <;> simp [initVec]

/-- The init rows leave the message registers unchanged.
Example: `vr64` keeps its value. -/
theorem mView_initF (F : VReg → BitVec 64) : mView (initF F) = mView F := by
  simp only [initF, mView_setV]

/-- The init rows leave the state registers unchanged.
Example: `vr80` keeps its value. -/
theorem hView_initF (F : VReg → BitVec 64) : hView (initF F) = hView F := by
  simp only [initF, hView_setV_wReg]

/-- The init rows change no register outside the pool `vr48..87`.
Example: `initF F vr40 = F vr40`. -/
theorem initF_out (F : VReg → BitVec 64) (r : VReg) (hr : ¬ InPool r) : initF F r = F r := by
  simp only [initF, setV, ne_of_pool hr (wReg_pool _), ↓reduceIte]

/-! ## Rounds: registers outside the work vector -/

private theorem mixF_hReg (M : Mix) (f : VReg → BitVec 64) (i : Fin 8) : mixF M f (hReg i) = f (hReg i) := by
  simp only [mixF, stepW, stepM, setV, hReg_ne_wReg, ↓reduceIte]

private theorem mixF_out (M : Mix) (f : VReg → BitVec 64) (r : VReg) (hr : ¬ InPool r) :
    mixF M f r = f r := by
  simp only [mixF, stepW, stepM, setV, ne_of_pool hr (wReg_pool _), ↓reduceIte]

private theorem mixesF_hReg (Ms : List Mix) (f : VReg → BitVec 64) (i : Fin 8) :
    mixesF Ms f (hReg i) = f (hReg i) := by
  induction Ms generalizing f with
  | nil => rfl
  | cons M Ms ih => exact (ih (mixF M f)).trans (mixF_hReg M f i)

/-- The calls of G change no register outside the pool `vr48..87`.
Example: `mixesF Ms f vr40 = f vr40`. -/
theorem mixesF_out (Ms : List Mix) (f : VReg → BitVec 64) (r : VReg) (hr : ¬ InPool r) :
    mixesF Ms f r = f r := by
  induction Ms generalizing f with
  | nil => rfl
  | cons M Ms ih => exact (ih (mixF M f)).trans (mixF_out M f r hr)

/-- The calls of G leave the state registers unchanged.
Example: `vr80` keeps its value through all 96 calls. -/
theorem hView_mixesF (Ms : List Mix) (f : VReg → BitVec 64) :
    hView (mixesF Ms f) = hView f := by
  apply Vector.ext
  intro k hk
  simp only [hView, Vector.getElem_ofFn]
  exact mixesF_hReg Ms f _

/-! ## Final -/

/-- The row `h[i] := h[i] ^ v[j]`.
Example: `xorH 0 0 G` is `XOR vr80, vr80, vr48` on `G`. -/
def xorH (i : Fin 8) (j : Fin 16) (G : VReg → BitVec 64) : VReg → BitVec 64 :=
  setV G (hReg i) (jolt_xor_value (G (hReg i)) (G (wReg j)))

/-- The register file after the final rows: for each `i`, `v[i] := v[i] ^ v[i + 8]`, then
`h[i] := h[i] ^ v[i]`. -/
def finalF (G : VReg → BitVec 64) : VReg → BitVec 64 :=
  xorH 7 7 <| stepW jolt_xor_value 7 15 <| xorH 6 6 <| stepW jolt_xor_value 6 14 <|
  xorH 5 5 <| stepW jolt_xor_value 5 13 <| xorH 4 4 <| stepW jolt_xor_value 4 12 <|
  xorH 3 3 <| stepW jolt_xor_value 3 11 <| xorH 2 2 <| stepW jolt_xor_value 2 10 <|
  xorH 1 1 <| stepW jolt_xor_value 1 9 <| xorH 0 0 <| stepW jolt_xor_value 0 8 G

private theorem finalRows_eq : finalRows =
  [
   .XOR (.vreg (wReg 0)) (.vreg (wReg 0)) (.vreg (wReg 8)),
   .XOR (.vreg (hReg 0)) (.vreg (hReg 0)) (.vreg (wReg 0)),
   .XOR (.vreg (wReg 1)) (.vreg (wReg 1)) (.vreg (wReg 9)),
   .XOR (.vreg (hReg 1)) (.vreg (hReg 1)) (.vreg (wReg 1)),
   .XOR (.vreg (wReg 2)) (.vreg (wReg 2)) (.vreg (wReg 10)),
   .XOR (.vreg (hReg 2)) (.vreg (hReg 2)) (.vreg (wReg 2)),
   .XOR (.vreg (wReg 3)) (.vreg (wReg 3)) (.vreg (wReg 11)),
   .XOR (.vreg (hReg 3)) (.vreg (hReg 3)) (.vreg (wReg 3)),
   .XOR (.vreg (wReg 4)) (.vreg (wReg 4)) (.vreg (wReg 12)),
   .XOR (.vreg (hReg 4)) (.vreg (hReg 4)) (.vreg (wReg 4)),
   .XOR (.vreg (wReg 5)) (.vreg (wReg 5)) (.vreg (wReg 13)),
   .XOR (.vreg (hReg 5)) (.vreg (hReg 5)) (.vreg (wReg 5)),
   .XOR (.vreg (wReg 6)) (.vreg (wReg 6)) (.vreg (wReg 14)),
   .XOR (.vreg (hReg 6)) (.vreg (hReg 6)) (.vreg (wReg 6)),
   .XOR (.vreg (wReg 7)) (.vreg (wReg 7)) (.vreg (wReg 15)),
   .XOR (.vreg (hReg 7)) (.vreg (hReg 7)) (.vreg (wReg 7))] := rfl

private theorem regRun_stepW_xor (i j : Fin 16) (l : List Instr) (f : VReg → BitVec 64) :
    regRun (.XOR (.vreg (wReg i)) (.vreg (wReg i)) (.vreg (wReg j)) :: l) f =
      regRun l (stepW jolt_xor_value i j f) :=
  regRun_cons_of (i := .XOR (.vreg (wReg i)) (.vreg (wReg i)) (.vreg (wReg j))) rfl (wReg_ge i) l f

private theorem regRun_xorH (i : Fin 8) (j : Fin 16) (l : List Instr) (f : VReg → BitVec 64) :
    regRun (.XOR (.vreg (hReg i)) (.vreg (hReg i)) (.vreg (wReg j)) :: l) f =
      regRun l (xorH i j f) :=
  regRun_cons_of (i := .XOR (.vreg (hReg i)) (.vreg (hReg i)) (.vreg (wReg j))) rfl (hReg_ge i) l f

/-- The 16 final rows evaluate to `finalF`.
Example: their first row sets `vr48` to `vr48 ^ vr56`. -/
theorem regRun_finalRows (G : VReg → BitVec 64) : regRun finalRows G = some (finalF G) := by
  rw [finalRows_eq]
  simp only [regRun_stepW_xor, regRun_xorH]
  rfl

private theorem hView_xorH (i : Fin 8) (j : Fin 16) (G : VReg → BitVec 64) :
    hView (xorH i j G) = (hView G).set i ((hView G)[i] ^^^ (wView G)[j]) := by
  rw [xorH, hView_setV_hReg, getElem_hView, getElem_wView]

private theorem wView_xorH (i : Fin 8) (j : Fin 16) (G : VReg → BitVec 64) :
    wView (xorH i j G) = wView G := wView_setV_hReg _ _ _

private theorem hView_stepW (op : BitVec 64 → BitVec 64 → BitVec 64) (i j : Fin 16)
    (G : VReg → BitVec 64) : hView (stepW op i j G) = hView G := hView_setV_wReg _ _ _

/-- After the final rows, state word `i` is `h[i] ^ (v[i] ^ v[i + 8])`, for the state `h` and
the work vector `v` before them.
Example: word 0 is `h[0] ^ (v[0] ^ v[8])`. -/
theorem hView_finalF (G : VReg → BitVec 64) :
    hView (finalF G) =
      Vector.ofFn fun i : Fin 8 => (hView G)[i] ^^^ ((wView G)[i.val] ^^^ (wView G)[i.val + 8]) := by
  simp only [finalF, hView_xorH, wView_xorH, hView_stepW, wView_stepW]
  apply Vector.ext
  intro k hk
  interval_cases k <;> simp

/-- The final rows change no register outside the pool `vr48..87`.
Example: `finalF G vr40 = G vr40`. -/
theorem finalF_out (G : VReg → BitVec 64) (r : VReg) (hr : ¬ InPool r) : finalF G r = G r := by
  simp only [finalF, xorH, stepW, setV, ne_of_pool hr (wReg_pool _), ne_of_pool hr (hReg_pool _),
    ↓reduceIte]

/-! ## Stores and resets -/

/-- The state registers `vr80..87`, in order. -/
def hRegs : List VReg := List.ofFn hReg

/-- The 8 store rows are `sdRows` of the state registers at offset 0.
Example: the second row is `SD rs1, vr81, 8`. -/
theorem storeRows_eq (rs1 : regidx) : storeRows rs1 = sdRows rs1 0 hRegs := rfl

/-- The register file `f` with the pool registers `vr48..87` reset to zero.
Example: `poolReset f vr60 = 0` and `poolReset f vr40 = f vr40`. -/
def poolReset (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  fun r => if InPool r then 0 else f r

private theorem regRun_resets (ks : List Nat) (hks : ∀ k ∈ ks, 48 + k < 128) (G : VReg → BitVec 64) :
    regRun (ks.map fun k =>
        .ADDI (.vreg (BitVec.ofNat 7 (48 + k))) (.xreg (regidx.Regidx 0)) 0) G =
      some (fun r => if 48 ≤ r.toNat ∧ r.toNat - 48 ∈ ks then 0 else G r) := by
  induction ks generalizing G with
  | nil => simp [regRun]
  | cons k ks ih =>
    have hk : 48 + k < 128 := hks k List.mem_cons_self
    have hd : (BitVec.ofNat 7 (48 + k)).toNat = 48 + k := by
      show (48 + k) % 128 = 48 + k; omega
    rw [List.map_cons, regRun_cons_of rfl (by rw [hd]; omega),
      ih (fun j hj => hks j (List.mem_cons_of_mem _ hj))]
    congr 1
    funext r
    simp only [setV, List.mem_cons]
    by_cases h1 : 48 ≤ r.toNat ∧ r.toNat - 48 ∈ ks
    · simp only [h1, and_self, or_true, ↓reduceIte]
    · by_cases h2 : r = BitVec.ofNat 7 (48 + k)
      · subst h2
        simp [hd]
      · have h3 : ¬ (48 ≤ r.toNat ∧ (r.toNat - 48 = k ∨ r.toNat - 48 ∈ ks)) := by
          rintro ⟨h4, h5 | h5⟩
          · apply h2
            apply BitVec.eq_of_toNat_eq
            rw [hd]
            omega
          · exact h1 ⟨h4, h5⟩
        simp only [h1, h2, h3, ↓reduceIte]

/-- The 40 reset rows evaluate to `poolReset`.
Example: afterwards `vr48 = 0` and `vr40` is unchanged. -/
theorem regRun_resetRows (G : VReg → BitVec 64) : regRun resetRows G = some (poolReset G) := by
  rw [resetRows, regRun_resets _ (fun k hk => by simp only [List.mem_range] at hk; omega)]
  congr 1
  funext r
  have := r.isLt
  simp only [poolReset, InPool, List.mem_range]
  congr 1
  apply propext
  omega

/-- Register files that agree outside the pool agree after `poolReset`.
Example: `poolReset (setV f vr50 7) = poolReset f`. -/
theorem poolReset_congr {f g : VReg → BitVec 64} (h : ∀ r, ¬ InPool r → f r = g r) :
    poolReset f = poolReset g := by
  funext r
  simp only [poolReset]
  split
  · rfl
  · exact h r ‹_›

/-! ## The result -/

/-- The words that the rows store, as a function of the inputs: run the 12 rounds on
`initVec`, then `h[i] ^ (v[i] ^ v[i + 8])`. -/
def rowsOut (x : Input) : Vector (BitVec 64) 8 :=
  let v := Spec.rounds x.m (initVec x.h x.t x.flag) 12
  Vector.ofFn fun i => x.h[i] ^^^ (v[i.val] ^^^ v[i.val + 8])

private theorem append_eq_lit (h c : Vector (BitVec 64) 8) :
    (h ++ c : Vector (BitVec 64) 16) =
      #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7],
        c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]] := by
  apply Vector.ext
  intro k hk
  interval_cases k
  all_goals first
    | exact Vector.getElem_append_left (by decide)
    | exact Vector.getElem_append_right (by decide) (by decide)

/-- The IV as 64-bit vectors. -/
theorem IV_bits : IV.map UInt64.toBitVec =
    (#v[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
      0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179] :
        Vector (BitVec 64) 8) := by
  apply Vector.ext
  intro k hk
  interval_cases k <;> (rw [Vector.getElem_map]; rfl)

/-- The init vector of the rows is the init vector of `Spec.compress` when the flag is 0 or 1.
-/
theorem initVec_eq (h : Vector (BitVec 64) 8) (t flag : BitVec 64) (hf : flag = 0 ∨ flag = 1) :
    initVec h t flag =
      let v : Vector Spec.Word 16 := h ++ IV.map UInt64.toBitVec
      let v := v.set 12 (v[12] ^^^ (t.setWidth 128).setWidth 64)
      let v := v.set 13 (v[13] ^^^ ((t.setWidth 128) >>> 64).setWidth 64)
      if decide (flag = 1) then v.set 14 (~~~v[14]) else v := by
  have ht : (t.setWidth 128).setWidth 64 = t := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := t.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hz : ((t.setWidth 128) >>> 64).setWidth 64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
    have := t.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
    rfl
  have hd0 : decide ((0 : BitVec 64) = 1) = false := by decide
  simp only [IV_bits, ht, hz]
  simp only [append_eq_lit]
  rcases hf with rfl | rfl
  · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
    apply Vector.ext
    intro k hk
    interval_cases k <;>
      simp [initVec, BitVec.xor_comm]
  · simp only
    apply Vector.ext
    intro k hk
    interval_cases k <;>
      simp [initVec, BitVec.xor_comm]

/-- **The rows compute `Spec.compress 12`** when the flag is 0 or 1. -/
theorem rowsOut_eq_compress (x : Input) (hf : x.flag = 0 ∨ x.flag = 1) :
    rowsOut x = Spec.compress 12 x.h x.m (x.t.setWidth 128) (decide (x.flag = 1)) := by
  rw [rowsOut, Spec.compress, initVec_eq _ _ _ hf]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, BitVec.xor_assoc]
  rfl

end JoltISA.Inlines.Blake2b
