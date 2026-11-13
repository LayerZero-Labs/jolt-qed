import JoltBytecode.Inlines.Sha256.Rounds
import JoltBytecode.Inlines.LoadStoreRows

/-!
# The load, final, store and reset blocks of `SHA256` and `SHA256_INIT`

`Sha256.Rounds` runs the 64 rounds on low words. This module runs the other blocks of
`Sha256.Rows` on full registers and puts the pieces together:

* the loads (`loadF`): for `SHA256`, the four state doublewords at `rs1`, each split into two
  words in `vr72..79`; for both inlines, the eight block doublewords at `rs2`, each byte-swapped
  word by word (`byteSwap`) and split into two words in `vr56..71`. `input` names the loaded
  state and block;
* the rounds and the final rows (`regs_spec`): the low words of `vr48..55` end as the words of
  `Spec.compression` of the loaded block and state;
* the stores (`storeStep`): word `2i` and word `2i + 1` packed into one doubleword, stored at
  `rs1 + 8i`;
* the resets (`regRun_resetRows`): the pool registers back to zero.

`rowsOut` is the four doublewords that the rows store.

Memory is little-endian: doubleword `i` at `rs1` holds state word `2i` in its low half and word
`2i + 1` in its high half, and doubleword `j` at `rs2` holds bytes `8j..8j+7` of the block.
SHA-256 reads the block as big-endian words, so block word `2j` is the byte swap of the low half
of doubleword `j`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Sha256

open JoltSpec.Sha256 JoltSpec.Sha256.Spec

/-! ## Words -/

/-- The bytes of a word in reverse order.
Example: `byteSwap 0x01020304 = 0x04030201`. -/
def byteSwap (w : BitVec 32) : BitVec 32 :=
  ((w &&& 0xFF) <<< 24) ||| ((w &&& 0xFF00) <<< 8) ||| ((w >>> 8) &&& 0xFF00) ||| (w >>> 24)

/-- Sail's `rev8` on a word is `byteSwap`. -/
theorem rev8_32 (x : BitVec 32) : rev8 x = byteSwap x := by
  unfold rev8
  simp only [Id.run]
  change IntRange.forIn' _ _ _ >>= _ = _
  unfold IntRange.forIn'
  simp only [Sail.BitVec.length, BitVec.length, Nat.cast_ofNat]
  iterate 5
    rw [IntRange.forIn'.loop]
    simp (config := { decide := true }) only [Membership.mem, dite_true, dite_false, pure_bind,
      bind_pure, Int.reduceAdd, Int.reduceSub, Int.reduceToNat]
  change BitVec.updateSubrange _ _ _ _ = _
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    zeros, byteSwap, Nat.reduceSub, Nat.reduceAdd]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  intro hi
  interval_cases i <;> simp (config := { decide := true }) at *

/-- Word `k mod 2` of a doubleword: the low half for even `k`, the high half for odd `k`.
Example: `halfWord 0x0000_0002_0000_0001 1 = 2`. -/
def halfWord (v : BitVec 64) (k : Nat) : BitVec 32 :=
  if k % 2 = 0 then v.setWidth 32 else (v >>> 32).setWidth 32

/-- Sail's `extractLsb x 63 32` is the high word. -/
private theorem extractLsb_hi (x : BitVec 64) :
    Sail.BitVec.extractLsb x 63 32 = (x >>> 32).setWidth 32 := by
  unfold Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb]
  simp [hi]

private theorem append_lo (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hi]

private theorem append_hi (a b : BitVec 32) : ((a ++ b) >>> 32).setWidth 32 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [hi]

/-- `VirtualRev8W` byte-swaps the low word. -/
theorem rev8w_lo (v : BitVec 64) :
    (jolt_virtual_rev8w_value v).setWidth 32 = byteSwap (v.setWidth 32) := by
  simp only [jolt_virtual_rev8w_value, extractLsb_lo, extractLsb_hi, rev8_32, append_lo]

/-- `VirtualRev8W` byte-swaps the high word. -/
theorem rev8w_hi (v : BitVec 64) :
    ((jolt_virtual_rev8w_value v) >>> 32).setWidth 32 = byteSwap ((v >>> 32).setWidth 32) := by
  simp only [jolt_virtual_rev8w_value, extractLsb_lo, extractLsb_hi, rev8_32, append_hi]

/-- The shift of `VirtualSRLI` with mask `srli32Mask` is 32. -/
theorem ctz_srli32Mask : ctz srli32Mask = 32 := by
  rw [show srli32Mask = 2 ^ 32 * (2 ^ 32 - 1) by unfold srli32Mask; norm_num,
    ctz_mul_pow2 32 (by norm_num), ctz_of_odd (by norm_num)]

/-- `VirtualSRLI` with mask `srli32Mask` shifts right by 32. -/
theorem srli32 (v : BitVec 64) : jolt_virtual_srli_value v srli32Mask = v >>> 32 := by
  rw [jolt_virtual_srli_value, ctz_srli32Mask]

private theorem muli_2_32 (x : BitVec 64) :
    jolt_virtual_muli_value x 0x100000000 = x <<< 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [jolt_virtual_muli_value, JoltISA.mulWide, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  norm_num

/-- The three packing rows put word `x` above word `y`.
Example: for `x = 2` and `y = 1` the result is `0x0000_0002_0000_0001`. -/
theorem pack_eq (x y : BitVec 64) :
    Riscv.ori (jolt_virtual_muli_value x 0x100000000) (jolt_virtual_zero_extend_word_value y) =
      x.setWidth 32 ++ y.setWidth 32 := by
  rw [muli_2_32]
  unfold Riscv.ori jolt_virtual_zero_extend_word_value zero_extend Sail.BitVec.zeroExtend
  rw [extractLsb_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  by_cases h : i < 32
  · simp [h, hi]
  · simp [h, hi]
    omega

/-! ## Loads -/

/-- The doubleword `i` of a buffer at `A`, or `0` when the load fails.
Example: `dword s A 1` is the doubleword at `A + 8`. -/
def dword (s : SailJoltState) (A : BitVec 64) (i : Nat) : BitVec 64 :=
  (loadDword? s (A + BitVec.ofNat 64 (8 * i))).getD 0

/-- State load `i` of `SHA256`: `LD vr(72 + 2i), 8i(rs1)`, then the high word into
`vr(73 + 2i)`. -/
def ivG (i : Nat) : VReg × BitVec 64 × List Instr :=
  (vr (72 + 2 * i), BitVec.ofNat 64 (8 * i),
    [.VirtualSRLI (.vreg (vr (73 + 2 * i))) (.vreg (vr (72 + 2 * i))) srli32Mask])

/-- Block load `i`: `LD vr(56 + 2i), 8i(rs2)`, byte-swap both words, then the high word into
`vr(57 + 2i)`. -/
def msgG (i : Nat) : VReg × BitVec 64 × List Instr :=
  (vr (56 + 2 * i), BitVec.ofNat 64 (8 * i),
    [.VirtualRev8W (.vreg (vr (56 + 2 * i))) (.vreg (vr (56 + 2 * i))) 0,
     .VirtualSRLI (.vreg (vr (57 + 2 * i))) (.vreg (vr (56 + 2 * i))) srli32Mask])

/-- The state loads are `ldPostRows` of `ivG`. -/
theorem ivLoadRows_eq (rs1 : regidx) :
    ivLoadRows rs1 = ldPostRows rs1 ((List.range 4).map ivG) := rfl

/-- The block loads are `ldPostRows` of `msgG`. -/
theorem msgLoadRows_eq (rs2 : regidx) :
    msgLoadRows rs2 = ldPostRows rs2 ((List.range 8).map msgG) := rfl

/-- What state load `i` does to the register file, given the doublewords `H`. -/
def ivStep (H : Nat → BitVec 64) (i : Nat) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  setV (setV f (vr (72 + 2 * i)) (H i)) (vr (73 + 2 * i)) (H i >>> 32)

/-- What block load `i` does to the register file, given the doublewords `M`. -/
def msgStep (M : Nat → BitVec 64) (i : Nat) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  setV (setV f (vr (56 + 2 * i)) (jolt_virtual_rev8w_value (M i))) (vr (57 + 2 * i))
    (jolt_virtual_rev8w_value (M i) >>> 32)

private theorem regRun_ivG (H : Nat → BitVec 64) (i : Nat) (hi : i < 4) (f : VReg → BitVec 64) :
    regRun (ivG i).2.2 (setV f (ivG i).1 (H i)) = some (ivStep H i f) := by
  simp only [ivG]
  rw [regRun_cons_of (i := .VirtualSRLI (.vreg (vr (73 + 2 * i))) (.vreg (vr (72 + 2 * i)))
    srli32Mask) rfl (by rw [vr_toNat _ (by omega)]; omega)]
  simp only [regRun, setV_same, srli32, ivStep]

private theorem regRun_msgG (M : Nat → BitVec 64) (i : Nat) (hi : i < 8) (f : VReg → BitVec 64) :
    regRun (msgG i).2.2 (setV f (msgG i).1 (M i)) = some (msgStep M i f) := by
  simp only [msgG]
  rw [regRun_cons_of (i := .VirtualRev8W (.vreg (vr (56 + 2 * i))) (.vreg (vr (56 + 2 * i))) 0)
    rfl (by rw [vr_toNat _ (by omega)]; omega),
    regRun_cons_of (i := .VirtualSRLI (.vreg (vr (57 + 2 * i))) (.vreg (vr (56 + 2 * i)))
      srli32Mask) rfl (by rw [vr_toNat _ (by omega)]; omega)]
  simp only [regRun, setV_same, setV_setV, srli32, msgStep]

/-- The register file after the state loads. -/
def ivFile (s : SailJoltState) (A : BitVec 64) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  (List.range 4).foldl (fun f i => ivStep (dword s A) i f) f

/-- The register file after the block loads. -/
def msgFile (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  (List.range 8).foldl (fun f i => msgStep (dword s B) i f) f

/-- The state loads evaluate to `ivFile`. -/
theorem ldPostFile_ivG (s : SailJoltState) (A : BitVec 64) (f : VReg → BitVec 64) :
    ldPostFile s A ((List.range 4).map ivG) f = some (ivFile s A f) :=
  ldPostFile_range s A 4 ivG _ (fun i hi f => regRun_ivG (dword s A) i hi f) f

/-- The block loads evaluate to `msgFile`. -/
theorem ldPostFile_msgG (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) :
    ldPostFile s B ((List.range 8).map msgG) f = some (msgFile s B f) :=
  ldPostFile_range s B 8 msgG _ (fun i hi f => regRun_msgG (dword s B) i hi f) f

/-- Every state load writes a register from `vr32` on. -/
theorem ivG_ge : ∀ g ∈ (List.range 4).map ivG, 32 ≤ g.1.toNat := by decide

/-- Every block load writes a register from `vr32` on. -/
theorem msgG_ge : ∀ g ∈ (List.range 8).map msgG, 32 ≤ g.1.toNat := by decide

/-- The pool registers: `vr48..83` for `SHA256`, `vr48..75` for `SHA256_INIT`.
Example: `InPool false vr80` holds and `InPool true vr80` does not. -/
def InPool (b : Bool) (r : VReg) : Prop := 48 ≤ r.toNat ∧ r.toNat < 48 + poolSize b

instance (b : Bool) (r : VReg) : Decidable (InPool b r) := inferInstanceAs (Decidable (_ ∧ _))

theorem poolSize_ge (b : Bool) : 28 ≤ poolSize b := by cases b <;> decide

private theorem poolSize_le (b : Bool) : poolSize b ≤ 36 := by cases b <;> decide

private theorem poolSize_false : poolSize false = 36 := rfl

/-- The block loads write only `vr56..71`. -/
private theorem msgStep_out (M : Nat → BitVec 64) (k : Nat) (hk : k < 8) (f : VReg → BitVec 64)
    (r : VReg) (h : r.toNat ≠ 56 + 2 * k) (h' : r.toNat ≠ 57 + 2 * k) : msgStep M k f r = f r := by
  have e1 : r ≠ vr (56 + 2 * k) := fun e => h (by rw [e, vr_toNat _ (by omega)])
  have e2 : r ≠ vr (57 + 2 * k) := fun e => h' (by rw [e, vr_toNat _ (by omega)])
  simp only [msgStep, setV, e1, e2, ↓reduceIte]

/-- The state loads write only `vr72..79`. -/
private theorem ivStep_out (H : Nat → BitVec 64) (k : Nat) (hk : k < 4) (f : VReg → BitVec 64)
    (r : VReg) (h : r.toNat ≠ 72 + 2 * k) (h' : r.toNat ≠ 73 + 2 * k) : ivStep H k f r = f r := by
  have e1 : r ≠ vr (72 + 2 * k) := fun e => h (by rw [e, vr_toNat _ (by omega)])
  have e2 : r ≠ vr (73 + 2 * k) := fun e => h' (by rw [e, vr_toNat _ (by omega)])
  simp only [ivStep, setV, e1, e2, ↓reduceIte]

/-- The block loads keep the registers outside `vr56..71`. -/
theorem msgFile_out (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) (r : VReg)
    (hr : r.toNat < 56 ∨ 72 ≤ r.toNat) : msgFile s B f r = f r :=
  foldl_range_frame _ 8 f r fun k hk g => msgStep_out _ k hk g r (by omega) (by omega)

/-- The state loads keep the registers outside `vr72..79`. -/
theorem ivFile_out (s : SailJoltState) (A : BitVec 64) (f : VReg → BitVec 64) (r : VReg)
    (hr : r.toNat < 72 ∨ 80 ≤ r.toNat) : ivFile s A f r = f r :=
  foldl_range_frame _ 4 f r fun k hk g => ivStep_out _ k hk g r (by omega) (by omega)

/-- After the block loads, the low word of window register `j` is block word `j mod 16`, the
byte swap of a half of doubleword `(j mod 16) / 2`. -/
theorem msgFile_mReg (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) (j : Nat) :
    (msgFile s B f (mReg j)).setWidth 32 =
      byteSwap (halfWord (dword s B (j % 16 / 2)) (j % 16)) := by
  have hj := Nat.mod_lt j (show 16 > 0 by decide)
  set i := j % 16 / 2 with hi
  have hi8 : i < 8 := by omega
  by_cases he : j % 16 % 2 = 0
  · have hr : mReg j = vr (56 + 2 * i) := by
      show vr (56 + j % 16) = _; congr 1; omega
    rw [hr, msgFile, foldl_range_apply _ 8 i hi8 f _ (fun k h1 h2 g => msgStep_out _ k h2 g _
      (by rw [vr_toNat _ (by omega)]; omega) (by rw [vr_toNat _ (by omega)]; omega))]
    simp only [msgStep, setV, vr_ne (by omega) (by omega) (show 56 + 2 * i ≠ 57 + 2 * i by omega),
      ↓reduceIte, rev8w_lo, halfWord, he]
  · have hr : mReg j = vr (57 + 2 * i) := by
      show vr (56 + j % 16) = _; congr 1; omega
    rw [hr, msgFile, foldl_range_apply _ 8 i hi8 f _ (fun k h1 h2 g => msgStep_out _ k h2 g _
      (by rw [vr_toNat _ (by omega)]; omega) (by rw [vr_toNat _ (by omega)]; omega))]
    simp only [msgStep, setV_same, rev8w_hi, halfWord, he, ↓reduceIte]

/-- After the state loads, the low word of `ivReg c` is word `c` of the loaded state. -/
theorem ivFile_ivReg (s : SailJoltState) (A : BitVec 64) (f : VReg → BitVec 64) (c : Nat)
    (hc : c < 8) : (ivFile s A f (ivReg c)).setWidth 32 = halfWord (dword s A (c / 2)) c := by
  set i := c / 2 with hi
  have hi4 : i < 4 := by omega
  by_cases he : c % 2 = 0
  · have hr : ivReg c = vr (72 + 2 * i) := by
      show vr (72 + c) = _; congr 1; omega
    rw [hr, ivFile, foldl_range_apply _ 4 i hi4 f _ (fun k h1 h2 g => ivStep_out _ k h2 g _
      (by rw [vr_toNat _ (by omega)]; omega) (by rw [vr_toNat _ (by omega)]; omega))]
    simp only [ivStep, setV, vr_ne (by omega) (by omega) (show 72 + 2 * i ≠ 73 + 2 * i by omega),
      ↓reduceIte, halfWord, he]
  · have hr : ivReg c = vr (73 + 2 * i) := by
      show vr (72 + c) = _; congr 1; omega
    rw [hr, ivFile, foldl_range_apply _ 4 i hi4 f _ (fun k h1 h2 g => ivStep_out _ k h2 g _
      (by rw [vr_toNat _ (by omega)]; omega) (by rw [vr_toNat _ (by omega)]; omega))]
    simp only [ivStep, setV_same, halfWord, he, ↓reduceIte]

/-! ## Inputs -/

/-- The working variables of a state of eight words, word `c` being half `c mod 2` of
doubleword `c / 2`.
Example: `(stateOf H).b` is the high word of `H 0`. -/
def stateOf (H : Nat → BitVec 64) : State :=
  ⟨halfWord (H 0) 0, halfWord (H 0) 1, halfWord (H 1) 2, halfWord (H 1) 3,
    halfWord (H 2) 4, halfWord (H 2) 5, halfWord (H 3) 6, halfWord (H 3) 7⟩

theorem stateOf_get (H : Nat → BitVec 64) (c : Nat) (hc : c < 8) :
    (stateOf H).get c = halfWord (H (c / 2)) c := by
  interval_cases c <;> rfl

/-- The inputs of a call: the state and the 16 block words. -/
structure Input where
  /-- The state that the block is compressed into. -/
  state : State
  /-- The block, as 16 big-endian words. -/
  block : Vector Word 16

/-- The inputs that the loads read from `s`: for `SHA256` (`b = false`) the state at `A`, for
`SHA256_INIT` (`b = true`) the initial hash value; the block at `B`. A failed load counts as
`0`.
Example: `(input true s A B).state = Spec.initial`. -/
def input (b : Bool) (s : SailJoltState) (A B : BitVec 64) : Input where
  state := if b then initial else stateOf (dword s A)
  block := Vector.ofFn fun j => byteSwap (halfWord (dword s B (j.val / 2)) j.val)

/-- Every load of a call succeeds: for `SHA256` the 4 doublewords at `A`, and the 8 at `B`.
Example: it fails when `B` is not 8-aligned. -/
def Readable (b : Bool) (s : SailJoltState) (A B : BitVec 64) : Prop :=
  (b = false → ∀ i < 4, (loadDword? s (A + BitVec.ofNat 64 (8 * i))).isSome) ∧
    ∀ i < 8, (loadDword? s (B + BitVec.ofNat 64 (8 * i))).isSome

/-- The register file after the loads. -/
def loadF (b : Bool) (s : SailJoltState) (A B : BitVec 64) : VReg → BitVec 64 :=
  msgFile s B (if b then s.vregs else ivFile s A s.vregs)

private theorem readable_range (s : SailJoltState) (A : BitVec 64) (n : Nat)
    (g : Nat → VReg × BitVec 64 × List Instr) (hg : ∀ i, (g i).2.1 = BitVec.ofNat 64 (8 * i)) :
    (∀ p ∈ (List.range n).map g, (loadDword? s (A + p.2.1)).isSome) ↔
      ∀ i < n, (loadDword? s (A + BitVec.ofNat 64 (8 * i))).isSome := by
  simp only [List.forall_mem_map, List.mem_range, hg]

/-- **The loads.** With `rs1` reading `A` (for `SHA256`) and `rs2` reading `B`, a run of the load rows and
then `rest` is a run of `rest` from the loaded register file, and it exists only when every
load succeeds. -/
theorem run_loadRows_iff {b : Bool} {rs1 rs2 : regidx} {s : SailJoltState} {A B : BitVec 64}
    (hr1 : b = false → XReads s rs1 A) (hr2 : XReads s rs2 B) (rest : List Instr)
    (s' : SailJoltState) :
    (Program.seq (loadRows b rs1 rs2 ++ rest)).Run s s' ↔
      Readable b s A B ∧ (Program.seq rest).Run { s with vregs := loadF b s A B } s' := by
  cases b with
  | false =>
    simp only [loadRows, Bool.false_eq_true, ↓reduceIte, ivLoadRows_eq, msgLoadRows_eq,
      List.append_assoc]
    rw [run_ldPostRows_iff (hr1 rfl) _ ivG_ge (ldPostFile_ivG s A s.vregs),
      run_ldPostRows_iff (XReads.vregs _ hr2) _ msgG_ge
        (by rw [ldPostFile_vregs]; exact ldPostFile_msgG s B _),
      readable_range s A 4 ivG (fun _ => rfl)]
    simp only [loadDword?_vregs, readable_range s B 8 msgG (fun _ => rfl), Readable,
      forall_const, and_assoc]
    rfl
  | true =>
    simp only [loadRows, ↓reduceIte, List.nil_append, msgLoadRows_eq]
    rw [run_ldPostRows_iff hr2 _ msgG_ge (ldPostFile_msgG s B s.vregs),
      readable_range s B 8 msgG (fun _ => rfl)]
    simp only [Readable, Bool.true_eq_false, false_implies, true_and]
    rfl

/-- The loads keep the registers outside the pool. -/
theorem loadF_out (b : Bool) (s : SailJoltState) (A B : BitVec 64) (r : VReg)
    (hr : ¬ InPool b r) : loadF b s A B r = s.vregs r := by
  have h1 := poolSize_ge b
  unfold InPool at hr
  rw [loadF, msgFile_out _ _ _ _ (by omega)]
  cases b with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [poolSize_false] at hr
    exact ivFile_out _ _ _ _ (by omega)

/-- After the loads, window register `j` holds block word `j mod 16`. -/
theorem loadF_mReg (b : Bool) (s : SailJoltState) (A B : BitVec 64) (j : Nat) :
    lo (loadF b s A B) (mReg j) = (input b s A B).block[j % 16]'(Nat.mod_lt _ (by decide)) := by
  simp only [lo, loadF, msgFile_mReg, input, Vector.getElem_ofFn]

/-- The initial hash value as immediates. -/
private theorem w32_ivImm (c : Nat) (hc : c < 8) : w32 (ivImm c) = initial.get c := by
  interval_cases c <;> rfl

/-- Working variable `c` before round 0 is the old state word `c`. -/
theorem cur_zero (b : Bool) (c : Nat) (hc : c < 8) : cur b 0 c = ivVal b c := by
  unfold cur
  split
  · congr 1
    omega
  · exact absurd (show 0 < 4 ∧ 0 ≤ c % 4 from ⟨by decide, Nat.zero_le _⟩) ‹_›

/-- After round 63, working variable `c` is in `vr(48 + c)`. -/
theorem cur_sixtyFour (b : Bool) (c : Nat) (hc : c < 8) : cur b 64 c = .reg (vr (48 + c)) := by
  unfold cur
  split
  · exact absurd ‹64 < 4 ∧ _›.1 (by decide)
  simp only [sReg]
  rw [show (c + 8 - 64 % 8) % 8 = c by omega]

/-- After the loads, the old state words are where round 0 reads them. -/
theorem loadF_cur (b : Bool) (s : SailJoltState) (A B : BitVec 64) (c : Nat) (hc : c < 8) :
    (cur b 0 c).eval (lo (loadF b s A B)) = (input b s A B).state.get c := by
  rw [cur_zero b c hc]
  cases b with
  | true =>
    simp only [ivVal, ↓reduceIte, Val.eval, input]
    exact w32_ivImm c hc
  | false =>
    simp only [ivVal, Bool.false_eq_true, ↓reduceIte, Val.eval, input, lo, loadF]
    rw [msgFile_out _ _ _ _ (by rw [ivReg_toNat]; omega), ivFile_ivReg _ _ _ c hc,
      stateOf_get _ c hc]

/-! ## Final -/

/-- The final rows of the first `n` working variables. -/
private def finalRowsN (b : Bool) (n : Nat) : List Instr :=
  (List.range n).flatMap fun c => (add (.reg (vr (48 + c))) (ivVal b c) (vr (48 + c))).1

private theorem ivVal_avoids (b : Bool) (c n : Nat) (hc : c < 8) (hn : n ≤ 8) :
    (ivVal b c).Avoids (fun r => 48 ≤ r.toNat ∧ r.toNat < 48 + n) := by
  intro r hr
  unfold ivVal at hr
  split at hr
  · cases hr
  · cases hr
    show ¬ (48 ≤ (ivReg c).toNat ∧ _)
    rw [ivReg_toNat]
    omega

private theorem finalRowsN_spec (b : Bool) (n : Nat) (hn : n ≤ 8) (L : VReg → BitVec 32) :
    ∃ L', Runs (finalRowsN b n) L L' (fun r => 48 ≤ r.toNat ∧ r.toNat < 48 + n) ∧
      ∀ c < n, L' (vr (48 + c)) = L (vr (48 + c)) + (ivVal b c).eval L := by
  induction n with
  | zero => exact ⟨L, Runs.nil L _, fun c hc => absurd hc (by omega)⟩
  | succ n ih =>
    obtain ⟨L₁, h₁, v₁⟩ := ih (by omega)
    obtain ⟨L₂, h₂, v₂, -⟩ := add_spec (.reg (vr (48 + n))) (ivVal b n) (vr (48 + n))
      (by rw [vr_toNat _ (by omega)]; omega) L₁
    rw [add_reg_left] at v₂
    refine ⟨L₂, ?_, fun c hc => ?_⟩
    · have := h₁.append h₂
      rw [finalRowsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      refine this.mono fun r hr => ?_
      rcases hr with hr | rfl
      · omega
      · rw [vr_toNat _ (by omega)]; omega
    · have hav := h₁.eval (ivVal_avoids b n n (by omega) (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · rw [h₂.frame _ (vr_ne (by omega) (by omega) (by omega)), v₁ c hc]
      · change L₂ (vr (48 + c)) = L₁ (vr (48 + c)) + (ivVal b c).eval L₁ at v₂
        rw [v₂, hav, h₁.frame _ (by rw [vr_toNat _ (by omega)]; omega)]

/-- **The final rows** add the old state word `c` into `vr(48 + c)` and write only
`vr48..55`. -/
theorem finalRows_spec (b : Bool) (L : VReg → BitVec 32) :
    ∃ L', Runs (finalRows b) L L' (fun r => 48 ≤ r.toNat ∧ r.toNat < 56) ∧
      ∀ c < 8, L' (vr (48 + c)) = L (vr (48 + c)) + (ivVal b c).eval L :=
  finalRowsN_spec b 8 le_rfl L

/-! ## Rounds and final on full registers -/

/-- The compression adds the old state to the state after 64 rounds. -/
theorem compression_get (input : Vector Word 16) (init : State) (c : Nat) (hc : c < 8) :
    (compression input init).get c = (rounds input init 64).get c + init.get c := by
  rw [BitVec.add_comm]
  interval_cases c <;> rfl

/-- The registers that the rounds and the final rows write. -/
private theorem roundsW_pool (b : Bool) (r : VReg) (h : roundsW b r ∨ (48 ≤ r.toNat ∧ r.toNat < 56)) :
    InPool b r := by
  have := tBase_ge b
  unfold InPool
  cases b <;>
    simp only [roundsW, temps, tBase_false, tBase_true, poolSize, Bool.false_eq_true,
      ↓reduceIte] at h ⊢ <;> omega

/-- **The register rows.** From the loaded register file, the 64 rounds and the final rows run;
the low word of `vr(48 + c)` is then word `c` of `Spec.compression` of the loaded block and
state, and every register outside the pool keeps its value. -/
theorem regs_spec (b : Bool) (s : SailJoltState) (A B : BitVec 64) :
    ∃ F, regRun (allRounds b 64 ++ finalRows b) (loadF b s A B) = some F ∧
      (∀ c < 8, (F (vr (48 + c))).setWidth 32 =
        (compression (input b s A B).block (input b s A B).state).get c) ∧
      ∀ r, ¬ InPool b r → F r = s.vregs r := by
  set x := input b s A B
  obtain ⟨L₁, h₁, hc₁, -⟩ := rounds_spec b x.block x.state (lo (loadF b s A B))
    (loadF_cur b s A B) (loadF_mReg b s A B) 64
  obtain ⟨L₂, h₂, hc₂⟩ := finalRows_spec b L₁
  obtain ⟨F, hF, hlo, hfr⟩ := (h₁.append h₂).lift
  refine ⟨F, hF, fun c hc => ?_, fun r hr => ?_⟩
  · have e : (F (vr (48 + c))).setWidth 32 = L₂ (vr (48 + c)) := by rw [← hlo]; rfl
    have hv := hc₁ c hc
    rw [cur_sixtyFour b c hc, roundsR_eq] at hv
    have hiv : (ivVal b c).eval L₁ = x.state.get c := by
      rw [h₁.eval (fun r hr hw => ?_), ← cur_zero b c hc, loadF_cur b s A B c hc]
      unfold ivVal at hr
      have := tBase_ge b
      split at hr
      · cases hr
      · cases hr
        rename_i hb
        simp only [Bool.not_eq_true] at hb
        subst hb
        simp only [roundsW, temps, tBase_false, ivReg_toNat] at hw
        omega
    rw [e, hc₂ c hc, hiv, compression_get _ _ c hc, ← hv]
    rfl
  · rw [hfr r (fun h => hr (roundsW_pool b r h)), loadF_out b s A B r hr]

/-! ## Stores -/

/-- The packing rows of doubleword `i` and the register they store. -/
def stG (i : Nat) : List Instr × VReg :=
  ([.VirtualZeroExtendWord (.vreg (vr (48 + 2 * i))) (.vreg (vr (48 + 2 * i))) 0,
    .VirtualMULI (.vreg (vr (49 + 2 * i))) (.vreg (vr (49 + 2 * i))) 0x100000000,
    .OR (.vreg (vr (48 + 2 * i))) (.vreg (vr (49 + 2 * i))) (.vreg (vr (48 + 2 * i)))],
   vr (48 + 2 * i))

/-- The store rows are `sdPreRows` of `stG`. -/
theorem storeRows_eq (rs1 : regidx) : storeRows rs1 = sdPreRows rs1 0 ((List.range 4).map stG) :=
  rfl

/-- What the packing rows of doubleword `i` do to the register file. -/
def storeStep (i : Nat) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  let f₁ := setV f (vr (48 + 2 * i)) (jolt_virtual_zero_extend_word_value (f (vr (48 + 2 * i))))
  let f₂ := setV f₁ (vr (49 + 2 * i)) (jolt_virtual_muli_value (f₁ (vr (49 + 2 * i))) 0x100000000)
  setV f₂ (vr (48 + 2 * i)) (Riscv.ori (f₂ (vr (49 + 2 * i))) (f₂ (vr (48 + 2 * i))))

/-- The packing rows of doubleword `i` evaluate to `storeStep i`. -/
theorem regRun_stG (i : Nat) (hi : i < 4) (f : VReg → BitVec 64) :
    regRun (stG i).1 f = some (storeStep i f) := by
  simp only [stG]
  rw [regRun_cons_of (i := .VirtualZeroExtendWord (.vreg (vr (48 + 2 * i)))
      (.vreg (vr (48 + 2 * i))) 0) rfl (by rw [vr_toNat _ (by omega)]; omega),
    regRun_cons_of (i := .VirtualMULI (.vreg (vr (49 + 2 * i))) (.vreg (vr (49 + 2 * i)))
      0x100000000) rfl (by rw [vr_toNat _ (by omega)]; omega),
    regRun_cons_of (i := .OR (.vreg (vr (48 + 2 * i))) (.vreg (vr (49 + 2 * i)))
      (.vreg (vr (48 + 2 * i)))) rfl (by rw [vr_toNat _ (by omega)]; omega)]
  rfl

/-- The packing rows of doubleword `i` write only `vr(48 + 2i)` and `vr(49 + 2i)`. -/
private theorem storeStep_out (k : Nat) (hk : k < 4) (f : VReg → BitVec 64) (r : VReg)
    (h : r.toNat ≠ 48 + 2 * k) (h' : r.toNat ≠ 49 + 2 * k) : storeStep k f r = f r := by
  have e1 : r ≠ vr (48 + 2 * k) := fun e => h (by rw [e, vr_toNat _ (by omega)])
  have e2 : r ≠ vr (49 + 2 * k) := fun e => h' (by rw [e, vr_toNat _ (by omega)])
  simp only [storeStep, setV, e1, e2, ↓reduceIte]

/-- The packing rows of doubleword `i` put word `2i + 1` above word `2i`. -/
private theorem storeStep_val (i : Nat) (hi : i < 4) (f : VReg → BitVec 64) :
    storeStep i f (vr (48 + 2 * i)) =
      (f (vr (49 + 2 * i))).setWidth 32 ++ (f (vr (48 + 2 * i))).setWidth 32 := by
  have hne : vr (49 + 2 * i) ≠ vr (48 + 2 * i) := vr_ne (by omega) (by omega) (by omega)
  simp only [storeStep, setV_same, setV, hne, hne.symm, ↓reduceIte, pack_eq]

/-- The register file after the packing rows. -/
def storeFile (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  (List.range 4).foldl (fun f i => storeStep i f) f

/-- The doublewords that the rows store: word `2i + 1` of the result above word `2i`. -/
def rowsOut (x : Input) : Vector (BitVec 64) 4 :=
  let o := compression x.block x.state
  Vector.ofFn fun i => o.get (2 * i.val + 1) ++ o.get (2 * i.val)

/-- The store block evaluates to `storeFile` and stores the packed words of `F`. -/
theorem sdPreFile_stG (F : VReg → BitVec 64) :
    sdPreFile ((List.range 4).map stG) F =
      some (storeFile F, (List.range 4).map fun i =>
        (F (vr (49 + 2 * i))).setWidth 32 ++ (F (vr (48 + 2 * i))).setWidth 32) := by
  rw [sdPreFile_range 4 stG storeStep regRun_stG F]
  simp only [Option.some.injEq, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [stG]
  rw [storeStep_val i hi, foldl_range_frame _ i F _ (fun k hk g => storeStep_out k (by omega) g _
      (by rw [vr_toNat _ (by omega)]; omega) (by rw [vr_toNat _ (by omega)]; omega)),
    foldl_range_frame _ i F _ (fun k hk g => storeStep_out k (by omega) g _
      (by rw [vr_toNat _ (by omega)]; omega) (by rw [vr_toNat _ (by omega)]; omega))]

/-- The packing rows keep the registers outside `vr48..55`. -/
theorem storeFile_out (F : VReg → BitVec 64) (r : VReg) (hr : r.toNat < 48 ∨ 56 ≤ r.toNat) :
    storeFile F r = F r :=
  foldl_range_frame _ 4 F r fun k hk g => storeStep_out k hk g r (by omega) (by omega)

/-- If `vr(48 + c)` holds word `c` of the result in its low half, the stored doublewords are
`rowsOut`. -/
theorem stored_eq (x : Input) (F : VReg → BitVec 64)
    (hF : ∀ c < 8, (F (vr (48 + c))).setWidth 32 = (compression x.block x.state).get c) :
    ((List.range 4).map fun i =>
      (F (vr (49 + 2 * i))).setWidth 32 ++ (F (vr (48 + 2 * i))).setWidth 32) =
        (rowsOut x).toList := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, rowsOut, Vector.getElem_toList,
      Vector.getElem_ofFn]
    rw [show 49 + 2 * k = 48 + (2 * k + 1) by omega, hF _ (by omega), hF _ (by omega)]

/-! ## Resets -/

/-- The register file `f` with the pool registers reset to zero.
Example: `poolReset false f vr80 = 0` and `poolReset true f vr80 = f vr80`. -/
def poolReset (b : Bool) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  fun r => if InPool b r then 0 else f r

/-- The reset rows evaluate to `poolReset`. -/
theorem regRun_resetRows (b : Bool) (G : VReg → BitVec 64) :
    regRun (resetRows b) G = some (poolReset b G) := by
  have := poolSize_le b
  rw [resetRows, regRun_resets _ (fun k hk => by simp only [List.mem_range] at hk; omega)]
  congr 1
  funext r
  have := r.isLt
  simp only [poolReset, InPool, List.mem_range]
  congr 1
  apply propext
  omega

/-- Register files that agree outside the pool agree after `poolReset`. -/
theorem poolReset_congr {b : Bool} {f g : VReg → BitVec 64} (h : ∀ r, ¬ InPool b r → f r = g r) :
    poolReset b f = poolReset b g := by
  funext r
  simp only [poolReset]
  split
  · rfl
  · exact h r ‹_›

end JoltISA.Inlines.Sha256
