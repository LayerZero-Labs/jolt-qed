import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# `VirtualPext` instruction and value lemmas

The Rust implementation scans a 64-bit mask and packs selected source bits
toward bit zero. The induction lemmas below functionalise that scan once. Load
proofs use only the resulting contiguous-window theorem; they never mention
the recursion fuel.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

private theorem mod_two_mul (x m : Nat) :
    x % (2 * m) = x % 2 + 2 * (x / 2 % m) := by
  have hdiv := Nat.mod_mul_right_div_self x 2 m
  have hmod := Nat.mod_mod_of_dvd x (show 2 ∣ 2 * m from ⟨m, rfl⟩)
  have hsplit := Nat.div_add_mod' (x % (2 * m)) 2
  rw [hdiv, hmod] at hsplit
  omega

private theorem pext_low_mask (width x : Nat) :
    jolt_pext_nat width x (2 ^ width - 1) = x % 2 ^ width := by
  induction width generalizing x with
  | zero =>
      simp only [jolt_pext_nat, pow_zero, Nat.mod_one]
  | succ width ih =>
      have hodd : (2 ^ (width + 1) - 1) % 2 = 1 := by
        rw [pow_succ]
        have hpos : 0 < 2 ^ width := by positivity
        omega
      have hdiv : (2 ^ (width + 1) - 1) / 2 = 2 ^ width - 1 := by
        rw [pow_succ]
        omega
      rw [jolt_pext_nat, if_pos hodd, hdiv, ih]
      rw [pow_succ, mul_comm (2 ^ width) 2, mod_two_mul]

private theorem pext_contiguous (offset width x : Nat) :
    jolt_pext_nat (offset + width) x ((2 ^ width - 1) * 2 ^ offset) =
      (x / 2 ^ offset) % 2 ^ width := by
  induction offset generalizing x with
  | zero =>
      simpa only [zero_add, pow_zero, mul_one, Nat.div_one] using
        pext_low_mask width x
  | succ offset ih =>
      have hmask : (2 ^ width - 1) * 2 ^ (offset + 1) =
          2 * ((2 ^ width - 1) * 2 ^ offset) := by
        rw [pow_succ]
        ring
      rw [show (offset + 1) + width = (offset + width) + 1 by omega]
      rw [hmask, jolt_pext_nat]
      have heven : 2 * ((2 ^ width - 1) * 2 ^ offset) % 2 = 0 := by omega
      rw [heven, if_neg (by decide : (0 : Nat) ≠ 1),
        show 2 * ((2 ^ width - 1) * 2 ^ offset) / 2 =
          (2 ^ width - 1) * 2 ^ offset by omega, ih]
      rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm (2 ^ offset) 2]

private theorem pext_zero_mask (fuel x : Nat) :
    jolt_pext_nat fuel x 0 = 0 := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
      rw [jolt_pext_nat, if_neg (by decide : (0 : Nat) ≠ 1), Nat.zero_div, ih]

private theorem pext_extend_fuel (fuel extra x mask : Nat)
    (hmask : mask < 2 ^ fuel) :
    jolt_pext_nat (fuel + extra) x mask = jolt_pext_nat fuel x mask := by
  induction fuel generalizing x mask with
  | zero =>
      have hzero : mask = 0 := by
        simpa only [pow_zero, Nat.lt_one_iff] using hmask
      subst hzero
      rw [pext_zero_mask, pext_zero_mask]
  | succ fuel ih =>
      have hdiv : mask / 2 < 2 ^ fuel := by
        rw [pow_succ] at hmask
        have hpos : 0 < 2 ^ fuel := by positivity
        omega
      rw [show (fuel + 1) + extra = (fuel + extra) + 1 by omega]
      rw [jolt_pext_nat, jolt_pext_nat]
      by_cases hbit : mask % 2 = 1
      · rw [if_pos hbit, if_pos hbit,
          ih (x := x / 2) (mask := mask / 2) hdiv]
      · rw [if_neg hbit, if_neg hbit,
          ih (x := x / 2) (mask := mask / 2) hdiv]

/-- `VirtualPext` with a contiguous `width`-bit mask at `offset` is exactly a
right shift followed by truncation and zero extension. -/
theorem pext_value_contiguous (x : BitVec 64) (offset width : Nat)
    (hfit : offset + width ≤ 64) :
    jolt_virtual_pext_value x
        (BitVec.ofNat 64 ((2 ^ width - 1) * 2 ^ offset)) =
      zero_extend (m := 64) ((x >>> offset).setWidth width) := by
  apply BitVec.eq_of_toNat_eq
  unfold jolt_virtual_pext_value zero_extend Sail.BitVec.zeroExtend BitVec.zeroExtend
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  have hmask_lt : (2 ^ width - 1) * 2 ^ offset < 2 ^ (offset + width) := by
    rw [Nat.pow_add]
    have hoffset_pos : 0 < 2 ^ offset := by positivity
    have hwidth_pos : 0 < 2 ^ width := by positivity
    have hwidth : 2 ^ width - 1 < 2 ^ width := by omega
    nlinarith
  have hmask64 : (2 ^ width - 1) * 2 ^ offset < 2 ^ 64 :=
    lt_of_lt_of_le hmask_lt (Nat.pow_le_pow_right (by omega) hfit)
  rw [Nat.mod_eq_of_lt hmask64]
  have hfuel := pext_extend_fuel (offset + width) (64 - (offset + width))
    x.toNat ((2 ^ width - 1) * 2 ^ offset) hmask_lt
  rw [show (offset + width) + (64 - (offset + width)) = 64 by omega] at hfuel
  rw [hfuel, pext_contiguous, Nat.shiftRight_eq_div_pow]

private theorem popcount_zero_mask (fuel : Nat) :
    jolt_popcount_nat fuel 0 = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [jolt_popcount_nat, Nat.zero_mod, Nat.zero_div, ih, zero_add]

private theorem popcount_low_mask (width : Nat) :
    jolt_popcount_nat width (2 ^ width - 1) = width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      have hodd : (2 ^ (width + 1) - 1) % 2 = 1 := by
        rw [pow_succ]
        have hpos : 0 < 2 ^ width := by positivity
        omega
      have hdiv : (2 ^ (width + 1) - 1) / 2 = 2 ^ width - 1 := by
        rw [pow_succ]
        omega
      rw [jolt_popcount_nat, hodd, hdiv, ih]
      omega

private theorem popcount_contiguous (offset width : Nat) :
    jolt_popcount_nat (offset + width) ((2 ^ width - 1) * 2 ^ offset) = width := by
  induction offset with
  | zero =>
      simpa only [zero_add, pow_zero, mul_one] using popcount_low_mask width
  | succ offset ih =>
      have hmask : (2 ^ width - 1) * 2 ^ (offset + 1) =
          2 * ((2 ^ width - 1) * 2 ^ offset) := by
        rw [pow_succ]
        ring
      rw [show (offset + 1) + width = (offset + width) + 1 by omega]
      rw [hmask, jolt_popcount_nat]
      have heven : 2 * ((2 ^ width - 1) * 2 ^ offset) % 2 = 0 := by omega
      rw [heven, show 2 * ((2 ^ width - 1) * 2 ^ offset) / 2 =
        (2 ^ width - 1) * 2 ^ offset by omega, ih]
      omega

private theorem popcount_extend_fuel (fuel extra mask : Nat)
    (hmask : mask < 2 ^ fuel) :
    jolt_popcount_nat (fuel + extra) mask = jolt_popcount_nat fuel mask := by
  induction fuel generalizing mask with
  | zero =>
      have hzero : mask = 0 := by
        simpa only [pow_zero, Nat.lt_one_iff] using hmask
      subst hzero
      rw [popcount_zero_mask, popcount_zero_mask]
  | succ fuel ih =>
      have hdiv : mask / 2 < 2 ^ fuel := by
        rw [pow_succ] at hmask
        have hpos : 0 < 2 ^ fuel := by positivity
        omega
      rw [show (fuel + 1) + extra = (fuel + extra) + 1 by omega]
      rw [jolt_popcount_nat, jolt_popcount_nat,
        ih (mask := mask / 2) hdiv]

private theorem popcount_value_contiguous (offset width : Nat)
    (hfit : offset + width ≤ 64) :
    jolt_popcount_nat 64
        (BitVec.ofNat 64 ((2 ^ width - 1) * 2 ^ offset)).toNat = width := by
  have hmask_lt : (2 ^ width - 1) * 2 ^ offset < 2 ^ (offset + width) := by
    rw [Nat.pow_add]
    have hoffset_pos : 0 < 2 ^ offset := by positivity
    have hwidth_pos : 0 < 2 ^ width := by positivity
    have hwidth : 2 ^ width - 1 < 2 ^ width := by omega
    nlinarith
  have hmask64 : (2 ^ width - 1) * 2 ^ offset < 2 ^ 64 :=
    lt_of_lt_of_le hmask_lt (Nat.pow_le_pow_right (by omega) hfit)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmask64]
  have hfuel := popcount_extend_fuel (offset + width) (64 - (offset + width))
    ((2 ^ width - 1) * 2 ^ offset) hmask_lt
  rw [show (offset + width) + (64 - (offset + width)) = 64 by omega] at hfuel
  rw [hfuel, popcount_contiguous]

private theorem sign_extend_eq_pext_extension {width : Nat} (lane : BitVec width)
    (hwidth : 0 < width) (hwidth64 : width ≤ 64) :
    (if (zero_extend (m := 64) lane).getLsbD (width - 1) then
        zero_extend (m := 64) lane |||
          ~~~(BitVec.ofNat 64 (2 ^ width - 1))
      else
        zero_extend (m := 64) lane) =
      sign_extend (m := 64) lane := by
  have hlast : width - 1 < width := by omega
  have hlast64 : width - 1 < 64 := lt_of_lt_of_le hlast hwidth64
  have hlast64b : (width - 1 <b 64) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hlast64
  have hlast_value :
      (zero_extend (m := 64) lane).getLsbD (width - 1) =
        lane.getLsbD (width - 1) := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.getLsbD_setWidth,
      hlast64b, Bool.true_and]
  have hwidthb : (0 <b width) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hwidth
  have hmsb : lane.msb = lane.getLsbD (width - 1) := by
    unfold BitVec.msb BitVec.getMsbD
    simp only [hwidthb, Bool.true_and, Nat.sub_zero]
  rw [hlast_value]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : (i <b 64) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
  unfold sign_extend Sail.BitVec.signExtend
  rw [BitVec.getLsbD_signExtend]
  simp only [hi64, Bool.true_and, hmsb]
  by_cases hiwidth : i < width
  · rw [if_pos hiwidth]
    have hiwidthb : (i <b width) = true := by
      simpa only [Nat.blt_eq, decide_eq_true_eq] using hiwidth
    have himask : (BitVec.ofNat 64 (2 ^ width - 1)).getLsbD i = true := by
      simp only [BitVec.getLsbD_ofNat, hi64, Bool.true_and,
        Nat.testBit_two_pow_sub_one, hiwidthb]
    have hiext : (zero_extend (m := 64) lane).getLsbD i = lane.getLsbD i := by
      simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.getLsbD_setWidth,
        hi64, Bool.true_and]
    by_cases hsign : lane.getLsbD (width - 1) = true
    · rw [if_pos hsign, BitVec.getLsbD_or, hiext, BitVec.getLsbD_not,
        hi64, Bool.true_and, himask]
      simp only [Bool.not_true, Bool.or_false]
    · rw [if_neg hsign, hiext]
  · rw [if_neg hiwidth]
    have hiwidthb : (i <b width) = false := by
      simpa only [Nat.blt_eq, decide_eq_false_iff_not] using hiwidth
    have himask : (BitVec.ofNat 64 (2 ^ width - 1)).getLsbD i = false := by
      simp only [BitVec.getLsbD_ofNat, hi64, Bool.true_and,
        Nat.testBit_two_pow_sub_one, hiwidthb]
    have hiext : (zero_extend (m := 64) lane).getLsbD i = false := by
      simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.getLsbD_setWidth,
        hi64, Bool.true_and]
      unfold BitVec.getLsbD
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le lane.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    by_cases hsign : lane.getLsbD (width - 1) = true
    · rw [if_pos hsign, BitVec.getLsbD_or, hiext, BitVec.getLsbD_not,
        hi64, Bool.true_and, himask, hsign]
      simp only [Bool.not_false, Bool.false_or]
    · have hsign_false : lane.getLsbD (width - 1) = false :=
        Bool.eq_false_of_not_eq_true hsign
      rw [if_neg hsign, hiext, hsign_false]

/-- `VirtualPextSigned` with a contiguous nonempty mask extracts the selected
window and sign-extends it to 64 bits. -/
theorem pext_signed_value_contiguous (x : BitVec 64) (offset width : Nat)
    (hwidth : 0 < width) (hfit : offset + width ≤ 64) :
    jolt_virtual_pext_signed_value x
        (BitVec.ofNat 64 ((2 ^ width - 1) * 2 ^ offset)) =
      sign_extend (m := 64) ((x >>> offset).setWidth width) := by
  unfold jolt_virtual_pext_signed_value
  rw [popcount_value_contiguous offset width hfit]
  rw [if_neg (Nat.ne_of_gt hwidth)]
  rw [pext_value_contiguous x offset width hfit]
  exact sign_extend_eq_pext_extension ((x >>> offset).setWidth width)
    hwidth (by omega)

/-- Unsigned `VirtualPext` with virtual sources and destination. -/
theorem virtual_pext_run_vreg_vreg_vreg (vd value mask : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualPext (.vreg vd) (.vreg value) (.vreg mask))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then jolt_virtual_pext_value (js.vregs value) (js.vregs mask)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_pext_value (js.vregs value) (js.vregs mask)) js hvd

/-- Signed `VirtualPext` with virtual sources and destination. -/
theorem virtual_pext_signed_run_vreg_vreg_vreg (vd value mask : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualPextSigned (.vreg vd) (.vreg value) (.vreg mask))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then jolt_virtual_pext_signed_value (js.vregs value) (js.vregs mask)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_pext_signed_value (js.vregs value) (js.vregs mask)) js hvd

/-- Unsigned `VirtualPext` from virtual sources to an architectural destination. -/
theorem virtual_pext_run_xreg_vreg_vreg (rd : regidx) (value mask : VReg)
    (js : SailJoltState) (s' : SailState)
    (hwrite : wX_bits rd (jolt_virtual_pext_value (js.vregs value) (js.vregs mask))
      js.sail = .ok () s') :
    (execInstr (.VirtualPext (.xreg rd) (.vreg value) (.vreg mask))).run js =
      .ok RETIRE_SUCCESS { js with sail := s' } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hwrite, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- Signed `VirtualPext` from virtual sources to an architectural destination. -/
theorem virtual_pext_signed_run_xreg_vreg_vreg (rd : regidx) (value mask : VReg)
    (js : SailJoltState) (s' : SailState)
    (hwrite : wX_bits rd
      (jolt_virtual_pext_signed_value (js.vregs value) (js.vregs mask))
      js.sail = .ok () s') :
    (execInstr (.VirtualPextSigned (.xreg rd) (.vreg value) (.vreg mask))).run js =
      .ok RETIRE_SUCCESS { js with sail := s' } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hwrite, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

end JoltISA

end
