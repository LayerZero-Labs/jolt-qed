import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import Mathlib

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULH: Rust inline sequence = Sail MULH

This file is deliberately organized as a small proof-engineering template for
M-extension instructions that do not use advice.

The theorem we ultimately care about is program-level:

```
System.systemProjectResult
  ((JoltISA.execProgram (JoltISA.mulhProgramAuto rd rs1 rs2)).run js)
  =
(execute_MUL rs2 rs1 rd mulhOp).run js.sail
```

That statement uses the program produced directly by the Rust-to-Lean
extractor.  The proof explains why this program is equivalent to Sail; it does
not hide behind a second handwritten monadic implementation.

The proof has three conceptual layers:

1. `JoltISA.mulhProgramAuto` is the literal Rust inline sequence.
2. `mulhProgramAuto_concrete` executes that program one instruction at a time and
   shows the value written to `rd`.
3. `mulh_correction_eq_mulhs` is the arithmetic lemma connecting that Jolt
   value to the Sail/RISC-V signed-high multiply value `mulhs`.

The Rust inline sequence, with the allocator choices fixed to virtual registers
`0`, `1`, and `2`, is:

```
VirtualMovsign v_sx, rs1
VirtualMovsign v_sy, rs2
MUL            v_sx, v_sx, rs2
MUL            v_sy, v_sy, rs1
MULHU          v_tmp, rs1, rs2
ADD            v_tmp, v_tmp, v_sx
ADD            rd,    v_tmp, v_sy
```
-/

def mulhOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Signed }

/-- The pure value written by the Rust `MULH` inline sequence. -/
def jolt_mulh_value (x y : BitVec 64) : BitVec 64 :=
  jolt_mulhu_value x y + jolt_movsign_value x * y + jolt_movsign_value y * x

/-- Extracting bits 127 down to 64 from a 128-bit truncated integer is the same
as dividing that integer by `2^64` and keeping the low 64 bits. -/
private theorem extract_high64_to_bits_truncate_eq_ofInt_div (p : Int) :
    (Sail.BitVec.extractLsb (to_bits_truncate (l := 128) p) 127 64 : BitVec 64) =
      BitVec.ofInt 64 (p / 2^64) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', to_bits_truncate,
        Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
  omega
/-- The local `mulhs` value agrees with Sail's generic signed/signed high-half
multiply operator. -/
private theorem mulhs_eq_sail_mulh_value (v1 v2 : BitVec 64) :
    mulhs v1 v2 =
      mult_to_bits_half (l := LeanRV64D.Functions.xlen)
        Signedness.Signed Signedness.Signed v1 v2 VectorHalf.High := by
  unfold mulhs mult_to_bits_half LeanRV64D.Functions.xlen
  simp only
  change BitVec.ofInt 64 (v1.toInt * v2.toInt / 2^64) =
    BitVec.setWidth 64
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) (v1.toInt * v2.toInt)) 127 64)
  rw [extract_high64_to_bits_truncate_eq_ofInt_div]
  simp
/-- A 64-bit word below `2^63` has signed interpretation equal to its unsigned
natural-number value. -/
private theorem toInt_of_toNat_lt_half (x : BitVec 64)
    (h : x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt]
  have hcond : 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
/-- A 64-bit word at least `2^63` has signed interpretation equal to its
unsigned value minus `2^64`. -/
private theorem toInt_of_half_le (x : BitVec 64)
    (h : ¬ x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) - (18446744073709551616 : Int) := by
  rw [BitVec.toInt]
  have hcond : ¬ 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
  norm_num
/-- Arithmetic correction for the case where `rs1` is negative and `rs2` is
nonnegative. -/
private theorem mulh_corr_neg_pos_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 =
      ((((a : Int) - 18446744073709551616) * (b : Int) /
            18446744073709551616) % 18446744073709551616).toNat := by
  rw [show ((a : Int) - 18446744073709551616) * (b : Int) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (b : Int) by
    rw [Nat.cast_mul]
    ring]
  omega
/-- Arithmetic correction for the case where `rs1` is nonnegative and `rs2` is
negative. -/
private theorem mulh_corr_pos_neg_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * a) %
        18446744073709551616 =
      (((a : Int) * ((b : Int) - 18446744073709551616) /
            18446744073709551616) % 18446744073709551616).toNat := by
  rw [show (a : Int) * ((b : Int) - 18446744073709551616) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (a : Int) by
    rw [Nat.cast_mul]
    ring]
  omega
/-- Arithmetic correction for the case where both operands are negative. -/
private theorem mulh_corr_neg_neg_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * b +
        18446744073709551615 * a) % 18446744073709551616 =
      ((((a : Int) - 18446744073709551616) *
          ((b : Int) - 18446744073709551616) / 18446744073709551616) %
        18446744073709551616).toNat := by
  rw [show ((a : Int) - 18446744073709551616) *
        ((b : Int) - 18446744073709551616) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (b : Int) -
        18446744073709551616 * (a : Int) +
          18446744073709551616 * 18446744073709551616 by
    rw [Nat.cast_mul]
    ring]
  omega
/-- The unsigned-high product plus the two sign corrections computed by Jolt is
exactly the signed-high product required by RV64 `MULH`. -/
private theorem mulh_correction_eq_mulhs (x y : BitVec 64) :
    jolt_mulh_value x y = mulhs x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · by_cases hy : y.toNat < 9223372036854775808
    · rw [jolt_mulh_value, jolt_movsign_value_eq_zero_of_toNat_lt_half x hx,
          jolt_movsign_value_eq_zero_of_toNat_lt_half y hy]
      unfold jolt_mulhu_value JoltISA.mulWide mulhs
      rw [toInt_of_toNat_lt_half x hx, toInt_of_toNat_lt_half y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      omega
    · rw [jolt_mulh_value, jolt_movsign_value_eq_zero_of_toNat_lt_half x hx,
          jolt_movsign_value_eq_neg_one_of_half_le y hy]
      unfold jolt_mulhu_value JoltISA.mulWide mulhs
      rw [toInt_of_toNat_lt_half x hx, toInt_of_half_le y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_pos_neg_arith x.toNat y.toNat
  · by_cases hy : y.toNat < 9223372036854775808
    · rw [jolt_mulh_value, jolt_movsign_value_eq_neg_one_of_half_le x hx,
          jolt_movsign_value_eq_zero_of_toNat_lt_half y hy]
      unfold jolt_mulhu_value JoltISA.mulWide mulhs
      rw [toInt_of_half_le x hx, toInt_of_toNat_lt_half y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_neg_pos_arith x.toNat y.toNat
    · rw [jolt_mulh_value, jolt_movsign_value_eq_neg_one_of_half_le x hx,
          jolt_movsign_value_eq_neg_one_of_half_le y hy]
      unfold jolt_mulhu_value JoltISA.mulWide mulhs
      rw [toInt_of_half_le x hx, toInt_of_half_le y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_neg_neg_arith x.toNat y.toNat
/-- Factor Sail's generated `execute_MUL` body for `MULH` into the simple shape
used by the generic R-type equivalence bridge. -/
theorem execute_MULH_factored (rs2 rs1 rd : regidx) :
    execute_MUL rs2 rs1 rd mulhOp = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (mulhs v1 v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_MUL, mulhOp, mulhs_eq_sail_mulh_value, bind_pure_comp]

private theorem inlineTmp0_ne_inlineTmp1 :
    JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp1 := by decide

private theorem inlineTmp1_ne_inlineTmp0 :
    JoltISA.inlineTmp1 ≠ JoltISA.inlineTmp0 := by decide

private theorem inlineTmp0_ne_inlineTmp2 :
    JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp2 := by decide

private theorem inlineTmp1_ne_inlineTmp2 :
    JoltISA.inlineTmp1 ≠ JoltISA.inlineTmp2 := by decide

/-- Program-level concrete theorem for `MULH`.

The instruction blocks prove the emitted Jolt sequence writes
`jolt_mulh_value`.  The final value block is the only place where the pure
arithmetic theorem changes that Jolt value into Sail's `MULH` value. -/
theorem mulhProgramAuto_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (jsf : SailJoltState),
      (JoltISA.execProgram (JoltISA.mulhProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (mulhs v1 v2) := by

  -- Instruction 1: `VirtualMovsign v0, rs1` writes the sign mask of `rs1`.
  let rs1SignMask := jolt_movsign_value v1
  obtain ⟨js_afterRs1SignMask, h_rs1_sign_mask_reads_rs1,
      h_rs1_sign_mask_keeps_sail, h_rs1_sign_mask_writes_rs1SignMask,
      h_rs1_sign_mask_preserves, h_rs1_sign_mask_succeeds⟩ :=
    JoltISA.exists_state_after_movsign_run_vreg_xreg
      JoltISA.inlineTmp0 rs1 js js.sail v1 rfl h_read_rs1
      (by unfold WritableVReg; decide)

  -- Instruction 2: `VirtualMovsign v1, rs2` writes the sign mask of `rs2`.
  let rs2SignMask := jolt_movsign_value v2
  obtain ⟨js_afterRs2SignMask, h_rs2_sign_mask_reads_rs2,
      h_rs2_sign_mask_keeps_sail, h_rs2_sign_mask_writes_rs2SignMask,
      h_rs2_sign_mask_preserves, h_rs2_sign_mask_succeeds⟩ :=
    JoltISA.exists_state_after_movsign_run_vreg_xreg
      JoltISA.inlineTmp1 rs2 js_afterRs1SignMask js.sail v2
      h_rs1_sign_mask_keeps_sail h_read_rs2
      (by unfold WritableVReg; decide)
  have h_rs2_sign_mask_preserves_rs1SignMask :
      js_afterRs2SignMask.vregs JoltISA.inlineTmp0 = rs1SignMask :=
    (h_rs2_sign_mask_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp1).trans
      h_rs1_sign_mask_writes_rs1SignMask

  -- Instruction 3: `MUL v0, v0, rs2` writes the `rs1` sign correction.
  let rs1CorrectionProduct := rs1SignMask * v2
  obtain ⟨js_afterRs1CorrectionMul, h_rs1_correction_mul_reads_rs2,
      h_rs1_correction_mul_keeps_sail, h_rs1_correction_mul_writes_rs1CorrectionProduct,
      h_rs1_correction_mul_preserves, h_rs1_correction_mul_succeeds⟩ :=
    JoltISA.exists_state_after_mul_run_vreg_vreg_xreg
      JoltISA.inlineTmp0 JoltISA.inlineTmp0 rs2 js_afterRs2SignMask js.sail
      rs1SignMask v2 h_rs2_sign_mask_keeps_sail
      h_rs2_sign_mask_preserves_rs1SignMask h_read_rs2
      (by unfold WritableVReg; decide)
  have h_rs1_correction_mul_preserves_rs2SignMask :
      js_afterRs1CorrectionMul.vregs JoltISA.inlineTmp1 = rs2SignMask :=
    (h_rs1_correction_mul_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp0).trans
      h_rs2_sign_mask_writes_rs2SignMask

  -- Instruction 4: `MUL v1, v1, rs1` writes the `rs2` sign correction.
  let rs2CorrectionProduct := rs2SignMask * v1
  obtain ⟨js_afterRs2CorrectionMul, h_rs2_correction_mul_reads_rs1,
      h_rs2_correction_mul_keeps_sail, h_rs2_correction_mul_writes_rs2CorrectionProduct,
      h_rs2_correction_mul_preserves, h_rs2_correction_mul_succeeds⟩ :=
    JoltISA.exists_state_after_mul_run_vreg_vreg_xreg
      JoltISA.inlineTmp1 JoltISA.inlineTmp1 rs1 js_afterRs1CorrectionMul js.sail
      rs2SignMask v1 h_rs1_correction_mul_keeps_sail
      h_rs1_correction_mul_preserves_rs2SignMask h_read_rs1
      (by unfold WritableVReg; decide)
  have h_rs2_correction_mul_preserves_rs1CorrectionProduct :
      js_afterRs2CorrectionMul.vregs JoltISA.inlineTmp0 = rs1CorrectionProduct :=
    (h_rs2_correction_mul_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp1).trans
      h_rs1_correction_mul_writes_rs1CorrectionProduct

  -- Instruction 5: `MULHU v2, rs1, rs2` writes the unsigned high product.
  let unsignedHighProduct := jolt_mulhu_value v1 v2
  obtain ⟨js_afterMulhu, h_mulhu_reads_rs1, h_mulhu_reads_rs2, h_mulhu_keeps_sail,
      h_mulhu_writes_unsignedHighProduct, h_mulhu_preserves, h_mulhu_succeeds⟩ :=
    JoltISA.exists_state_after_mulhu_run_vreg_xreg_xreg
      JoltISA.inlineTmp2 rs1 rs2 js_afterRs2CorrectionMul js.sail v1 v2
      h_rs2_correction_mul_keeps_sail h_read_rs1 h_read_rs2
      (by unfold WritableVReg; decide)
  have h_mulhu_preserves_rs1CorrectionProduct :
      js_afterMulhu.vregs JoltISA.inlineTmp0 = rs1CorrectionProduct :=
    (h_mulhu_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp2).trans
      h_rs2_correction_mul_preserves_rs1CorrectionProduct
  have h_mulhu_preserves_rs2CorrectionProduct :
      js_afterMulhu.vregs JoltISA.inlineTmp1 = rs2CorrectionProduct :=
    (h_mulhu_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp2).trans
      h_rs2_correction_mul_writes_rs2CorrectionProduct

  -- Instruction 6: `ADD v2, v2, v0` adds the `rs1` correction into the high product.
  let highProductWithRs1Correction := unsignedHighProduct + rs1CorrectionProduct
  obtain ⟨js_afterAddRs1Correction, h_add_rs1_correction_keeps_sail,
      h_add_rs1_correction_writes_highProductWithRs1Correction,
      h_add_rs1_correction_preserves, h_add_rs1_correction_succeeds⟩ :=
    JoltISA.exists_state_after_add_run_vreg_vreg_vreg
      JoltISA.inlineTmp2 JoltISA.inlineTmp2 JoltISA.inlineTmp0 js_afterMulhu
      unsignedHighProduct rs1CorrectionProduct
      (by unfold WritableVReg; decide) h_mulhu_writes_unsignedHighProduct
      h_mulhu_preserves_rs1CorrectionProduct
  have h_add_rs1_correction_preserves_rs2CorrectionProduct :
      js_afterAddRs1Correction.vregs JoltISA.inlineTmp1 = rs2CorrectionProduct :=
    (h_add_rs1_correction_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp2).trans
      h_mulhu_preserves_rs2CorrectionProduct
  have h_add_rs1_correction_sail :
      js_afterAddRs1Correction.sail = js.sail := by
    rw [h_add_rs1_correction_keeps_sail, h_mulhu_keeps_sail]

  -- Instruction 7: `ADD rd, v2, v1` writes the final Jolt `MULH` value.
  let mulhJoltResult := jolt_mulh_value v1 v2
  obtain ⟨js_afterFinalAdd, h_final_add_writes_mulhJoltResult,
      h_final_add_succeeds⟩ :=
    JoltISA.exists_state_after_add_run_xreg_vreg_vreg
      rd JoltISA.inlineTmp2 JoltISA.inlineTmp1 js_afterAddRs1Correction js.sail
      highProductWithRs1Correction rs2CorrectionProduct h_add_rs1_correction_sail
      h_add_rs1_correction_writes_highProductWithRs1Correction
      h_add_rs1_correction_preserves_rs2CorrectionProduct

  -- Full program succeeds by stepping through the seven instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.mulhProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js_afterFinalAdd := by
    unfold JoltISA.mulhProgramAuto
    rw [JoltISA.isX0_eq_false_of_ne_zero hrd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl,
      show (BitVec.ofNat 7 41 : JoltISA.VReg) = JoltISA.inlineTmp1 by rfl,
      show (BitVec.ofNat 7 42 : JoltISA.VReg) = JoltISA.inlineTmp2 by rfl]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs1SignMask
      h_rs1_sign_mask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterRs1SignMask js_afterRs2SignMask
      h_rs2_sign_mask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterRs2SignMask
      js_afterRs1CorrectionMul h_rs1_correction_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterRs1CorrectionMul
      js_afterRs2CorrectionMul h_rs2_correction_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterRs2CorrectionMul js_afterMulhu
      h_mulhu_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMulhu js_afterAddRs1Correction
      h_add_rs1_correction_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAddRs1Correction js_afterFinalAdd
      h_final_add_succeeds]
    rfl

  refine ⟨js_afterFinalAdd, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt MULH value.
  have h_final_jolt_value :
      js_afterFinalAdd.sail = stateAfterWrite js.sail rd mulhJoltResult := by
    simp only [mulhJoltResult, jolt_mulh_value]
    exact h_final_add_writes_mulhJoltResult

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's correction sequence is Sail's MULH value.
  have h_mulh_value :
      mulhJoltResult = mulhs v1 v2 := by
    simp only [mulhJoltResult]
    -- NOTE: The core math theorem.
    exact mulh_correction_eq_mulhs v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_mulh_value]
  exact h_final_jolt_value

/-- `MULH` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem mulhProgramAuto_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.mulhProgramAuto rd rs1 rs2)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.mulhProgramAuto rd rs1 rs2) := by
    unfold JoltISA.mulhProgramAuto
    split
    · simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true]
    · rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl,
        show (BitVec.ofNat 7 41 : JoltISA.VReg) = JoltISA.inlineTmp1 by rfl,
        show (BitVec.ofNat 7 42 : JoltISA.VReg) = JoltISA.inlineTmp2 by rfl]
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true]
      exact ⟨JoltISA.inlineTmp0_not_protected, JoltISA.inlineTmp1_not_protected,
        JoltISA.inlineTmp0_not_protected, JoltISA.inlineTmp1_not_protected,
        JoltISA.inlineTmp2_not_protected, JoltISA.inlineTmp2_not_protected⟩
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level theorem: interpreting the Jolt ISA `MULH` expansion has
the same projected architectural result as Sail's `MULH` semantics. -/
def mulhProgramEqSailStatement (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.mulhProgramAuto rd rs1 rs2)).run js) =
    (execute_MUL rs2 rs1 rd mulhOp).run js.sail

/-- Main program-level theorem: interpreting the Jolt ISA `MULH` expansion has
the same projected architectural result as Sail's `MULH` semantics. -/
theorem mulhProgram_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    mulhProgramEqSailStatement rs2 rs1 rd js h := by
  unfold mulhProgramEqSailStatement
  let v1 := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  let v2 := h.rs2_val
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.mulhProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    have hzero := JoltISA.pureWritebackRdZeroProgram_run js
    unfold JoltISA.pureWritebackRdZeroProgram at hzero
    rw [hzero]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_MULH_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterFinalAdd, h_program_succeeds, h_final_sail⟩ :=
    mulhProgramAuto_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterFinalAdd :=
    mulhProgramAuto_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_MULH_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (mulhs v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterFinalAdd rd (mulhs v1 v2) h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (mulhs v1 v2) js.sail s' h_write).symm

end
