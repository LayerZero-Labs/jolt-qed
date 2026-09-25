import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Sail operation descriptor for RV64 `MUL`. -/
def sailMulOp : mul_op where
  result_part := VectorHalf.Low
  signed_rs1 := Signedness.Signed
  signed_rs2 := Signedness.Signed

/-- Main native `MUL` equivalence statement. -/
def mulInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd
      (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2)))).run js) =
    ((execute_MUL rs2 rs1 rd sailMulOp).run js.sail)

private abbrev sail_value (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  mult_to_bits_half (l := LeanRV64D.Functions.xlen)
    sailMulOp.signed_rs1 sailMulOp.signed_rs2
    rs1_val rs2_val sailMulOp.result_part

private abbrev jolt_value (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val * rs2_val

private abbrev op (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  jolt_value rs1_val rs2_val

theorem mul_sail_retire_after_write
    (rd : regidx)
    (x y : BitVec 64)
    (s s' : SailState)
    (hwrite : wX_bits rd (op x y) s = .ok () s') :
    ((wX_bits rd
        (mult_to_bits_half (l := LeanRV64D.Functions.xlen)
          sailMulOp.signed_rs1 sailMulOp.signed_rs2
          x y sailMulOp.result_part) >>=
      fun _ => (pure RETIRE_SUCCESS : SailM ExecutionResult)) s) =
      ((pure RETIRE_SUCCESS : SailM ExecutionResult) s') := by
  have h_value : sail_value x y = op x y := by
    unfold sail_value op jolt_value sailMulOp
    exact sail_mul_value_eq_jolt_mul_value x y
  have hwrite_sail : wX_bits rd (sail_value x y) s = .ok () s' := by
    rw [h_value]
    exact hwrite
  unfold sail_value at hwrite_sail
  simp only [bind, EStateM.bind, hwrite_sail, pure, EStateM.pure]

theorem mulInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    mulInstrEqSailStatement rs2 rs1 rd js h := by
  unfold mulInstrEqSailStatement
  -- Select Rust's no-op for x0; its full state agrees with a discarded write.
  rw [NativeDispatch.pureWriteback_run_eq rd _ js (by
    intro hx0
    have hrd := JoltISA.eq_regidx_zero_of_isX0_eq_true hx0
    subst rd
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      h.rs1_read, h.rs2_read, wX_bits_regidx_zero])]
  -- RHS
  simp only [execute_MUL, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]
  obtain ⟨s', h_write_sail⟩ := wX_shape rd (sail_value h.rs1_val h.rs2_val) js.sail
  have h_write : wX_bits rd (op h.rs1_val h.rs2_val) js.sail = .ok () s' := by
    have h_value : sail_value h.rs1_val h.rs2_val = op h.rs1_val h.rs2_val := by
      unfold sail_value op jolt_value sailMulOp
      exact sail_mul_value_eq_jolt_mul_value h.rs1_val h.rs2_val
    rw [← h_value]
    exact h_write_sail
  have h_sail_retire :=
    mul_sail_retire_after_write rd h.rs1_val h.rs2_val js.sail s' h_write

  -- LHS
  simp only [JoltISA.execInstr, JoltISA.mulWide_low, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h.rs2_read, h_write]
  exact (Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write).trans h_sail_retire.symm

end Natives

end
