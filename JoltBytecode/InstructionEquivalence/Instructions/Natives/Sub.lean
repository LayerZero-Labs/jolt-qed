import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Sub

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Factoring: `execute_RTYPE rs2 rs1 rd rop.SUB` reads `rs1`, reads `rs2`,
writes their difference to `rd`, and returns `RETIRE_SUCCESS`. -/
theorem execute_RTYPE_SUB_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SUB = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (v1 - v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- Native `SUB` never writes the persistent CSR virtual registers materialized
by `systemProject`. -/
theorem subInstr_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun :
      (JoltISA.execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.InstrWritesNoProtectedVReg
        (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2)) := by
    simp only [JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]
  have hprotected :=
    JoltISA.execInstr_preserves_protected
      (instr := .SUB (.xreg rd) (.xreg rs1) (.xreg rs2))
      (js := js) (js' := js') (result := result) hsafe hrun
  exact ⟨
    hprotected JoltISA.trapHandlerVReg rfl,
    hprotected JoltISA.mscratchVReg rfl,
    hprotected JoltISA.mepcVReg rfl,
    hprotected JoltISA.mcauseVReg rfl,
    hprotected JoltISA.mtvalVReg rfl,
    hprotected JoltISA.mstatusVReg rfl⟩

/-- Main native `SUB` equivalence statement. -/
def subInstrEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.SUB).run js.sail)

private abbrev op (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val - rs2_val

/-- Native `SUB` agrees with Sail `execute_RTYPE ... SUB`. -/
theorem subInstr_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    subInstrEqSailStatement rs2 rs1 rd js h := by
  unfold subInstrEqSailStatement
  simp only [execute_RTYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail
  simp only [h_write]
  simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h.rs2_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write

end Natives

end
