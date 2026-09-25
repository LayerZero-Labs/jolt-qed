import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Factoring: `execute_ITYPE imm rs1 rd iop.ADDI` reads `rs1`, writes the
sign-extended immediate sum to `rd`, and returns `RETIRE_SUCCESS`. -/
theorem execute_ITYPE_ADDI_factored
    (imm : BitVec 12)
    (rs1 rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ADDI = (do
      let v1 ← rX_bits rs1
      wX_bits rd (v1 + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := by
  simp only [execute_ITYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- RHS as final state: running native Sail `ADDI` reads `rs1 = v1`, then leaves
the Sail state as `s` with `rd` overwritten by `v1 + sign_extend imm`. -/
theorem execute_ITYPE_ADDI_run
    (imm : BitVec 12) (rs1 rd : regidx) (s : SailState) (v1 : BitVec 64)
    (h_read : rX_bits rs1 s = .ok v1 s) :
    (execute_ITYPE imm rs1 rd iop.ADDI).run s =
      .ok RETIRE_SUCCESS (stateAfterWrite s rd (v1 + sign_extend (m := 64) imm)) := by
  rw [execute_ITYPE_ADDI_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (v1 + sign_extend (m := 64) imm) s
  rw [h_write]
  rw [wX_bits_eq_stateAfterWrite rd (v1 + sign_extend (m := 64) imm) s s' h_write]

/-- Native `ADDI` never writes the persistent CSR virtual registers materialized
by `systemProject`, so projection commutes with the architectural write. -/
theorem addiInstr_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.InstrWritesNoProtectedVReg
        (.ADDI (.xreg rd) (.xreg rs1) imm) := by
    simp only [JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]
  have hprotected :=
    JoltISA.execInstr_preserves_protected
      (instr := .ADDI (.xreg rd) (.xreg rs1) imm)
      (js := js) (js' := js') (result := result) hsafe hrun
  exact ⟨
    hprotected JoltISA.trapHandlerVReg rfl,
    hprotected JoltISA.mscratchVReg rfl,
    hprotected JoltISA.mepcVReg rfl,
    hprotected JoltISA.mcauseVReg rfl,
    hprotected JoltISA.mtvalVReg rfl,
    hprotected JoltISA.mstatusVReg rfl⟩

/-- Main native `ADDI` equivalence statement. -/
def addiInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_ITYPE imm rs1 rd iop.ADDI).run js.sail)

private abbrev op (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  rs1_val + sign_extend (m := 64) imm

theorem addiInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    addiInstrEqSailStatement imm rs1 rd js h := by
  unfold addiInstrEqSailStatement
  simp only [execute_ITYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val imm) js.sail
  simp only [pure, EStateM.pure, h_write]
  simp only [JoltISA.execInstr, JoltISA.addWide_low, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val imm)
    h.linkedCSRs h_write



end Natives

end
