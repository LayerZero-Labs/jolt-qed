import JoltBytecode.JoltISA.Core
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `SUBW` equivalence statement. -/
def subwInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd
      (.SUBW (.xreg rd) (.xreg rs1) (.xreg rs2)))).run js) =
    ((execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail)

private abbrev op (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  jolt_subw_value rs1_val rs2_val

/-- Native `SUBW` agrees with Sail `execute_RTYPEW ... SUBW`. -/
theorem subwInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    subwInstrEqSailStatement rs2 rs1 rd js h := by
  unfold subwInstrEqSailStatement
  -- Select Rust's no-op for x0; its full state agrees with a discarded write.
  rw [NativeDispatch.pureWriteback_run_eq rd _ js (by
    intro hx0
    have hrd := JoltISA.eq_regidx_zero_of_isX0_eq_true hx0
    subst rd
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      h.rs1_read, h.rs2_read, wX_bits_regidx_zero])]
  -- Sail side
  simp only [execute_RTYPEW, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read]
  simp only [pure, EStateM.pure]
  simp only [h.rs2_read]
  rw [sail_subw_value_eq_jolt_subw_value]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail
  simp only [h_write]
  -- Jolt side
  simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h.rs2_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write

end Natives

end
