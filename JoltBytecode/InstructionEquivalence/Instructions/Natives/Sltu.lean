import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.SLTU

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `SLTU` equivalence statement. -/
def sltuInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.SLTU).run js.sail)

private abbrev op (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  jolt_sltu_value rs1_val rs2_val

theorem sltuInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    sltuInstrEqSailStatement rs2 rs1 rd js h := by
  unfold sltuInstrEqSailStatement 
  simp only [execute_RTYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail 
  have h_write_sail :
      wX_bits rd
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u h.rs1_val h.rs2_val)))
          js.sail = .ok () s' := by
    simpa only [op, jolt_sltu_value] using h_write
  simp only [h_write_sail]
  simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h.rs2_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write

end Natives

end
