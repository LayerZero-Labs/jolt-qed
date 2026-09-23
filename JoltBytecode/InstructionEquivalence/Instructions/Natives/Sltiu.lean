import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `SLTIU` equivalence statement. -/
def sltiuInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.Encoded.SLTIU (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_ITYPE imm rs1 rd iop.SLTIU).run js.sail)

private abbrev op (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u rs1_val (sign_extend (m := 64) imm)))

theorem sltiuInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    sltiuInstrEqSailStatement imm rs1 rd js h := by
  unfold sltiuInstrEqSailStatement
  simp only [execute_ITYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val imm) js.sail
  simp only [pure, EStateM.pure, h_write]
  simp only [JoltISA.execInstr, jolt_sltu_value, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val imm)
    h.linkedCSRs h_write

end Natives

end
