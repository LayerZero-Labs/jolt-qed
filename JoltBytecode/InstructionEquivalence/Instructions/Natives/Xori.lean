import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `XORI` equivalence statement. -/
def xoriInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd
      (JoltISA.Encoded.XORI (.xreg rd) (.xreg rs1) imm))).run js) =
    ((execute_ITYPE imm rs1 rd iop.XORI).run js.sail)

private abbrev op (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  rs1_val ^^^ sign_extend (m := 64) imm

theorem xoriInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    xoriInstrEqSailStatement imm rs1 rd js h := by
  unfold xoriInstrEqSailStatement
  -- Select Rust's no-op for x0; its full state agrees with a discarded write.
  rw [NativeDispatch.pureWriteback_run_eq rd _ js (by
    intro hx0
    have hrd := JoltISA.eq_regidx_zero_of_isX0_eq_true hx0
    subst rd
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      h.rs1_read, wX_bits_regidx_zero])]
  simp only [execute_ITYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val imm) js.sail
  simp only [pure, EStateM.pure, h_write]
  simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val imm)
    h.linkedCSRs h_write

end Natives

end
