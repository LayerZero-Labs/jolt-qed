import JoltBytecode.JoltISA.Core
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ADDIW` equivalence statement. -/
def addiwInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd
      (JoltISA.Encoded.ADDIW (.xreg rd) (.xreg rs1) imm))).run js) =
    ((execute_ADDIW imm rs1 rd).run js.sail)

private abbrev op (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  jolt_addiw_value rs1_val imm

/-- Native `ADDIW` agrees with Sail `execute_ADDIW`. -/
theorem addiwInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    addiwInstrEqSailStatement imm rs1 rd js h := by
  unfold addiwInstrEqSailStatement
  -- Select Rust's no-op for x0; its full state agrees with a discarded write.
  rw [NativeDispatch.pureWriteback_run_eq rd _ js (by
    intro hx0
    have hrd := JoltISA.eq_regidx_zero_of_isX0_eq_true hx0
    subst rd
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      h.rs1_read, wX_bits_regidx_zero])]
  -- Sail side
  simp only [execute_ADDIW, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read]
  simp only [pure, EStateM.pure]
  rw [sail_addiw_value_eq_jolt_addiw_value]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val imm) js.sail
  simp only [h_write]
  -- Jolt side
  simp only [JoltISA.execInstr, jolt_addiw_value64_encoded, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h_write]
  simp only [pure, EStateM.pure]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val imm) h.linkedCSRs h_write

end Natives

end
