import JoltBytecode.JoltISA.Core
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ANDN` equivalence statement. -/
def andnInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd
      (.ANDN (.xreg rd) (.xreg rs1) (.xreg rs2)))).run js) =
    ((execute_ZBB_RTYPE rs2 rs1 rd brop_zbb.ANDN).run js.sail)


private abbrev op (rs1_val rs2_val : BitVec 64): BitVec 64 :=
  rs1_val &&& Complement.complement rs2_val 


theorem andnInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    andnInstrEqSailStatement rs2 rs1 rd js h := by
  unfold andnInstrEqSailStatement
  -- Select Rust's no-op for x0; its full state agrees with a discarded write.
  rw [NativeDispatch.pureWriteback_run_eq rd _ js (by
    intro hx0
    have hrd := JoltISA.eq_regidx_zero_of_isX0_eq_true hx0
    subst rd
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      h.rs1_read, h.rs2_read, wX_bits_regidx_zero])]
  -- parsing the RHS of the main theorem statement 
  simp only [execute_ZBB_RTYPE] -- Tell the giant match block we are doing ANDN
  simp only [EStateM.run_bind] -- Go from do notation to nested matches
  simp only [EStateM.run]
  simp only [h.rs1_read, h.rs2_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail
  simp only [h_write]
  -- Jolt executes the same two reads and architectural write.
  simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h.rs2_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write


end Natives

end
