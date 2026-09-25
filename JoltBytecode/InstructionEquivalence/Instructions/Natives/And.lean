import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `AND` equivalence statement. -/
def andInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd
      (.AND (.xreg rd) (.xreg rs1) (.xreg rs2)))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.AND).run js.sail)

private abbrev op (rs1_val rs2_val : BitVec 64): BitVec 64 :=
  rs1_val &&& rs2_val 

theorem andInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    andInstrEqSailStatement rs2 rs1 rd js h := by
  unfold andInstrEqSailStatement
  -- Select Rust's no-op for x0; its full state agrees with a discarded write.
  rw [NativeDispatch.pureWriteback_run_eq rd _ js (by
    intro hx0
    have hrd := JoltISA.eq_regidx_zero_of_isX0_eq_true hx0
    subst rd
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      h.rs1_read, h.rs2_read, wX_bits_regidx_zero])]
  -- RHS 
  simp only [execute_RTYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]  
  -- wX_shape is a helper theorem i wrote that write succeeds and there exists state 
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail
  simp only [h_write]  -- WE have RHS retires successfully.

  -- LHS
  simp only [JoltISA.execInstr, Riscv.andi, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h.rs2_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (h.rs1_val &&& h.rs2_val)
    h.linkedCSRs h_write


end Natives

end
