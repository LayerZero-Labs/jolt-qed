import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Add
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives
/-- Main native `ADD` equivalence statement. -/
def addInstrEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.ADD).run js.sail)

private abbrev op (rs1_val rs2_val : BitVec 64): BitVec 64 :=
  rs1_val + rs2_val 


/-- Native `ADD` agrees with Sail `execute_RTYPE ... ADD`. -/
theorem addInstr_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    addInstrEqSailStatement rs2 rs1 rd js h := by
  unfold addInstrEqSailStatement
  -- RHS 
  simp only [execute_RTYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]  
  -- wX_shape is a helper theorem i wrote that write succeeds and there exists state 
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail
  simp only [h_write]  -- WE have RHS retires successfully.
 
 -- LHS 
  simp only [JoltISA.execInstr, JoltISA.addWide_low, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h.rs2_read, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
   (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write

end Natives

end
