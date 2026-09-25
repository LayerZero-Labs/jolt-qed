import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Blt

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `BLTU` equivalence statement. -/
def bltuInstrEqSailStatement
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.BLTU (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_BTYPE imm rs2 rs1 bop.BLTU).run js.sail)

theorem bltuInstr_eq_sail
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    bltuInstrEqSailStatement imm rs2 rs1 js h := by
 unfold bltuInstrEqSailStatement
 -- RHS
 simp only [execute_BTYPE]
 simp only [EStateM.run, bind, EStateM.bind]
 simp only [h.rs1_read, h.rs2_read]
 simp only [pure, EStateM.pure]
 -- LHS
 simp only [JoltISA.execInstr, JoltISA.branchDecisionPure,
   bind, EStateM.bind, pure,
   JoltISA.readSrc_xreg_run_of_read rs1 js h.rs1_val h.rs1_read,
   JoltISA.readSrc_xreg_run_of_read rs2 js h.rs2_val h.rs2_read]
 cases h_taken : zopz0zI_u h.rs1_val h.rs2_val
 · -- not taken
   simp only [Bool.false_eq_true, if_false]
   exact Projection.systemProjectResult_pure_retire js h.linkedCSRs
 · -- taken
   simp only [if_true]
   simpa only [Projection.liftSail_bind] using
     (Projection.systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
       h.linkedCSRs
       (branchJump_preservesSystemProjectRegs imm js))

end Natives

end
